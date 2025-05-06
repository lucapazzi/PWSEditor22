package pws.editor.semantics;

import assembly.Assembly;
import machinery.StateInterface;
import machinery.StateMachine;
import machinery.Transition;
import machinery.TransitionInterface;
import smalgebra.BasicStateProposition;
import smalgebra.FalseProposition;
import smalgebra.OrProposition;
import smalgebra.SMProposition;

import java.io.Serializable;
import java.util.*;

import static assembly.AssemblyGenerator.evaluateSMPropositionOverAllFeasibleAssemblies;
import java.util.Objects;


public class Semantics implements Serializable {
    private String assemblyId;
    private Set<Configuration> configurations;

    public Semantics(String assemblyId) {
        this.assemblyId = assemblyId;
        this.configurations = new HashSet<>();
    }

    public String getAssemblyId() {
        return assemblyId;
    }

    public Set<Configuration> getConfigurations() {
        return configurations;
    }

    /**
     * Adds a Configuration, verifying that it belongs to the same assembly.
     * On one hand, if the new configuration is more specific than at least one existing configuration,
     * it will not be inserted.
     * On the other hand, if the new configuration is less specific than some existing configurations,
     * then those more specific configurations will be removed.
     */
    public Semantics addConfiguration(Configuration config) {
        if (!config.getAssemblyId().equals(this.assemblyId)) {
            throw new IllegalArgumentException("The configuration belongs to a different assembly.");
        }
        // Create a copy of the current configurations to iterate safely.
        Set<Configuration> toCheck = new HashSet<>(configurations);
        for (Configuration existing : toCheck) {
            if (config.implies(existing)) {
                // New configuration is more specific than an existing configuration.
                // Therefore, do not add the new configuration.
                return this;
            }
            if (existing.implies(config)) {
                // Existing configuration is more specific than the new one.
                // Remove the more specific configuration.
                configurations.remove(existing);
            }
        }
        configurations.add(config);
        return this;
    }

    /**
     * Determines whether this Semantics implies the other Semantics.
     * In other words, for every configuration in this Semantics,
     * there exists at least one configuration in the other Semantics
     * that is implied by it.
     *
     * @param other The Semantics to compare against.
     * @return true if every configuration in this Semantics implies at least one configuration in the other Semantics; false otherwise.
     * @throws IllegalArgumentException if the two Semantics belong to different assemblies.
     */
    /**
     * Determines whether this Semantics implies the other Semantics.
     * In other words, every configuration in this Semantics must imply the other Semantics.
     *
     * @param other The Semantics to compare against.
     * @return true if every configuration in this Semantics implies the other Semantics; false otherwise.
     * @throws IllegalArgumentException if the two Semantics belong to different assemblies.
     */
    public boolean implies(Semantics other) {
        if (!this.assemblyId.equals(other.getAssemblyId())) {
            throw new IllegalArgumentException("Both Semantics must belong to the same assembly.");
        }
        for (Configuration config : this.configurations) {
            if (!config.implies(other)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Simplifies this Semantics by checking, for each state machine m in the given Assembly and each state S of m,
     * whether the semantics consisting solely of the configuration for m.S implies this Semantics.
     * If so, that configuration is added to this Semantics.
     *
     * @param assembly The Assembly instance from which to derive the state machines and states.
     * @return The simplified Semantics (this instance, after potential modifications).
     */
    public Semantics simplify(Assembly assembly) {
        if (!this.assemblyId.equals(assembly.getAssemblyId())) {
            throw new IllegalArgumentException("Assembly ID mismatch.");
        }
        // For each state machine in the assembly
        for (String machineId : assembly.getStateMachines().keySet()) {
            StateMachine machine = assembly.getStateMachines().get(machineId);
            // For each state in the machine
            for (StateInterface state : machine.getStates()) {
                // Create a configuration representing only this state's constraint: m.S
                Configuration conf = new BasicStateProposition(machineId, state.getName()).toConf(assembly);
                // Create a temporary Semantics containing just that configuration
                // Semantics tempSem = conf.toSemantics();
                // If { m.S } implies this Semantics, add the configuration m.S to this Semantics.
                if (conf.implies(this)) {
                    this.addConfiguration(conf);
                }
            }
        }
        return this;
    }

    // Other operations (union, intersection, etc.) would go here

    /**
     * Converts this Semantics into its symbolic representation (an SMProposition).
     * For instance, you might take the disjunction (OR) of the SMProposition representations
     * of each configuration.
     */
    public SMProposition toSMProposition() {
        // If no configurations are present, return the identity element for OR (FalseProposition)
        if (configurations.isEmpty()) {
            return new FalseProposition();
        }
        // Alternatively, you can start with a FalseProposition and OR every configuration’s SMProposition.
        SMProposition disj = new FalseProposition();
        for (Configuration config : configurations) {
            disj = new OrProposition(disj, config.toSMProposition());
        }
        return disj;
    }

    public Semantics intersection(Semantics other) {
        if (!this.assemblyId.equals(other.getAssemblyId())) {
            throw new IllegalArgumentException("Both Semantics must belong to the same assembly.");
        }
        Set<Configuration> intersectionSet = new HashSet<>();
        // Compute pairwise intersections without using addConfiguration
        for (Configuration config1 : this.configurations) {
            for (Configuration config2 : other.configurations) {
                Configuration intersectConfig = config1.intersect(config2);
                if (intersectConfig != null) {
                    intersectionSet.add(intersectConfig);
                }
            }
        }
        // Create a new Semantics object and assign the computed intersections directly.
        Semantics result = new Semantics(this.assemblyId);
        result.configurations.addAll(intersectionSet);
        return result;
    }

    /**
     * Computes the union of this Semantics with another Semantics.
     * It merges the configurations from both Semantics, ensuring that redundant configurations
     * (ones implied by another) are not included in the result.
     */
    public Semantics union(Semantics other) {
        if (!this.assemblyId.equals(other.getAssemblyId())) {
            throw new IllegalArgumentException("Both Semantics must belong to the same assembly.");
        }
        Semantics result = new Semantics(this.assemblyId);
        // Merge configurations from both semantics.
        Set<Configuration> unionSet = new HashSet<>();
        unionSet.addAll(this.configurations);
        unionSet.addAll(other.configurations);

        // Remove redundant configurations: if a configuration is implied by another, remove it.
        Set<Configuration> finalSet = new HashSet<>(unionSet);
        for (Configuration c1 : unionSet) {
            for (Configuration c2 : unionSet) {
                if (c1 != c2 && c1.implies(c2)) {
                    finalSet.remove(c2);
                }
            }
        }
        // Add the filtered configurations to the result.
        for (Configuration config : finalSet) {
            result.addConfiguration(config);
        }
        return result;
    }

    /**
     * Computes the complement (logical negation) of this Semantics using a hybrid approach.
     *
     * This method converts the current Semantics into its symbolic representation (SMProposition),
     * negates it, and then evaluates the negated proposition over all the feasible concrete
     * assemblies
     *
     * @param assembly The Assembly instance used to generate all the feasible concrete assemblies
     * @return The complement of this Semantics computed relative to the provided Assembly.
     */
    public Semantics complementHybrid(Assembly assembly) {
        SMProposition originalProp = this.toSMProposition();
        SMProposition negatedProp = originalProp.negate();

        if (!this.assemblyId.equals(assembly.getAssemblyId())) {
            throw new IllegalArgumentException("The expression to be negated has to refer to the assembly against which complement is computed.");
        }
         return evaluateSMPropositionOverAllFeasibleAssemblies(assembly,negatedProp);
    }

    /**
     * Helper method to compute the cartesian product of a list of lists.
     * Each element of the result is a combination (list) that contains one element
     * from each list in the input.
     */
    private static List<List<BasicStateProposition>> cartesianProduct(List<List<BasicStateProposition>> lists) {
        List<List<BasicStateProposition>> result = new ArrayList<>();
        if (lists.isEmpty()) {
            result.add(new ArrayList<>());
            return result;
        }
        cartesianProductHelper(lists, result, 0, new ArrayList<>());
        return result;
    }

    private static void cartesianProductHelper(List<List<BasicStateProposition>> lists,
                                               List<List<BasicStateProposition>> result,
                                               int depth,
                                               List<BasicStateProposition> current) {
        if (depth == lists.size()) {
            result.add(new ArrayList<>(current));
            return;
        }
        for (BasicStateProposition element : lists.get(depth)) {
            current.add(element);
            cartesianProductHelper(lists, result, depth + 1, current);
            current.remove(current.size() - 1);
        }
    }

//    @Override
//    public String toString() {
//        StringJoiner joiner = new StringJoiner(", ");
//        for (Configuration config : configurations) {
//            joiner.add(config.toString());
//        }
//        return "Semantics{" +
//                "assemblyId='" + assemblyId + "', configurations={" + joiner.toString() + "}" +
//                "}";
//    }

    @Override
    public String toString() {
        StringJoiner joiner = new StringJoiner(", ");
        for (Configuration config : configurations) {
            joiner.add(config.toString());
        }
        return "{" + joiner.toString() + "}";
    }

    // Add the following methods in the Semantics class (for example, after the existing methods):

    /**
     * Computes the union of this Semantics with another Semantics.
     * The union is defined as the set union of configurations followed by a minimization step
     * that removes redundant configurations. If one configuration implies another, the more specific
     * configuration is removed, leaving the more general configuration.
     *
     * @param other The other Semantics to union with.
     * @return A new Semantics representing the union.
     */
    public Semantics unionTest(Semantics other) {
        if (!this.assemblyId.equals(other.getAssemblyId())) {
            throw new IllegalArgumentException("Both Semantics must belong to the same assembly.");
        }
        Set<Configuration> unionSet = new HashSet<>();
        unionSet.addAll(this.configurations);
        unionSet.addAll(other.configurations);

        // Minimize: remove the configuration that implies the other (i.e. the more specific one).
        Set<Configuration> minimized = new HashSet<>(unionSet);
        for (Configuration c1 : unionSet) {
            for (Configuration c2 : unionSet) {
                if (c1 != c2 && c1.implies(c2)) {
                    // c1 is more specific than c2, so remove c1.
                    minimized.remove(c1);
                }
            }
        }
        Semantics result = new Semantics(this.assemblyId);
        for (Configuration c : minimized) {
            result.addConfiguration(c);
        }
        return result;
    }

    /**
     * Computes the intersection of this Semantics with another Semantics.
     * The intersection is computed pairwise for every configuration from this Semantics
     * and the other Semantics, then minimized by removing redundant configurations.
     *
     * @param other The other Semantics to intersect with.
     * @return A new Semantics representing the intersection.
     */
    public Semantics intersectionTest(Semantics other) {
        if (!this.assemblyId.equals(other.getAssemblyId())) {
            throw new IllegalArgumentException("Both Semantics must belong to the same assembly.");
        }
        Set<Configuration> interSet = new HashSet<>();
        for (Configuration c1 : this.configurations) {
            for (Configuration c2 : other.configurations) {
                Configuration cInter = c1.intersect(c2);
                if (cInter != null) {
                    interSet.add(cInter);
                }
            }
        }
        // Minimize: remove redundant configurations
        Set<Configuration> minimized = new HashSet<>(interSet);
        for (Configuration c1 : interSet) {
            for (Configuration c2 : interSet) {
                if (c1 != c2 && c1.implies(c2)) {
                    minimized.remove(c2);
                }
            }
        }
        Semantics result = new Semantics(this.assemblyId);
        for (Configuration c : minimized) {
            result.addConfiguration(c);
        }
        return result;
    }

    /**
     * Computes the complement of this Semantics relative to the universe generated by the given Assembly.
     * The complement consists of those configurations in the universe that do NOT imply any configuration
     * in this Semantics.
     *
     * @param assembly The Assembly instance used to generate the universe.
     * @return A new Semantics representing the complement.
     */
    public Semantics complementTest(Assembly assembly) {
        if (!this.assemblyId.equals(assembly.getAssemblyId())) {
            throw new IllegalArgumentException("Assembly ID mismatch.");
        }
        Set<Configuration> universe = assembly.generateUniverse();
        Semantics result = new Semantics(this.assemblyId);
        for (Configuration c : universe) {
            boolean isSatisfied = false;
            // If configuration c satisfies (i.e. implies) any configuration in this Semantics,
            // then it belongs to the initial semantics and must be excluded.
            for (Configuration s : this.configurations) {
                if (c.implies(s)) {
                    isSatisfied = true;
                    break;
                }
            }
            if (!isSatisfied) {
                result.addConfiguration(c);
            }
        }
        return result;
    }

    /**
     * Determines whether this Semantics implies the other Semantics.
     * According to the theory, this Semantics implies the other if every configuration in this Semantics
     * implies at least one configuration in the other Semantics.
     *
     * @param other The Semantics to compare against.
     * @return true if for every configuration in this Semantics there exists at least one configuration in the other that is implied by it; false otherwise.
     */
    public boolean impliesTest(Semantics other) {
        if (!this.assemblyId.equals(other.getAssemblyId())) {
            throw new IllegalArgumentException("Both Semantics must belong to the same assembly.");
        }
        for (Configuration c : this.configurations) {
            boolean found = false;
            for (Configuration otherConf : other.getConfigurations()) {
                if (c.implies(otherConf)) {
                    found = true;
                    break;
                }
            }
            if (!found) return false;
        }
        return true;
    }

    /**
     * Determines whether this Semantics logically implies the other Semantics,
     * using a universal evaluation over all feasible assemblies.
     * Instead of cloning assemblies, it converts both Semantics operands to their
     * SMProposition representations, evaluates each over all feasible assemblies via
     * evaluateSMPropositionOverAllFeasibleAssemblies, and then compares the resulting Semantics.
     *
     * @param other The Semantics to compare against.
     * @param assembly The Assembly instance used to generate the universe of configurations.
     * @return true if, for every fully-specified configuration where this Semantics holds,
     *         the other Semantics also holds; false otherwise.
     * @throws IllegalArgumentException if the two Semantics belong to different assemblies.
     */
    public boolean impliesTestUniversal(Semantics other, Assembly assembly) {
        if (!this.assemblyId.equals(other.getAssemblyId())) {
            throw new IllegalArgumentException("Both Semantics must belong to the same assembly.");
        }
        // Convert both semantics to their SMProposition forms.
        SMProposition s1Prop = this.toSMProposition();
        SMProposition s2Prop = other.toSMProposition();

        // Evaluate each proposition over all feasible assemblies.
        // This method returns a Semantics representing the set of fully-specified configurations
        // in which the proposition holds.
        Semantics semS1 = evaluateSMPropositionOverAllFeasibleAssemblies(assembly, s1Prop);
        Semantics semS2 = evaluateSMPropositionOverAllFeasibleAssemblies(assembly, s2Prop);

        // Now, we consider that this Semantics implies the other if every configuration in semS1
        // implies at least one configuration in semS2.
        return semS1.impliesTest(semS2);
    }

    /**
     * Simplifies this Semantics by checking, for each state machine m in the given Assembly and each state S of m,
     * whether the semantics consisting solely of the configuration for m.S implies this Semantics.
     * If so, that configuration is added to this Semantics.
     *
     * @param assembly The Assembly instance from which to derive the state machines and states.
     * @return This Semantics instance after potential modifications.
     */
    public Semantics simplifyTest(Assembly assembly) {
        if (!this.assemblyId.equals(assembly.getAssemblyId())) {
            throw new IllegalArgumentException("Assembly ID mismatch.");
        }
        Semantics resultSemantics = this.clone();
        // For each state machine in the assembly
        for (String machineId : assembly.getStateMachines().keySet()) {
            StateMachine machine = assembly.getStateMachines().get(machineId);
            // For each state in the machine
            for (StateInterface state : machine.getStates()) {
                // Create the configuration corresponding to m.S
                Configuration conf = new BasicStateProposition(machineId, state.getName()).toConf(assembly);
                Semantics singleConf = conf.toSemantics();
                final boolean leq = singleConf.LEQ(resultSemantics, assembly);
                if (leq)  {
                    resultSemantics.addConfiguration(conf);
                }
            }
        }
        return resultSemantics;
    }

    /**
     * Transforms this Semantics by applying an action A = M.E, where M is a machine and E is an event.
     *
     * This transformation is conceptualized as a function mapping a domain to a codomain:
     *
     * 1. Domain: Identify the subset of configurations in this Semantics that are affected by the transition,
     *    i.e. those configurations that contain the constraint { M:S } where S is the source state of the transition.
     *
     * 2. Transformation: For each configuration in the domain, replace the constraint { M:S } with { M:T },
     *    where T is the target state of the transition triggered by event E.
     *
     * 3. Final Semantics: Compute the transformed semantics by removing the original domain from this Semantics
     *    and then uniting it with the codomain (the set of transformed configurations).
     *
     * If no transition matching the given event is found in machine M, or if the intersection of this Semantics
     * with the domain is empty, then no transformation is performed and the original Semantics is returned.
     *
     * @param machineId The identifier of the machine M that is involved in the action.
     * @param eventName The event E triggering the transition.
     * @param assembly  The Assembly instance from which the machine and its transitions are retrieved.
     * @return A new Semantics object reflecting the transformation:
     *         configurations originally satisfying { M:S } are replaced by configurations satisfying { M:T }.
     * @throws IllegalArgumentException if the machine or the corresponding transition is not found.
     */
    public Semantics transformByMachineEvent(String machineId, String eventName, Assembly assembly) {
        // Retrieve the state machine for the given machineId
        StateMachine machine = assembly.getStateMachines().get(machineId);
        if (machine == null) {
            throw new IllegalArgumentException("Machine " + machineId + " not found in assembly.");
        }

        // Find a transition triggered by eventName.
        Transition transition = null;
        for (TransitionInterface t : machine.getTransitions()) {
            if (t.getTriggerEvent().equals(eventName)) {
                transition = (Transition) t;
                break;
            }
        }
        if (transition == null) {
            throw new IllegalArgumentException("No transition triggered by event " + eventName + " found in machine " + machineId);
        }

        String sourceState = transition.getSource().getName();
        String targetState = transition.getTarget().getName();

        // Create a configuration representing { machineId: sourceState }
        Configuration confSource = Configuration.fromBasicStatePropositions(
                this.assemblyId,
                Arrays.asList(new BasicStateProposition(machineId, sourceState))
        );
        // Check if the current Semantics intersects  { machineId: sourceState }
        Semantics semSource = confSource.toSemantics();

        // build the domain of the transformation function
        Semantics domain = this.intersection(semSource);
        // check if the domain is not empty
        if ( domain.configurations.isEmpty() ) {
            // If it is empty, we don't perform any transformation.
            return this;
        }
        // if is not empty transform the domain in the codomain

        // Build a new codomain by transforming the domain:
        // For each configuration in the domain, substitute each basic state proposition
        // (...,machineId.sourceState,...) with (...,machineId.targetState,...)
        final Semantics codomain = domain.computeCodomain(machineId, assembly, sourceState, targetState);
        Semantics removeDomainFromThis = this.AND(semSource.NOT(assembly));
        Semantics addCodomainToThis = removeDomainFromThis.OR(codomain);

        return addCodomainToThis.clone();
    }

    public Semantics transformByMachineTransition(String machineId, Transition transition, Assembly assembly) {
        String sourceState = transition.getSource().getName();
        String targetState = transition.getTarget().getName();

        // Create a configuration representing { machineId: sourceState }
        Configuration confSource = Configuration.fromBasicStatePropositions(
                this.assemblyId,
                Arrays.asList(new BasicStateProposition(machineId, sourceState))
        );
        // Check if the current Semantics intersects  { machineId: sourceState }
        Semantics semSource = confSource.toSemantics();

        // build the domain of the transformation function
        Semantics domain = this.intersection(semSource);
        // check if the domain is not empty
        if ( domain.configurations.isEmpty() ) {
            // If it is empty, we don't perform any transformation.
            return this;
        }
        // if is not empty transform the domain in the codomain

        // Build a new codomain by transforming the domain:
        // For each configuration in the domain, substitute each basic state proposition
        // (...,machineId.sourceState,...) with (...,machineId.targetState,...)
        final Semantics codomain = domain.computeCodomain(machineId, assembly, sourceState, targetState);
        Semantics removeDomainFromThis = this.AND(semSource.NOT(assembly));
        Semantics addCodomainToThis = removeDomainFromThis.OR(codomain);

        return addCodomainToThis.clone();
    }

    public Semantics computeCodomain(String machineId, Assembly assembly, String sourceState, String targetState) {
        Semantics codomain = new Semantics(assembly.getAssemblyId());
        for (Configuration conf : this.configurations) {
            if (conf.contains(machineId) && conf.getStateName(machineId).equals(sourceState)) {
                Configuration newConf = conf.replaceConstraint(machineId, targetState);
                codomain.addConfiguration(newConf);
            }
        }
        return codomain;
    }

    @Override
    public Semantics clone() {
        Semantics cloned = new Semantics(this.assemblyId);
        for (Configuration config : this.configurations) {
            // Get the list of basic state propositions from the original configuration.
            List<BasicStateProposition> clonedProps = new ArrayList<>(config.getBasicStatePropositions());
            // Create a new Configuration with the same assemblyId and propositions.
            Configuration clonedConfig = Configuration.fromBasicStatePropositions(this.assemblyId, clonedProps);
            // Add the cloned configuration to the new Semantics.
            cloned.addConfiguration(clonedConfig);
        }
        return cloned;
    }

    // Some logic here

    public static Semantics top(String assemblyId, Assembly assembly) {
        // Return a Semantics that contains all fully-specified configurations
        Semantics sem = new Semantics(assemblyId);
        sem.getConfigurations().addAll(assembly.generateUniverse());
        return sem;
    }

    public static Semantics bottom(String assemblyId) {
        // Return a Semantics that is empty.
        return new Semantics(assemblyId);
    }

    // Add the following methods to the Semantics class (e.g., after the existing top and bottom methods):

    public static Semantics top(Assembly assembly) {
        return top(assembly.getAssemblyId(), assembly);
    }

    public static Semantics bottom(Assembly assembly) {
        return bottom(assembly.getAssemblyId());
    }

    public Semantics OR(Semantics other) {
        return this.unionTest(other);
    }

    public Semantics AND(Semantics other) {
        return this.intersectionTest(other);
    }

    public Semantics NOT(Assembly assembly) {
        return this.complementTest(assembly);
    }

    public Semantics DIFF(Semantics other, Assembly assembly) {
        Semantics notOther = other.NOT(assembly);
        Semantics diff = this.AND(notOther);
        return diff;
    }

    public boolean LEQ(Semantics other, Assembly assembly) {
        return this.impliesTestUniversal(other,assembly);
    }

    public boolean ISEMPTY() {
        return this.configurations.isEmpty();
    }

    public boolean EQ(Semantics other) {
        return this.impliesTest(other) && other.impliesTest(this);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof Semantics)) return false;
        Semantics that = (Semantics) o;
        return Objects.equals(assemblyId, that.assemblyId)
                && Objects.equals(configurations, that.configurations);
    }

    @Override
    public int hashCode() {
        return Objects.hash(assemblyId, configurations);
    }
}