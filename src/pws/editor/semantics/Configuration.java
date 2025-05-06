package pws.editor.semantics;

import smalgebra.BasicStateProposition;
import smalgebra.SMProposition;
import smalgebra.TrueProposition;

import java.io.Serializable;
import java.util.*;

public class Configuration implements Serializable {
    private String assemblyId;
    private List<BasicStateProposition> propositions;

    public Configuration(String assemblyId) {
        this.assemblyId = assemblyId;
        this.propositions = new ArrayList<>();
    }

    public String getAssemblyId() {
        return assemblyId;
    }

    /**
     * Aggiunge una BasicStateProposition mantenendo l'ordine (ordinamento lessicografico in base all'id).
     */
    public void addBasicStateProposition(BasicStateProposition bsp) {
        // Inserimento ordinato in base a bsp.getId()
        int index = 0;
        while (index < propositions.size() && propositions.get(index).getMachineId().compareTo(bsp.getMachineId()) < 0) {
            index++;
        }
        propositions.add(index, bsp);
    }

    public List<BasicStateProposition> getBasicStatePropositions() {
        return Collections.unmodifiableList(propositions);
    }

    /**
     * Costruisce una Configuration a partire da una lista di BasicStateProposition.
     * Le proposizioni vengono inserite in ordine.
     */
    public static Configuration fromBasicStatePropositions(String assemblyId, List<BasicStateProposition> props) {
        Configuration config = new Configuration(assemblyId);
        for (BasicStateProposition bsp : props) {
            config.addBasicStateProposition(bsp);
        }
        return config;
    }

    public Configuration intersect(Configuration other) {
        if (!this.assemblyId.equals(other.getAssemblyId())) {
            throw new IllegalArgumentException("Assemblies do not match.");
        }
        // Merge constraints from both configurations
        Map<String, BasicStateProposition> resultMap = new HashMap<>();
        // Add all propositions from this configuration
        for (BasicStateProposition bsp : this.getBasicStatePropositions()) {
            resultMap.put(bsp.getMachineId(), bsp);
        }
        // For each proposition in the other configuration, merge constraints
        for (BasicStateProposition bsp : other.getBasicStatePropositions()) {
            String machineId = bsp.getMachineId();
            if (resultMap.containsKey(machineId)) {
                BasicStateProposition existing = resultMap.get(machineId);
                if (!existing.equals(bsp)) {
                    // Conflict: different constraints for the same machine, intersection is undefined.
                    return null;
                }
            } else {
                resultMap.put(machineId, bsp);
            }
        }
        List<BasicStateProposition> resultList = new ArrayList<>(resultMap.values());
        return Configuration.fromBasicStatePropositions(this.assemblyId, resultList);
    }

    public boolean implies(Configuration other) {
        if (!this.assemblyId.equals(other.getAssemblyId())) {
            throw new IllegalArgumentException("Assemblies do not match.");
        }
        // Per ogni vincolo presente in 'other', verifico che anche 'this' lo contenga con lo stesso valore.
        for (BasicStateProposition bspOther : other.getBasicStatePropositions()) {
            boolean found = false;
            for (BasicStateProposition bspThis : this.getBasicStatePropositions()) {
                if (bspThis.getMachineId().equals(bspOther.getMachineId())) {
                    found = true;
                    if (!bspThis.equals(bspOther)) {
                        return false;
                    }
                }
            }
            // Se 'other' specifica un vincolo per un machineID che 'this' non specifica,
            // allora 'this' non implica 'other'.
            if (!found) {
                return false;
            }
        }
        return true;
    }

    /**
     * Determines whether this configuration implies at least one configuration in the provided Semantics.
     * That is, it returns true if there exists at least one configuration in s such that
     * this configuration implies that configuration.
     *
     * @param s The Semantics object to check against.
     * @return true if this configuration implies at least one configuration in s; false otherwise.
     */
    public boolean implies(Semantics s) {
        for (Configuration conf : s.getConfigurations()) {
            if (this.implies(conf)) {
                return true;
            }
        }
        return false;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof Configuration)) return false;
        Configuration that = (Configuration) o;
        return Objects.equals(assemblyId, that.assemblyId) &&
                Objects.equals(propositions, that.propositions);
    }

    @Override
    public int hashCode() {
        return Objects.hash(assemblyId, propositions);
    }

//    @Override
//    public String toString() {
//        StringJoiner joiner = new StringJoiner(", ");
//        for (BasicStateProposition bsp : propositions) {
//            joiner.add(bsp.toString());
//        }
//        return "Configuration{" +
//                "assemblyId='" + assemblyId + "', propositions=[" + joiner.toString() + "]" +
//                "}";
//    }

    @Override
    public String toString() {
        StringJoiner joiner = new StringJoiner(",");
        for (BasicStateProposition bsp : propositions) {
            joiner.add(bsp.toString());
        }
        return "(" + joiner.toString() + ")";
    }

    public SMProposition toSMProposition() {
        // Start with the identity element for AND: TrueProposition.
        SMProposition conj = new TrueProposition();
        for (BasicStateProposition bsp : propositions) {
            // Assuming that andBSP returns a new SMProposition representing the conjunction.
            conj = conj.andBSP(bsp);
        }
        return conj;
    }

    /**
     * Converts this Configuration into a Semantics object consisting solely of itself.
     *
     * @return A Semantics object containing only this Configuration.
     */
    public Semantics toSemantics() {
        Semantics sem = new Semantics(this.assemblyId);
        sem.addConfiguration(this);
        return sem;
    }

    // HELPER METHODS

    /**
     * Returns true if this configuration contains a constraint for the given machineId.
     *
     * @param machineId The identifier of the machine.
     * @return true if a BasicStateProposition for machineId is present; false otherwise.
     */
    public boolean contains(String machineId) {
        for (BasicStateProposition bsp : propositions) {
            if (bsp.getMachineId().equals(machineId)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Returns the state name for the given machineId in this configuration.
     * If no constraint exists for the machine, returns null.
     *
     * @param machineId The identifier of the machine.
     * @return The state name, or null if not present.
     */
    public String getStateName(String machineId) {
        for (BasicStateProposition bsp : propositions) {
            if (bsp.getMachineId().equals(machineId)) {
                return bsp.getStateName();
            }
        }
        return null;
    }

    /**
     * Returns a new Configuration that is identical to this one except that the constraint
     * for the given machineId is replaced with newState. If no constraint exists for machineId,
     * then the new configuration will have that constraint added.
     *
     * @param machineId The identifier of the machine.
     * @param newState  The new state name for that machine.
     * @return A new Configuration with the updated constraint.
     */
    public Configuration replaceConstraint(String machineId, String newState) {
        List<BasicStateProposition> newProps = new ArrayList<>();
        boolean replaced = false;
        for (BasicStateProposition bsp : propositions) {
            if (bsp.getMachineId().equals(machineId)) {
                newProps.add(new BasicStateProposition(machineId, newState));
                replaced = true;
            } else {
                newProps.add(bsp);
            }
        }
        if (!replaced) {
            newProps.add(new BasicStateProposition(machineId, newState));
        }
        return Configuration.fromBasicStatePropositions(this.assemblyId, newProps);
    }
}