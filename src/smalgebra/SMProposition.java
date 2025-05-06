package smalgebra;

import assembly.Assembly;
import assembly.AssemblyInterface;
import pws.editor.semantics.Configuration;
import pws.editor.semantics.Semantics;

import java.io.Serializable;
import java.util.Set;

public interface SMProposition extends Cloneable, Serializable {


    SMProposition clone();

    boolean evaluate(AssemblyInterface assembly);

    /**
     * Trasforma l'espressione sostituendo, per la macchina data, lo stato fromState con toState.
     * (Non viene più controllata l'ontologica validità dell'espressione.)
     */
    default SMProposition transform(String machineId, String fromState, String toState, AssemblyInterface assembly) {
        if (this instanceof BasicStateProposition) {
            BasicStateProposition bsp = (BasicStateProposition) this;
            if (bsp.getMachineId().equals(machineId) && bsp.getStateName().equals(fromState)) {
                return new BasicStateProposition(machineId, toState);
            } else {
                return bsp;
            }
        } else if (this instanceof AndProposition) {
            AndProposition ap = (AndProposition) this;
            SMProposition newLeft = ap.getLeft().transform(machineId, fromState, toState, assembly);
            SMProposition newRight = ap.getRight().transform(machineId, fromState, toState, assembly);
            return new AndProposition(newLeft, newRight);
        } else if (this instanceof OrProposition) {
            OrProposition op = (OrProposition) this;
            SMProposition newLeft = op.getLeft().transform(machineId, fromState, toState, assembly);
            SMProposition newRight = op.getRight().transform(machineId, fromState, toState, assembly);
            return new OrProposition(newLeft, newRight);
        } else if (this instanceof NotProposition) {
            NotProposition np = (NotProposition) this;
            SMProposition newProp = np.getProposition().transform(machineId, fromState, toState, assembly);
            return new NotProposition(newProp);
        } else {
            return this;
        }
    }

    /**
     * A livello ontologico, A ontoImplies B se per ogni configurazione in cui A è vera, B è vera.
     */
    default boolean ontoImplies(SMProposition other, AssemblyInterface assembly) {
        for (AssemblyInterface conf : assembly.getAllConcreteAssemblies()) {
            if (this.evaluate(conf) && !other.evaluate(conf)) {
                return false;
            }
        }
        return true;
    }

    /**
     * A livello ontologico, A ontoEquiv B se A ontoImplies B e B ontoImplies A.
     */
    default boolean ontoEquiv(SMProposition other, AssemblyInterface assembly) {
        return this.ontoImplies(other, assembly) && other.ontoImplies(this, assembly);
    }

    default SMProposition andBSP(BasicStateProposition bsp) {
        return new AndProposition(bsp, this);
    }

    default SMProposition negate() {
        return new NotProposition(this);
    }

    /**
     * A livello ontologico, A ontoEquiv B se A ontoImplies B e B ontoImplies A.
     */
    default boolean ontoEquiv(SMProposition other, Assembly assembly) {
        return this.ontoImplies(other, assembly) && other.ontoImplies(this, assembly);
    }

    /**
     * Converte l'espressione nella forma normale negativa (NNF)
     * in cui le negazioni appaiono solo direttamente davanti agli atomi.
     */
    default SMProposition toNNF() {
        if (this instanceof BasicStateProposition) {
            return this;
        } else if (this instanceof NotProposition) {
            SMProposition inner = ((NotProposition) this).getProposition();
            if (inner instanceof NotProposition) {
                // doppia negazione: ¬(¬A) = A
                return ((NotProposition) inner).getProposition().toNNF();
            } else if (inner instanceof AndProposition) {
                // ¬(A ∧ B) = ¬A ∨ ¬B
                SMProposition left = new NotProposition(((AndProposition) inner).getLeft()).toNNF();
                SMProposition right = new NotProposition(((AndProposition) inner).getRight()).toNNF();
                return new OrProposition(left, right);
            } else if (inner instanceof OrProposition) {
                // ¬(A ∨ B) = ¬A ∧ ¬B
                SMProposition left = new NotProposition(((OrProposition) inner).getLeft()).toNNF();
                SMProposition right = new NotProposition(((OrProposition) inner).getRight()).toNNF();
                return new AndProposition(left, right);
            } else {
                return new NotProposition(inner.toNNF());
            }
        } else if (this instanceof AndProposition) {
            SMProposition left = ((AndProposition) this).getLeft().toNNF();
            SMProposition right = ((AndProposition) this).getRight().toNNF();
            return new AndProposition(left, right);
        } else if (this instanceof OrProposition) {
            SMProposition left = ((OrProposition) this).getLeft().toNNF();
            SMProposition right = ((OrProposition) this).getRight().toNNF();
            return new OrProposition(left, right);
        }
        return this; // default
    }

    /**
     * Converte l'espressione in forma normale congiuntiva (CNF).
     */
    default SMProposition toCNF() {
        SMProposition nnf = this.toNNF();
        return distributeOrOverAnd(nnf);
    }

    /**
     * Converte l'espressione in forma normale disgiuntiva (DNF).
     */
    default SMProposition toDNF() {
        SMProposition nnf = this.toNNF();
        return distributeAndOverOr(nnf);
    }

    /**
     * Distribuisce l'OR sull'AND per ottenere la CNF.
     * Implementa la regola: A ∨ (B ∧ C) = (A ∨ B) ∧ (A ∨ C)
     */
    static SMProposition distributeOrOverAnd(SMProposition expr) {
        if (expr instanceof OrProposition) {
            SMProposition left = distributeOrOverAnd(((OrProposition) expr).getLeft());
            SMProposition right = distributeOrOverAnd(((OrProposition) expr).getRight());
            // Se uno dei due lati è una congiunzione, applica la distribuzione.
            if (left instanceof AndProposition) {
                SMProposition a = ((AndProposition) left).getLeft();
                SMProposition b = ((AndProposition) left).getRight();
                return new AndProposition(
                        distributeOrOverAnd(new OrProposition(a, right)),
                        distributeOrOverAnd(new OrProposition(b, right))
                );
            } else if (right instanceof AndProposition) {
                SMProposition a = ((AndProposition) right).getLeft();
                SMProposition b = ((AndProposition) right).getRight();
                return new AndProposition(
                        distributeOrOverAnd(new OrProposition(left, a)),
                        distributeOrOverAnd(new OrProposition(left, b))
                );
            } else {
                return new OrProposition(left, right);
            }
        } else if (expr instanceof AndProposition) {
            SMProposition left = distributeOrOverAnd(((AndProposition) expr).getLeft());
            SMProposition right = distributeOrOverAnd(((AndProposition) expr).getRight());
            return new AndProposition(left, right);
        }
        // Per NotProposition e BasicStateProposition, la distribuzione non cambia nulla.
        return expr;
    }

    /**
     * Distribuisce l'AND sull'OR per ottenere la DNF.
     * Implementa la regola: A ∧ (B ∨ C) = (A ∧ B) ∨ (A ∧ C)
     */
    static SMProposition distributeAndOverOr(SMProposition expr) {
        if (expr instanceof AndProposition) {
            SMProposition left = distributeAndOverOr(((AndProposition) expr).getLeft());
            SMProposition right = distributeAndOverOr(((AndProposition) expr).getRight());
            // Se uno dei due lati è una disgiunzione, applica la distribuzione.
            if (left instanceof OrProposition) {
                SMProposition a = ((OrProposition) left).getLeft();
                SMProposition b = ((OrProposition) left).getRight();
                return new OrProposition(
                        distributeAndOverOr(new AndProposition(a, right)),
                        distributeAndOverOr(new AndProposition(b, right))
                );
            } else if (right instanceof OrProposition) {
                SMProposition a = ((OrProposition) right).getLeft();
                SMProposition b = ((OrProposition) right).getRight();
                return new OrProposition(
                        distributeAndOverOr(new AndProposition(left, a)),
                        distributeAndOverOr(new AndProposition(left, b))
                );
            } else {
                return new AndProposition(left, right);
            }
        } else if (expr instanceof OrProposition) {
            SMProposition left = distributeAndOverOr(((OrProposition) expr).getLeft());
            SMProposition right = distributeAndOverOr(((OrProposition) expr).getRight());
            return new OrProposition(left, right);
        }
        // Per NotProposition e BasicStateProposition, la distribuzione non cambia nulla.
        return expr;
    }

//    default Semantics toSem() {
//        return ConfigurationExtractor.ConvertToSemantics(this);
//    }

    /**
     * Evaluates the SMProposition on a given fully-specified configuration by creating an ad hoc Assembly.
     * It creates an Assembly with the assemblyId from the configuration and sets each machine's current state
     * according to the BasicStatePropositions in the configuration, then calls evaluate(AssemblyInterface).
     */
    default boolean evaluateConfiguration(Configuration config, AssemblyInterface properAssembly) {
        // Use the provided fully-initialized assembly instead of creating a new one.
        AssemblyInterface adHocAssembly = properAssembly; // .clone(); // Or properAssembly, if clone is not needed.

        // For each BasicStateProposition in the configuration, set the corresponding machine's current state.
        for (BasicStateProposition bsp : config.getBasicStatePropositions()) {
            machinery.StateMachine machine = adHocAssembly.getStateMachines().get(bsp.getMachineId());
            if (machine != null) {
                for (machinery.StateInterface state : machine.getStates()) {
                    if (state.getName().equals(bsp.getStateName())) {
                        machine.setCurrentState(state);
                        break;
                    }
                }
            }
        }

        // Evaluate the proposition on the ad hoc Assembly.
        return evaluate(adHocAssembly);
    }

    /**
     * Converts this SMProposition into a Semantics object by evaluating it over
     * the universe of fully-specified configurations generated from the provided Assembly.
     * Only those configurations for which the proposition evaluates to true are included.
     *
     * @param assembly the Assembly instance used to generate the universe of configurations.
     * @return a Semantics object representing the set of configurations where this proposition holds.
     */
    default Semantics toSemantics(Assembly assembly) {
        Semantics result = new Semantics(assembly.getAssemblyId());
        // Generate the full universe of configurations from the Assembly.
        Set<Configuration> universe = assembly.generateUniverse();
        for (Configuration config : universe) {
            // Evaluate the proposition on the configuration using evaluateConfiguration.
            if (this.evaluateConfiguration(config, assembly)) {
                result.addConfiguration(config);
            }
        }
        return result;
    }
}