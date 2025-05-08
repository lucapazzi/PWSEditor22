package pws.editor.semantics;

import java.util.*;
import java.util.logging.Logger;
import java.util.logging.Level;
import java.util.ArrayList;

import assembly.Action;
import smalgebra.TrueProposition;

import machinery.StateInterface;
import pws.PWSState;
import pws.PWSStateMachine;
import pws.PWSTransition;
import machinery.TransitionInterface;
import assembly.Assembly;
import pws.editor.semantics.Semantics;

/**
 * Visitor that computes fixed‑point semantics for all states in a PWSStateMachine.
 * Each state’s semantics is the union of the contributions of its incoming
 * transitions, where:
 *
 * <ul>
 *   <li>triggerable (and initial) transitions apply their guard AND then any actions to
 *       the source state’s <i>stateSemantics</i>;</li>
 *   <li>reactive (autonomous) transitions apply internal transformations
 *       (via ExitZone) to the source state’s <i>reactiveSemantics</i> and then any actions.</li>
 * </ul>
 */
public class SemanticsVisitor {
    private static final Logger logger = Logger.getLogger(SemanticsVisitor.class.getName());

    /**
     * Iteratively computes a semantics map for every PWSState until convergence.
     */
    public static Map<PWSState, Semantics> computeAllStateSemantics(PWSStateMachine machine) {
        logger.info("Starting fixed-point semantics computation for machine '" + machine.getName() + "'.");

        Assembly asm = machine.getAssembly();
        Map<PWSState, Semantics> semMap = new HashMap<>();
        for (StateInterface s : machine.getStates()) {
            semMap.put((PWSState) s, Semantics.bottom(asm.getAssemblyId()));
        }
        Semantics initSem = machine.getAssembly().calculateInitialStateSemantics();
        // Seed the actual pseudostate instance in semMap
        for (PWSState s : semMap.keySet()) {
            if (s.isPseudoState()) {
                semMap.put(s, initSem);
                break;
            }
        }
        boolean changed = true;
        int iter = 0;
        int maxIter = 1000; // example cap, adjust as necessary
        while (changed && iter < maxIter) {
            logger.info("Iteration " + (iter + 1) + ":");
            changed = false;
            // Update each non-pseudostate’s reactive semantics before computing new state semantics
            for (PWSState ps : new ArrayList<>(semMap.keySet())) {
                if (!ps.isPseudoState()) {
                    HashSet<ExitZone> zones = machine.computeReactiveSemantics(semMap.get(ps));
                    ps.setReactiveSemantics(zones);
                }
            }
            for (StateInterface s : machine.getStates()) {
                // skip pseudostate so we do not overwrite its initial semantics
                if (s instanceof PWSState && ((PWSState) s).isPseudoState()) {
                    continue;
                }
                Semantics newSem = computeStateSemanticsOnce((PWSState) s, machine, semMap);
                if (!newSem.equals(semMap.get(s))) {
                    semMap.put((PWSState) s, newSem);
                    changed = true;
                }
            }
            iter++;
            logger.info("------------------------------");
        }
        if (iter >= maxIter) {
            logger.warning("SemanticsVisitor reached iteration cap (" + maxIter + " iterations) for machine '" + machine.getName() + "'. Results may not have fully converged.");
        }
        logger.info("Completed semantics computation in " + iter + " iterations for machine '" + machine.getName() + "'.");

        return semMap;
    }

    /**
     * Compute the semantics for a single target state in one iteration of the fixed-point algorithm.
     *
     * <p>This method aggregates the contributions of all incoming transitions whose target is the specified state.
     * It handles two kinds of transitions:
     * <ul>
     *   <li><b>Triggerable or initial transitions</b>: applies the guard proposition AND-ed with the source state's
     *       current semantics.</li>
     *   <li><b>Reactive (autonomous) transitions</b>: for each exit zone associated with the source state, applies
     *       the corresponding internal state-machine transition to the reactive semantics, then ORs the results.</li>
     * </ul>
     *
     * <p>After processing all transitions, the aggregated semantics captures the new “stateSemantics” for the target.
     *
     * @param target    the PWSState for which to compute updated semantics
     * @param machine   the state machine containing the transitions and assembly context
     * @param currentMap map of PWSState to their current semantics from the previous iteration
     * @return the newly computed Semantics for the target state
     */
    private static Semantics computeStateSemanticsOnce(
            PWSState target,
            PWSStateMachine machine,
            Map<PWSState, Semantics> currentMap) {
        logger.info(">> computeStateSemanticsOnce START for target='" + target.getName() + "'");
        logger.info("    Current semantics for state '" + target.getName() + "': " + currentMap.get(target));


        // Retrieve the assembly context for semantics conversions
        Assembly asm = machine.getAssembly();
        // Initialize accumulator to ⊥ (no configurations) for fixed-point aggregation
        Semantics agg = Semantics.bottom(asm.getAssemblyId());


        // Iterate through all transitions in the machine
        for (TransitionInterface ti : machine.getTransitions()) {
            // Skip any non-PWS transitions
            if (!(ti instanceof PWSTransition)) continue;
            // Cast to PWS-specific transition type
            PWSTransition t = (PWSTransition) ti;
            // Only process transitions whose target matches the current state
            if (t.getTarget() != target) continue;
            PWSState src = (PWSState) t.getSource();
            // Use working semantics instead of state fields
            Semantics base = currentMap.get(src);
            Semantics contrib = computeTransitionContribution(t, base, asm);
            logger.info("Transition from '" + src.getName() + "': "
                    + currentMap.get(src)
                    + " contributes " + contrib
                    + " to state '" + target.getName() + "'");
            // OR-accumulate the contribution into the aggregate for target state
            agg = agg.OR(contrib);
        }

        logger.info("<< computeStateSemanticsOnce END for target='" + target.getName() + "': result=" + agg);
        return agg;
    }
    /**
     * Compute a single transition’s contribution using the working base semantics.
     */
    private static Semantics computeTransitionContribution(
            PWSTransition t,
            Semantics base,
            Assembly asm) {
        Semantics result;
        // Triggerable or initial
        if (t.isTriggerable() || ((PWSState) t.getSource()).isPseudoState()) {
            Semantics guardSem = t.getGuardProposition().toSemantics(asm);
            result = base.AND(guardSem);
        } else {
            // Reactive/autonomous
            result = Semantics.bottom(asm.getAssemblyId());
            for (ExitZone ez : ((PWSState) t.getSource()).getReactiveSemantics()) {
                if (t.getGuardProposition() instanceof TrueProposition
                        || ez.getTarget().equals(t.getGuardProposition())) {
                    Semantics frag = base.transformByMachineTransition(
                            ez.getStateMachineId(),
                            ez.getTransition(),
                            asm);
                    result = result.OR(frag);
                }
            }
        }
        // Apply post-actions
        for (Action a : t.getActionList()) {
            result = result.transformByMachineEvent(a.getMachineId(), a.getEvent(), asm);
        }
        return result;
    }
}