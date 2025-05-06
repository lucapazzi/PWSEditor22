package pws.editor.semantics;

import machinery.Transition;
import smalgebra.BasicStateProposition;

import java.io.Serializable;
import java.util.Objects;

/**
 * An ExitZone represents one autonomous‐transition “exit” from a PWSState’s reactive semantics.
 *
 * <p>Each ExitZone records:
 * <ul>
 *   <li><b>stateMachineId</b>: the ID of the component state machine where the autonomous transition occurs;</li>
 *   <li><b>transition</b>: the specific autonomous transition object;</li>
 *   <li><b>source</b>: a BasicStateProposition naming the machine and source state, indicating
 *       the condition under which the autonomous transition fires;</li>
 *   <li><b>target</b>: a BasicStateProposition naming the machine and target state, indicating
 *       the outcome state and thus the “deviation” from the PWSState’s own semantics.</li>
 * </ul>
 *
 * <p>In computing reactive transitions, we match an ExitZone’s target proposition against
 * the guard proposition of a PWSTransition.  Whenever they coincide, we apply an
 * <i>internal transformation</i> of the PWSState’s reactive semantics by invoking
 * {@code stateSemantics.transformByMachineTransition(...)} with the zone’s machineId
 * and transition.  Multiple matching zones are OR‑ed together to yield the transition’s
 * contribution to the target state’s overall semantics.
 */

public class ExitZone implements Serializable {
    private String stateMachineId = null;
    private Transition transition = null;
    private BasicStateProposition source = null;
    private BasicStateProposition target = null;

    public ExitZone(String stateMachineId, Transition transition, BasicStateProposition source, BasicStateProposition target) {
        this.stateMachineId = stateMachineId;
        this.transition = transition;
        this.source = source;
        this.target = target;
    }

    public String getStateMachineId() {
        return stateMachineId;
    }

    public void setStateMachineId(String stateMachineId) {
        this.stateMachineId = stateMachineId;
    }

    public void setTransition(Transition transition) {
        this.transition = transition;
    }

    public Transition getTransition() {
        return transition;
    }

    public void setSource(BasicStateProposition source) {
        this.source = source;
    }

    public void setTarget(BasicStateProposition target) {
        this.target = target;
    }

    public BasicStateProposition getSource() {
        return source;
    }

    public BasicStateProposition getTarget() {
        return target;
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof ExitZone exitZone)) return false;
        return Objects.equals(stateMachineId, exitZone.stateMachineId) && Objects.equals(transition, exitZone.transition) && Objects.equals(source, exitZone.source) && Objects.equals(target, exitZone.target);
    }

    @Override
    public int hashCode() {
        return Objects.hash(stateMachineId, transition, source, target);
    }

    @Override
    public String toString() {
        return source.getMachineId() + ":" + " (" + source.getStateName() + "->" + target.getStateName() + ")";
        // return source.toString() + "⧴" + target.toString();
        // return target.toString();
    }
}
