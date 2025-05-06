// ================================
// File: AssemblyTruthTableMapper.java
// ================================
package smalgebra.DEMO;

import assembly.AssemblyInterface;
import machinery.State;
import machinery.StateInterface;
import machinery.StateMachine;

import java.util.ArrayList;
import java.util.Map;

/**
 * Utility class that maps the current state of each state machine in an Assembly
 * to a truth table vector representation.
 *
 * Assumptions:
 *  - The states of each state machine are ordered (for example, by insertion order).
 *    For instance, if the states are added in the order R, G, Y then that is their order.
 *  - The truth vector will have a 1 in the position corresponding to the current state,
 *    and 0 in all other positions.
 */
public class AssemblyTruthTableMapper {

    /**
     * Maps the current state of each state machine in the Assembly to a truth table string.
     * For example, if the assembly contains two state machines "tl1" and "tl2" and
     * their ordered states are [R, G, Y], then if tl1 is in state G and tl2 is in state Y,
     * the output will be:
     *
     *   "tl1: {0, 1, 0} tl2: {0, 0, 1}"
     *
     * @param assembly the Assembly containing the state machines
     * @return a string representing the truth table mapping of current states
     */
    public static String mapAssemblyToTruthTable(AssemblyInterface assembly) {
        StringBuilder sb = new StringBuilder();
        // Iterate over each state machine in the assembly.
        for (Map.Entry<String, StateMachine> entry : assembly.getStateMachines().entrySet()) {
            String machineId = entry.getKey();
            StateMachine machine = entry.getValue();
            // Assume that machine.getStates() returns the states in the correct order.
            // If not, consider maintaining an ordered list of states in the StateMachine.
            ArrayList<StateInterface> orderedStates = new ArrayList<>(machine.getStates());
            sb.append(machineId).append(": {");
            for (int i = 0; i < orderedStates.size(); i++) {
                State state = (State) orderedStates.get(i);
                // Mark 1 if this state is the current state, 0 otherwise.
                final StateInterface st1 = state;
                final String name = st1.getName();
                final StateInterface st2 = machine.getCurrentState();
                final String name1 = st2.getName();
                final boolean eq = name.equals(name1);
                sb.append(eq ? "1" : "0");
                if (i < orderedStates.size() - 1) {
                    sb.append(", ");
                }
            }
            sb.append("} ");
        }
        return sb.toString().trim();
    }
}