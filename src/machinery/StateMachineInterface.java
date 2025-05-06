package machinery;

import java.io.Serializable;
import java.util.List;
import java.util.Set;

/**
 * Represents a state machine.
 */
public interface StateMachineInterface extends Serializable {
    String getName();
    List<StateInterface> getStates(); // Manteniamo l'ordine di creazione
    List<StateInterface> getLogicalStates();
    List<TransitionInterface> getTransitions();
    List<StateInterface> getInitialStates();
    void addState(StateInterface state);
    void addTransition(TransitionInterface transition);
    StateInterface getCurrentState();
    void setCurrentState(StateInterface state);
//    void initializeCurrentState();

    /**
     * Restituisce l'insieme degli eventi (trigger) associati alle transizioni controllabili.
     */
    Set<String> getEvents();

    void setName(String newName);
}