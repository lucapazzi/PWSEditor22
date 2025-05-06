package machinery;

import java.awt.*;
import java.io.Serializable;
import java.util.*;
import java.util.List;

public class StateMachine implements StateMachineInterface, Cloneable {
    private String name;
    protected List<StateInterface> states;
    protected List<TransitionInterface> transitions;
    private StateInterface currentState;
    private Set<String> events;
    protected StateInterface pseudoState; // Pseudostato iniziale

    public StateMachine(String name) {
        this.name = name;
        this.states = new ArrayList<>();
        this.transitions = new ArrayList<>();
        this.events = new HashSet<>();
        // Posizione modificata in modo che il pseudostato sia visibile (es. (20,20))
        this.pseudoState = new State("PseudoState", new Point(20, 20));
        this.states.add(pseudoState);
    }

    public StateMachine(String name,
                        List<StateInterface> states,
                        List<TransitionInterface> transitions,
                        StateInterface currentState,
                        Set<String> events) {
        this.name = name;
        this.states = (states != null) ? states : new ArrayList<>();
        this.transitions = (transitions != null) ? transitions : new ArrayList<>();
        this.currentState = currentState;
        this.events = (events != null) ? events : new HashSet<>();
        boolean foundPseudo = false;
        for (StateInterface s : this.states) {
            if (s.getName().equals("PseudoState")) {
                foundPseudo = true;
                this.pseudoState = s;
                break;
            }
        }
        if (!foundPseudo) {
            this.pseudoState = new State("PseudoState", new Point(20, 20));
            this.states.add(this.pseudoState);
        }
    }

    // Metodi getter e setter e gli altri metodi restano invariati...
    @Override
    public String getName() {
        return name;
    }

    @Override
    public List<StateInterface> getInitialStates() {
        List<StateInterface> initialStates = new ArrayList<>();
        for (TransitionInterface t : transitions) {
            if (t.getSource() == pseudoState && t.isAutonomous()) {
                initialStates.add(t.getTarget());
            }
        }
        return initialStates;
    }

    @Override
    public void addState(StateInterface state) {
        states.add(state);
    }

    @Override
    public void addTransition(TransitionInterface transition) {
        transitions.add(transition);
        // Se la transizione è triggerable, aggiungi il trigger agli eventi della macchina.
        if (transition.isTriggerable()) {
            String trigger = transition.getTriggerEvent();
            if (trigger != null && !trigger.trim().isEmpty()) {
                events.add(trigger);
            }
        }
    }

    @Override
    public StateInterface getCurrentState() {
        return currentState;
    }

    @Override
    public void setCurrentState(StateInterface state) {
        this.currentState = state;
    }

//    @Override
//    public void initializeCurrentState() {
//        List<StateInterface> initialStates = getInitialStates();
//        if (!initialStates.isEmpty()) {
//            this.currentState = initialStates.get(0);
//        }
//    }

    @Override
    public Set<String> getEvents() {
        return events;
    }

    @Override
    public void setName(String newName) {
        this.name = newName;
    }

    public List<StateInterface> getLogicalStates() {
        List<StateInterface> logicalStates = new ArrayList<>();
        for (StateInterface state : states) {
            if (state != this.pseudoState) {
                logicalStates.add(state);
            }
        }
        return logicalStates;
    }
    @Override
    public List<StateInterface> getStates() {
        return states;
    }

    public void setStates(List<StateInterface> states) {
        this.states = states;
    }

    @Override
    public List<TransitionInterface> getTransitions() {
        return transitions;
    }

    public void setTransitions(List<TransitionInterface> transitions) {
        this.transitions = transitions;
    }

    @Override
    public StateMachine clone() {
        // Create a new StateMachine with the same name.
        // Note: the constructor automatically creates a pseudoState.
        StateMachine clone = new StateMachine(this.getName());
        Map<StateInterface, StateInterface> stateMap = new HashMap<>();

        // --- Clone states ---
        for (StateInterface s : this.getStates()) {
            // Create a new state with the same name and a copy of its position.
            State newState = new State(s.getName(), new Point(s.getPosition()));
            stateMap.put(s, newState);
            clone.addState(newState);
        }

        // --- Clone transitions ---
        for (TransitionInterface t : this.getTransitions()) {
            // Get the cloned source and target states from the stateMap.
            StateInterface clonedSource = stateMap.get(t.getSource());
            StateInterface clonedTarget = stateMap.get(t.getTarget());
            // Create a new Transition with the same properties.
            Transition newTransition = new Transition(clonedSource, clonedTarget, t.isAutonomous(), t.getTriggerEvent());
            // Copy the controlPoint if it exists. This deep-copies the Point.
            Point originalControlPoint = ((Transition) t).getControlPoint();
            if (originalControlPoint != null) {
                newTransition.setControlPoint(new Point(originalControlPoint));
            }
            clone.addTransition(newTransition);

            // Update the incoming/outgoing relationships for the cloned states.
            if (clonedSource != null && clonedSource.getOutgoingTransitions() != null) {
                clonedSource.getOutgoingTransitions().add(newTransition);
            }
            if (clonedTarget != null && clonedTarget.getIncomingTransitions() != null) {
                clonedTarget.getIncomingTransitions().add(newTransition);
            }
        }

        // --- Clone events ---
        clone.events.addAll(this.events);

        // --- Fix duplicate pseudoState issue ---
        // The StateMachine constructor adds a default pseudoState that isn't part of the original.
        clone.getStates().remove(clone.pseudoState);
        if (stateMap.containsKey(this.pseudoState)) {
            clone.pseudoState = stateMap.get(this.pseudoState);
            if (!clone.getStates().contains(clone.pseudoState)) {
                clone.getStates().add(clone.pseudoState);
            }
        }

        return clone;
    }
    public void setEvents(Set<String> events) {
        this.events = events;
    }

    public StateInterface getPseudoState() {
        return pseudoState;
    }

    public void setPseudoState(StateInterface pseudoState) {
        this.pseudoState = pseudoState;
    }
}