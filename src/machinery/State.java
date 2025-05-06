package machinery;

import java.awt.*;
import java.util.ArrayList;
import java.util.List;

public class State implements StateInterface {
    private String name;
//    private boolean initial = false;
    private List<TransitionInterface> outgoingTransitions;
    private List<TransitionInterface> incomingTransitions;

    private Point position;

    public State() {
        this.outgoingTransitions = new ArrayList<>();
        this.incomingTransitions = new ArrayList<>();
    }

    public State(String name,
                 Point position) {
        this.name = name;
        this.position = position;
        this.outgoingTransitions = new ArrayList<>();
        this.incomingTransitions = new ArrayList<>();
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public void setName(String newName) {
        this.name = newName;
    }

//    @Override
//    public boolean isInitial() {
//        return initial;
//    }

    @Override
    public List<TransitionInterface> getOutgoingTransitions() {
        return outgoingTransitions;
    }

    @Override
    public List<TransitionInterface> getIncomingTransitions() {
        return incomingTransitions;
    }

    @Override
    public void addOutgoingTransition(TransitionInterface transition) {
        if (!outgoingTransitions.contains(transition)) {
            outgoingTransitions.add(transition);
        }
    }

    @Override
    public void addIncomingTransition(TransitionInterface transition) {
        if (!incomingTransitions.contains(transition)) {
            incomingTransitions.add(transition);
        }
    }

    @Override
    public Point getPosition() {
        return position;
    }

    @Override
    public void setPosition(Point p) {
        this.position = p;
    }
}