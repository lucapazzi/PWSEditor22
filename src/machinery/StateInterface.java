package machinery;

import java.awt.*;
import java.io.Serializable;
import java.util.List;
import java.util.stream.Collectors;

public interface StateInterface extends Serializable {
    String getName();
    void setName(String newName);
//    boolean isInitial();
    List<TransitionInterface> getOutgoingTransitions();
    List<TransitionInterface> getIncomingTransitions();
    void addOutgoingTransition(TransitionInterface transition);
    void addIncomingTransition(TransitionInterface transition);
    Point getPosition();
    void setPosition(Point p);
    // boolean isInitial();

    default List<TransitionInterface> getTriggerableOutgoingTransitions() {
        return getOutgoingTransitions().stream()
                .filter(TransitionInterface::isTriggerable)
                .collect(Collectors.toList());
    }


    default List<TransitionInterface> getAutonomousOutgoingTransitions() {
        return getOutgoingTransitions().stream()
                .filter(TransitionInterface::isAutonomous)
                .collect(Collectors.toList());
    }


    default List<TransitionInterface> getTriggerableIncomingTransitions() {
        return getIncomingTransitions().stream()
                .filter(TransitionInterface::isTriggerable)
                .collect(Collectors.toList());
    }

    default List<TransitionInterface> getAutonomousIncomingTransitions() {
        return getIncomingTransitions().stream()
                .filter(TransitionInterface::isAutonomous)
                .collect(Collectors.toList());
    }
}