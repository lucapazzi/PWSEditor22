package machinery;

import java.awt.*;
import java.io.Serializable;

public interface TransitionInterface extends Serializable {
    StateInterface getSource();
    StateInterface getTarget();
    boolean isAutonomous(); // true se la transizione è autonoma

    /**
     * Se la transizione è triggerable, restituisce il trigger event associato;
     * altrimenti, può restituire null o una stringa vuota.
     */
    String getTriggerEvent();

    void fire();

    /**
     * Metodo di utilità: restituisce true se la transizione è triggerable,
     * ossia non è autonoma e il trigger event non è null né vuoto.
     */
    default boolean isTriggerable() {
        return !isAutonomous() && getTriggerEvent() != null && !getTriggerEvent().isEmpty();
    }

    void setTriggerOffset(Point point);
    Point getTriggerOffset();
}