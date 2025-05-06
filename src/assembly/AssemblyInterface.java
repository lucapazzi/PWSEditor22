package assembly;

import machinery.StateMachine;
import pws.editor.semantics.Semantics;
import smalgebra.BasicStateProposition;

import java.io.Serializable;
import java.util.List;
import java.util.Map;

public interface AssemblyInterface extends Serializable {
    Map<String, StateMachine> getStateMachines();
    void addStateMachine(String identifier, StateMachine machine);

    /**
     * Restituisce tutte le assembly concrete generate (cioè, tutte le configurazioni possibili,
     * ottenute variando il current state di ciascuna macchina).
     */
    List<AssemblyInterface> getAllConcreteAssemblies();

    Semantics calculateInitialStateSemantics();

    List<BasicStateProposition> getAssemblyGuards();
    List<Action> getAssemblyActions();
}