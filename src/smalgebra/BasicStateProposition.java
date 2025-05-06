package smalgebra;

import assembly.Assembly;
import assembly.AssemblyInterface;
import machinery.StateInterface;
import pws.editor.semantics.Configuration;
import pws.editor.semantics.Semantics;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * Rappresenta una proposizione di stato elementare del tipo "machineId.stateName".
 */
public class BasicStateProposition implements SMProposition {
    private final String machineId;
    private final String stateName;

    public BasicStateProposition(String machineId, String stateName) {
        this.machineId = machineId;
        this.stateName = stateName;
    }

    @Override
    public boolean evaluate(AssemblyInterface assembly) {
        machinery.StateMachine machine = assembly.getStateMachines().get(machineId);
        if (machine == null) {
            return false;
        }
        StateInterface current = machine.getCurrentState();
        if (current == null) {
            return false;
        }
        return current.getName().equals(stateName);
    }

    public String getMachineId() {
        return machineId;
    }
    public String getStateName() {
        return stateName;
    }

    @Override
    public String toString() {
        return machineId + "." + stateName;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof BasicStateProposition)) return false;
        BasicStateProposition that = (BasicStateProposition) o;
        return Objects.equals(machineId, that.machineId) &&
                Objects.equals(stateName, that.stateName);
    }

    @Override
    public int hashCode() {
        return Objects.hash(machineId, stateName);
    }

    @Override
    public SMProposition clone() {
        return new BasicStateProposition(this.machineId, this.stateName);
    }

    /**
     * Returns a Configuration containing only this BasicStateProposition.
     * The configuration is created using the provided assembly's identifier.
     *
     * @param assembly The Assembly instance used to derive the configuration.
     * @return A Configuration containing this BasicStateProposition.
     */
    public Configuration toConf(Assembly assembly) {
        List<BasicStateProposition> props = new ArrayList<>();
        props.add(this);
        return Configuration.fromBasicStatePropositions(assembly.getAssemblyId(), props);
    }

    /**
     * Returns a Semantics containing a single configuration corresponding to this BasicStateProposition.
     * The Semantics will have the same assembly identifier as the provided assembly.
     *
     * @param assembly The Assembly instance used to derive the semantics.
     * @return A Semantics containing the configuration derived from this BasicStateProposition.
     */
    public Semantics toSemantics(Assembly assembly) {
        Semantics sem = new Semantics(assembly.getAssemblyId());
        sem.addConfiguration(this.toConf(assembly));
        return sem;
    }
}