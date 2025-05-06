package smalgebra;

import assembly.AssemblyInterface;

public class FalseProposition implements SMProposition {

    @Override
    public boolean evaluate(AssemblyInterface assembly) {
        return false;
    }

    @Override
    public String toString() {
        return "FALSE";
    }

    @Override
    public SMProposition clone() {
        return new FalseProposition();
    }
}