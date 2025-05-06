package smalgebra;

import assembly.AssemblyInterface;

public class TrueProposition implements SMProposition {

    @Override
    public boolean evaluate(AssemblyInterface assembly) {
        return true;
    }

    @Override
    public String toString() {
        return "TRUE";
    }

    @Override
    public SMProposition clone() {
        return new TrueProposition();
    }
}