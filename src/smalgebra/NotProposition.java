package smalgebra;

import assembly.AssemblyInterface;

/**
 * Rappresenta la negazione logica (NOT) di una SMProposition.
 */
public class NotProposition implements SMProposition {
    private final SMProposition proposition;

    public NotProposition(SMProposition proposition) {
        this.proposition = proposition;
    }

    @Override
    public boolean evaluate(AssemblyInterface assembly) {
        return !proposition.evaluate(assembly);
    }

    public SMProposition getProposition() {
        return proposition;
    }

    @Override
    public String toString() {
        return "(NOT " + proposition + ")";
    }

    @Override
    public SMProposition clone() {
        return new NotProposition(this.proposition.clone());
    }
}