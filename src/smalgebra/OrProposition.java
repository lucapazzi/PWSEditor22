package smalgebra;

import assembly.AssemblyInterface;

/**
 * Rappresenta la disgiunzione logica (OR) di due SMProposition.
 */
public class OrProposition implements SMProposition {
    private final SMProposition left;
    private final SMProposition right;

    public OrProposition(SMProposition left, SMProposition right) {
        this.left = left;
        this.right = right;
    }

    @Override
    public boolean evaluate(AssemblyInterface assembly) {
        return left.evaluate(assembly) || right.evaluate(assembly);
    }

    public SMProposition getLeft() {
        return left;
    }

    public SMProposition getRight() {
        return right;
    }

    @Override
    public String toString() {
        return "(" + left + " OR " + right + ")";
    }

    @Override
    public SMProposition clone() {
        return new OrProposition(this.left.clone(), this.right.clone());
    }
}