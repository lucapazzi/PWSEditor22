package smalgebra;

import assembly.Assembly;
import assembly.AssemblyInterface;

/**
 * Rappresenta la congiunzione logica (AND) di due SMProposition.
 */
public class AndProposition implements SMProposition {
    private final SMProposition left;
    private final SMProposition right;

    public AndProposition(SMProposition left, SMProposition right) {
        this.left = left;
        this.right = right;
    }

    @Override
    public boolean evaluate(AssemblyInterface assembly) {
        return left.evaluate(assembly) && right.evaluate(assembly);
    }

    public SMProposition getLeft() {
        return left;
    }

    public SMProposition getRight() {
        return right;
    }

    @Override
    public String toString() {
        return "(" + left + " AND " + right + ")";
    }

    @Override
    public SMProposition clone() {
        return new AndProposition(this.left.clone(), this.right.clone());
    }
}