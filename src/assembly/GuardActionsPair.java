package assembly;

import smalgebra.SMProposition;

import java.util.List;

public class GuardActionsPair {
    private SMProposition guard;
    private List<Action> actions;

    public GuardActionsPair(SMProposition guard, List<Action> actions) {
        this.guard = guard;
        this.actions = actions;
    }

    public SMProposition getGuard() {
        return guard;
    }

    public List<Action> getActions() {
        return actions;
    }

    @Override
    public String toString() {
        return "[" + guard + "] 〈" + String.join(", ", actions.stream().map(Action::toString).toArray(String[]::new)) + "〉";
    }
}