package assembly;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collection;

public class ActionList extends ArrayList<Action> implements Serializable {

    public ActionList() {
        super();
    }

    public ActionList(Collection<? extends Action> c) {
        super(c);
    }

    @Override
    public String toString() {
        if (this.isEmpty()) {
            return "〈 〉";
        }
        StringBuilder sb = new StringBuilder("〈 ");
        for (int i = 0; i < this.size(); i++) {
            sb.append(this.get(i).toString());
            if (i < this.size() - 1) {
                sb.append(", ");
            }
        }
        sb.append(" 〉");
        return sb.toString();
    }
}