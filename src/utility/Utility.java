package utility;

import assembly.Action;
import assembly.ActionList;
import assembly.AssemblyInterface;
import machinery.StateInterface;
import machinery.StateMachine;
import machinery.TransitionInterface;
import smalgebra.*;

public class Utility {
    /**
     * Questo metodo statico trasforma una SMProposition
     * sostituendo, per una data macchina, ogni occorrenza dello stato "fromState" con "toState".
     *
     * La trasformazione avviene ricorsivamente sulla struttura della SMProposition:
     *
     *   - Se la proposizione è elementare (BasicStateProposition) e riguarda la macchina e lo stato interessato,
     *     viene restituita una nuova BasicStateProposition con lo stato sostituito.
     *   - Se è composta con operatori booleani (AND, OR, NOT), la trasformazione viene applicata ricorsivamente
     *     ai suoi sotto-argomenti.
     *
     * @param proposition la SMProposition originale
     * @param machineId   l'identificatore della macchina interessata
     * @param fromState   lo stato da sostituire
     * @param toState     lo stato sostitutivo
     * @return una nuova SMProposition con la sostituzione applicata
     */
    public static SMProposition transformByMachineIdAndState(SMProposition proposition, String machineId, String fromState, String toState) {
        if (proposition instanceof BasicStateProposition) {
            BasicStateProposition bsp = (BasicStateProposition) proposition;
            // Se la proposizione elementare riguarda la macchina e lo stato da sostituire,
            // restituisce una nuova proposizione elementare con il nuovo stato.
            if (bsp.getMachineId().equals(machineId) && bsp.getStateName().equals(fromState)) {
                return new BasicStateProposition(machineId, toState);
            } else {
                return proposition;
            }
        } else if (proposition instanceof AndProposition) {
            AndProposition ap = (AndProposition) proposition;
            SMProposition newLeft = transformByMachineIdAndState(ap.getLeft(), machineId, fromState, toState);
            SMProposition newRight = transformByMachineIdAndState(ap.getRight(), machineId, fromState, toState);
            return new AndProposition(newLeft, newRight);
        } else if (proposition instanceof OrProposition) {
            OrProposition op = (OrProposition) proposition;
            SMProposition newLeft = transformByMachineIdAndState(op.getLeft(), machineId, fromState, toState);
            SMProposition newRight = transformByMachineIdAndState(op.getRight(), machineId, fromState, toState);
            return new OrProposition(newLeft, newRight);
        } else if (proposition instanceof NotProposition) {
            NotProposition np = (NotProposition) proposition;
            SMProposition newProp = transformByMachineIdAndState(np.getProposition(), machineId, fromState, toState);
            return new NotProposition(newProp);
        } else {
            // Se la SMProposition non è riconosciuta, restituiscila invariata.
            return proposition;
        }
    }

    /**
     * Trasforma la SMProposition base applicando, per ciascuna azione presente in actions, la seguente procedura:
     *
     * 1. Per ciascuna azione (ad esempio "m1.e") in actions:
     *    1.1 Recupera la state machine corrispondente dall'assembly, utilizzando l'identificatore (machineId).
     *    1.2 Per ciascuno stato S della state machine:
     *          1.2.1 Se lo stato appartiene alla proposizione da trasformare
     *              a) Per ciascuna transizione triggerable in uscita da S avente trigger uguale a quello dell'azione,
     *              trasforma pre in post tramite SMPropositionTransformer.transformByMachineIdAndState.
     *
     * 2. Se nessuna azione produce trasformazioni, restituisce base; altrimenti restituisce post.
     *
     * @param base La SMProposition di partenza.
     * @param actions La lista di azioni da applicare.
     * @param assembly L'assembly da cui risalire alle state machine.
     * @return La SMProposition risultante.
     */
    public static SMProposition applyActions(SMProposition base, ActionList actions, AssemblyInterface assembly) {
        SMProposition workCopy  = base; // .clone();

        // Per ciascuna azione nella lista
        for (Action a : actions) {
            // separo id da evento
            String machineId = a.getMachineId();
            String event = a.getEvent();

            // Recupera la state machine dall'assembly attraverso l'id dell'azione
            StateMachine machine = assembly.getStateMachines().get(machineId);
            if (machine == null) {
                continue; // Se non vi sono macchine a stati associate a quell'id, passa alla prossima azione
            }

            // Per ogni stato della state machine
            for (StateInterface s : machine.getStates()) {
                //  Per ogni transizione che origina da quello stato
                // 1.2.1 Se lo stato appartiene alla proposizione da trasformare
                BasicStateProposition bsp = new BasicStateProposition(machineId, s.getName());
                if (bsp.ontoImplies(base,assembly)) {
                    // allora per ciascuna delle sue transizioni che ha event come trigger
                    for (TransitionInterface t : s.getOutgoingTransitions()) {
                        // se t ha event come trigger
                        if (t.isTriggerable() && t.getTriggerEvent().equals(event)) {
                            // Trasforma pre in post usando il trasformatore
                            workCopy = Utility.transformByMachineIdAndState(workCopy, machineId, t.getSource().getName(), t.getTarget().getName());
                            // Aggrega il risultato con OR logico: se result è null, post diventa result; altrimenti,
                            // result = OR(result, post)
                        }
                    }
                }
            }
        }
        return workCopy;
    }


}
