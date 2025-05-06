package utility;

import assembly.AssemblyInterface;
import machinery.StateInterface;
import machinery.StateMachine;

import javax.swing.*;
import java.awt.*;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

public class PWSDialogs {

    /**
     * Mostra un dialogo per la scelta della guardia e delle azioni.
     * La guardia è una coppia "machineId.stateName" e per le azioni, per ciascun machineId,
     * l'utente può scegliere una sola azione nel formato "machineId.event".
     *
     * @param assembly L'assembly contenente le state machine di base.
     * @return Un array di due stringhe: [guard, azioni]. Se l'utente annulla, restituisce {"", ""}.
     */
    public static String[] askForGuardAndAction(AssemblyInterface assembly) {
        // Costruiamo la lista delle guardie.
        List<String> guardOptions = new ArrayList<>();
        // Per le azioni, vogliamo avere una mappa da machineId a lista di azioni.
        Map<String, List<String>> actionOptionsMap = new LinkedHashMap<>();

        // Supponiamo che assembly.getStateMachines() restituisca una Map<String, StateMachine>
        Map<String, StateMachine> machines = assembly.getStateMachines();
        for (Map.Entry<String, StateMachine> entry : machines.entrySet()) {
            String machineId = entry.getKey();
            StateMachine machine = entry.getValue();

            // Per le guardie: per ogni stato della macchina, aggiungiamo "machineId.stateName".
            for (StateInterface s : machine.getStates()) {
                guardOptions.add(machineId + "." + s.getName());
            }

            // Per le azioni: per ogni evento della macchina, aggiungiamo "machineId.event".
            List<String> actionList = new ArrayList<>();
            if (machine.getEvents() != null) {
                for (String event : machine.getEvents()) {
                    actionList.add(machineId + "." + event);
                }
            }
            actionOptionsMap.put(machineId, actionList);
        }

        // Creiamo il pannello per il dialogo.
        JPanel panel = new JPanel(new GridBagLayout());
        GridBagConstraints gbc = new GridBagConstraints();
        gbc.insets = new Insets(5, 5, 5, 5);

        // Riga 0: Label e JComboBox per la guardia.
        gbc.gridx = 0;
        gbc.gridy = 0;
        panel.add(new JLabel("Seleziona una guard (m.S):"), gbc);
        gbc.gridx = 1;
        JComboBox<String> guardCombo = new JComboBox<>(guardOptions.toArray(new String[0]));
        guardCombo.setPreferredSize(new Dimension(200, 25));
        panel.add(guardCombo, gbc);

        // Riga successive: per ciascun machineId, aggiungiamo una riga per la scelta dell'azione.
        Map<String, JComboBox<String>> actionCombos = new LinkedHashMap<>();
        int row = 1;
        for (Map.Entry<String, List<String>> entry : actionOptionsMap.entrySet()) {
            String machineId = entry.getKey();
            List<String> actions = entry.getValue();

            gbc.gridx = 0;
            gbc.gridy = row;
            panel.add(new JLabel("Azione per " + machineId + ":"), gbc);

            gbc.gridx = 1;
            // Creiamo un JComboBox per le azioni con una opzione predefinita "None".
            String[] actionArray = new String[actions.size() + 1];
            actionArray[0] = "None";
            for (int i = 0; i < actions.size(); i++) {
                actionArray[i + 1] = actions.get(i);
            }
            JComboBox<String> actionCombo = new JComboBox<>(actionArray);
            actionCombo.setPreferredSize(new Dimension(200, 25));
            panel.add(actionCombo, gbc);
            actionCombos.put(machineId, actionCombo);
            row++;
        }

        int result = JOptionPane.showConfirmDialog(null, panel, "Seleziona Guard e Azione",
                JOptionPane.OK_CANCEL_OPTION, JOptionPane.PLAIN_MESSAGE);
        if (result == JOptionPane.OK_OPTION) {
            String selectedGuard = (String) guardCombo.getSelectedItem();
            // Per le azioni, raccogliamo una sola azione per ciascun machineId (saltando "None")
            List<String> chosenActions = new ArrayList<>();
            for (Map.Entry<String, JComboBox<String>> entry : actionCombos.entrySet()) {
                String selected = (String) entry.getValue().getSelectedItem();
                if (selected != null && !selected.equals("None")) {
                    chosenActions.add(selected);
                }
            }
            // Costruiamo la stringa delle azioni, separata da virgole.
            String actionsStr = String.join(", ", chosenActions);
            return new String[] { selectedGuard != null ? selectedGuard : "", actionsStr };
        } else {
            return new String[] { "", "" };
        }
    }
}