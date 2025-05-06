package pws.editor;

import assembly.AssemblyInterface;
import machinery.StateMachine;
import pws.PWSStateMachine;

import javax.swing.*;
import java.awt.*;
import java.util.Map;

public class AssemblyPanel extends JPanel {
    private AssemblyInterface assembly;
    private DefaultListModel<String> listModel;
    private JList<String> stateMachineList;

    public AssemblyPanel(AssemblyInterface assembly) {
        this.assembly = assembly;
        setLayout(new BorderLayout());
        listModel = new DefaultListModel<>();
        stateMachineList = new JList<>(listModel);
        refreshList();
        add(new JScrollPane(stateMachineList), BorderLayout.CENTER);

        JPanel buttonPanel = new JPanel();
        JButton addButton = new JButton("Aggiungi");
        JButton editButton = new JButton("Modifica");
        JButton removeButton = new JButton("Rimuovi");

        addButton.addActionListener(e -> onAdd());
        editButton.addActionListener(e -> onEdit());
        removeButton.addActionListener(e -> onRemove());

        buttonPanel.add(addButton);
        buttonPanel.add(editButton);
        buttonPanel.add(removeButton);

        add(buttonPanel, BorderLayout.SOUTH);
    }

    private void refreshList() {
        listModel.clear();
        for(String id: assembly.getStateMachines().keySet()) {
            StateMachine machine = assembly.getStateMachines().get(id);
            listModel.addElement(id + " - " + machine.getName());
        }
    }

    private void onAdd() {
        // Chiedi un identificatore univoco
        String id = JOptionPane.showInputDialog(this, "Inserisci un identificatore univoco:");
        if (id == null || id.trim().isEmpty()) {
            return;
        }
        // Chiedi se si desidera una nuova macchina o usare una esistente
        int option = JOptionPane.showOptionDialog(this,
                "Vuoi creare una nuova macchina o selezionare una già presente?",
                "Aggiungi StateMachine",
                JOptionPane.YES_NO_OPTION,
                JOptionPane.QUESTION_MESSAGE,
                null,
                new Object[] {"Nuova", "Esistente"},
                "Nuova");
        if(option == JOptionPane.YES_OPTION) {
            // Crea una nuova PWSStateMachine
            String name = JOptionPane.showInputDialog(this, "Inserisci il nome della macchina:");
            if(name == null || name.trim().isEmpty()){
                return;
            }
            StateMachine newMachine = new PWSStateMachine(name);
            assembly.addStateMachine(id, newMachine);
        } else if(option == JOptionPane.NO_OPTION) {
            // Seleziona una macchina esistente: mostriamo una lista degli identificatori già presenti
            Map<String, StateMachine> machines = assembly.getStateMachines();
            if(machines.isEmpty()){
                JOptionPane.showMessageDialog(this, "Non ci sono macchine esistenti. Verrà creata una nuova macchina.");
                String name = JOptionPane.showInputDialog(this, "Inserisci il nome della macchina:");
                if(name == null || name.trim().isEmpty()){
                    return;
                }
                StateMachine newMachine = new PWSStateMachine(name);
                assembly.addStateMachine(id, newMachine);
            } else {
                Object[] options = machines.keySet().toArray();
                String selectedId = (String) JOptionPane.showInputDialog(this, "Seleziona una macchina:",
                        "Macchine esistenti", JOptionPane.PLAIN_MESSAGE, null, options, options[0]);
                if(selectedId != null) {
                    StateMachine existingMachine = machines.get(selectedId);
                    // Aggiungi la stessa macchina con il nuovo identificatore
                    assembly.addStateMachine(id, existingMachine);
                }
            }
        }
        refreshList();
    }

    private void onEdit() {
        String selected = stateMachineList.getSelectedValue();
        if(selected == null) return;
        // Estrai l'identificatore (assumendo formato "id - nome")
        String id = selected.split(" - ")[0];
        String newName = JOptionPane.showInputDialog(this, "Modifica il nome della macchina:",
                assembly.getStateMachines().get(id).getName());
        if(newName != null && !newName.trim().isEmpty()){
            assembly.getStateMachines().get(id).setName(newName);
            refreshList();
        }
    }

    private void onRemove() {
        String selected = stateMachineList.getSelectedValue();
        if(selected == null) return;
        String id = selected.split(" - ")[0];
        int confirm = JOptionPane.showConfirmDialog(this,
                "Sei sicuro di voler rimuovere la macchina con identificatore " + id + "?",
                "Conferma", JOptionPane.YES_NO_OPTION);
        if(confirm == JOptionPane.YES_OPTION) {
            assembly.getStateMachines().remove(id);
            refreshList();
        }
    }
}