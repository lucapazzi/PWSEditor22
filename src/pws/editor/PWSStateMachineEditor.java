package pws.editor;

import editor.StateMachineEditor;
import pws.PWSStateMachine;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

public class PWSStateMachineEditor extends StateMachineEditor {

    public PWSStateMachineEditor(PWSStateMachine stateMachine, String title) {
        super(stateMachine, title);
        // Sostituisce il pannello base con il pannello specifico per PWS.
        getContentPane().remove(statePanel);
        statePanel = new PWSStateMachinePanel(stateMachine);
        getContentPane().add(statePanel, BorderLayout.CENTER);

        // Crea una toolbar per aggiungere il pulsante "Aggiorna semantica"
        JPanel toolbar = new JPanel();
        toolbar.setLayout(new FlowLayout(FlowLayout.LEFT));
        JButton updateSemanticButton = new JButton("Aggiorna semantica");
        updateSemanticButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                // Richiama il metodo recalculateSemantics sulla state machine
                ((PWSStateMachine) stateMachine).recalculateSemantics();
                statePanel.revalidate();
                statePanel.repaint();
            }
        });
        toolbar.add(updateSemanticButton);
        getContentPane().add(toolbar, BorderLayout.NORTH);

        revalidate();
        repaint();
    }
}