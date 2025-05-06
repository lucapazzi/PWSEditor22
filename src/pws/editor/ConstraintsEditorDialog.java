package pws.editor;

import assembly.Assembly;
import pws.PWSState;
import pws.editor.semantics.Semantics;
import pws.editor.semantics.Configuration;
import smalgebra.BasicStateProposition;

import javax.swing.*;
import java.awt.*;
import java.util.Map;
import java.util.LinkedHashMap;
import java.util.Set;
import java.util.HashSet;

public class ConstraintsEditorDialog extends JDialog {
    private JTextArea textArea;
    private JButton applyButton, cancelButton;
    private PWSState state;  // the state whose constraint semantics we're editing
    private Assembly assembly; // Added field

    public ConstraintsEditorDialog(PWSState state, Assembly assembly) { // Modified constructor
        this.state = state;
        this.assembly = assembly;
        setModal(true);
        setTitle("Edit Constraints Semantics");
        textArea = new JTextArea(10, 30);
        // Prepopulate with current constraints semantics
        textArea.setText(getConstraintsTextFromState(state));

        applyButton = new JButton("Apply");
        cancelButton = new JButton("Cancel");

        applyButton.addActionListener(e -> {
            String text = textArea.getText();
            Semantics newConstraints = parseConfigurations(text);
            state.setConstraintsSemantics(newConstraints);
            state.setRawConstraintText(text.trim());
            dispose();
        });
        cancelButton.addActionListener(e -> dispose());

        JPanel buttonPanel = new JPanel();
        buttonPanel.add(applyButton);
        buttonPanel.add(cancelButton);
        add(new JScrollPane(textArea), BorderLayout.CENTER);
        add(buttonPanel, BorderLayout.SOUTH);
        pack();
        setLocationRelativeTo(null);
    }

    private Semantics parseConfigurations(String text) {
        // For each non-empty line in text, parse the configuration, then union them
        Semantics result = Semantics.bottom(assembly); // Modified call
        for (String line : text.split("\\n")) {
            if (!line.trim().isEmpty()) {
                // Here, parse each line into a Semantics object.
                Semantics confSem = parseConfigurationLine(line.trim());
                result = result.OR(confSem);
            }
        }
        return result;
    }

    private String getConstraintsTextFromState(PWSState state) {
        Semantics sem = state.getConstraintsSemantics();
        // Get all fully-specified configurations
        Set<Configuration> configs = sem.getConfigurations();
        // Prepare map from machineId to observed state names
        Map<String, Set<String>> valuesMap = new LinkedHashMap<>();
        for (String mId : assembly.getStateMachines().keySet()) {
            valuesMap.put(mId, new HashSet<>());
        }
        for (Configuration conf : configs) {
            for (BasicStateProposition bsp : conf.getBasicStatePropositions()) {
                Set<String> vs = valuesMap.get(bsp.getMachineId());
                if (vs != null) {
                    vs.add(bsp.getStateName());
                }
            }
        }
        // Build a single line showing only those machines with a single state assignment
        StringBuilder sb = new StringBuilder();
        boolean first = true;
        for (Map.Entry<String, Set<String>> entry : valuesMap.entrySet()) {
            Set<String> vs = entry.getValue();
            if (vs.size() == 1) {
                if (!first) sb.append(", ");
                first = false;
                sb.append(entry.getKey()).append(".").append(vs.iterator().next());
            }
        }
        return sb.toString();
    }

    private Semantics parseConfigurationLine(String line) {
        // Remove surrounding parentheses if present
        if (line.startsWith("(") && line.endsWith(")")) {
            line = line.substring(1, line.length() - 1);
        }
        String[] pairs = line.split(",");
        // Start with universal (top) semantics
        Semantics configSem = Semantics.top(assembly);
        for (String pair : pairs) {
            String p = pair.trim();
            String machine = null, stateName = null;
            // support "machine:state" or "machine.state"
            if (p.contains(":")) {
                String[] parts = p.split(":", 2);
                machine = parts[0].trim();
                stateName = parts[1].trim();
            } else if (p.contains(".")) {
                String[] parts = p.split("\\.", 2);
                machine = parts[0].trim();
                stateName = parts[1].trim();
            }
            if (machine != null && stateName != null) {
                BasicStateProposition bsp = new BasicStateProposition(machine, stateName);
                configSem = configSem.AND(bsp.toSemantics(assembly));
            }
        }
        return configSem;
    }
}