package pws.editor;

import assembly.Assembly;
import assembly.AssemblyInterface;
import assembly.GuardActionsPair;
import editor.StateMachineEditor;
import machinery.StateMachine;
import pws.PWSState;
import pws.PWSStateMachine;
import serializer.BinaryModelSerializer;
import utility.SVGExporter;
import java.util.logging.Logger;
import java.util.logging.Handler;
import java.util.logging.LogRecord;
import java.util.logging.SimpleFormatter;

import javax.swing.*;
import javax.swing.InputMap;
import javax.swing.ActionMap;
import javax.swing.KeyStroke;
import javax.swing.AbstractAction;
import java.awt.event.ActionEvent;
import java.awt.*;
import java.io.*;

import pws.editor.PWSStateMachineEditor;
import pws.editor.PWSStateMachinePanel;
import javax.swing.JCheckBoxMenuItem;

public class PWSEditor extends JFrame {

    // private Assembly assembly;
    private PWSStateMachine pwsStateMachine;
    private StateMachineEditor baseEditor;  // Editor for the current state machine
    private PWSPanel assemblyPanel;         // Panel to manage the Assembly
    private JTabbedPane tabbedPane;         // Panel to switch between baseEditor and assemblyPanel

    // The main PWSEditor window uses a fixed title, e.g. "PWSEditor"
    public PWSEditor(PWSStateMachine machine) {
        super("PWSEditor");
        // Use the specialized PWSStateMachine:
        if (machine instanceof PWSStateMachine) {
            this.pwsStateMachine = ((PWSStateMachine) machine).clone();
        } else {
            this.pwsStateMachine = new PWSStateMachine(machine.getName());
        }
        initComponents();
    }

    private void initComponents() {
        setJMenuBar(createMenuBar());

        // Create a specialized editor using PWSStateMachineEditor and a custom title (here "PWSMachine").
        baseEditor = new PWSStateMachineEditor(pwsStateMachine, "PWSMachine");
        JPanel editorPanel = new JPanel(new BorderLayout());
        editorPanel.add(baseEditor.getContentPane(), BorderLayout.CENTER);

        assemblyPanel = new PWSPanel(pwsStateMachine.getAssembly());

        tabbedPane = new JTabbedPane();
        tabbedPane.addTab("Editor", editorPanel);
        tabbedPane.addTab("Assembly", assemblyPanel);
        /* ---- Disable default LEFT / RIGHT navigation of JTabbedPane ---- */
        InputMap imDefault = tabbedPane.getInputMap(JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);
        imDefault.put(KeyStroke.getKeyStroke("LEFT"),  "none");
        imDefault.put(KeyStroke.getKeyStroke("RIGHT"), "none");

        getContentPane().add(tabbedPane, BorderLayout.CENTER);

        /* ---------- Arrow‑key tab switching ---------- */
        InputMap im = tabbedPane.getInputMap(JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);
        ActionMap am = tabbedPane.getActionMap();

        im.put(KeyStroke.getKeyStroke("alt LEFT"),  "prevTab");
        im.put(KeyStroke.getKeyStroke("alt RIGHT"), "nextTab");

        am.put("prevTab", new AbstractAction() {
            @Override public void actionPerformed(ActionEvent e) {
                int idx = tabbedPane.getSelectedIndex();
                if (idx > 0) tabbedPane.setSelectedIndex(idx - 1);
            }
        });
        am.put("nextTab", new AbstractAction() {
            @Override public void actionPerformed(ActionEvent e) {
                int idx = tabbedPane.getSelectedIndex();
                if (idx < tabbedPane.getTabCount() - 1) tabbedPane.setSelectedIndex(idx + 1);
            }
        });
    }

    private JMenuBar createMenuBar() {
        JMenuBar menuBar = new JMenuBar();

        // File menu
        JMenu fileMenu = new JMenu("File");

//        // Save model item (existing)
//        JMenuItem saveItem = new JMenuItem("Salva");
//        saveItem.addActionListener(e -> {
//            JFileChooser fileChooser = new JFileChooser();
//            int option = fileChooser.showSaveDialog(PWSEditor.this);
//            if (option == JFileChooser.APPROVE_OPTION) {
//                String filename = fileChooser.getSelectedFile().getAbsolutePath();
//                try {
//                    BinaryModelSerializer.saveModel(pwsStateMachine, filename);
//                    JOptionPane.showMessageDialog(PWSEditor.this, "Modello salvato correttamente.");
//                } catch (IOException ex) {
//                    ex.printStackTrace();
//                    JOptionPane.showMessageDialog(PWSEditor.this, "Errore durante il salvataggio: " + ex.getMessage());
//                }
//            }
//        });
//        fileMenu.add(saveItem);
//
//        // Load model item (existing)
//        JMenuItem loadItem = new JMenuItem("Carica");
//        loadItem.addActionListener(e -> {
//            JFileChooser fileChooser = new JFileChooser();
//            int option = fileChooser.showOpenDialog(PWSEditor.this);
//            if (option == JFileChooser.APPROVE_OPTION) {
//                String filename = fileChooser.getSelectedFile().getAbsolutePath();
//                try {
//                    Object loadedModel = BinaryModelSerializer.loadModel(filename);
//                    if (loadedModel instanceof PWSStateMachine) {
//                        pwsStateMachine = (PWSStateMachine) loadedModel;
//                        baseEditor.dispose(); // Close the previous editor if needed
//                        baseEditor = new PWSStateMachineEditor(pwsStateMachine, "PWSMachine");
//
//                        JPanel editorPanel = new JPanel(new BorderLayout());
//                        editorPanel.add(baseEditor.getContentPane(), BorderLayout.CENTER);
//                        tabbedPane.setComponentAt(0, editorPanel);
//
//                        assemblyPanel = new PWSPanel(pwsStateMachine.getAssembly());
//                        tabbedPane.setComponentAt(1, assemblyPanel);
//
//                        revalidate();
//                        repaint();
//                        JOptionPane.showMessageDialog(PWSEditor.this, "Modello caricato correttamente.");
//                    } else {
//                        JOptionPane.showMessageDialog(PWSEditor.this, "Il file selezionato non contiene un modello valido.");
//                    }
//                } catch (IOException | ClassNotFoundException ex) {
//                    ex.printStackTrace();
//                    JOptionPane.showMessageDialog(PWSEditor.this, "Errore durante il caricamento: " + ex.getMessage());
//                }
//            }
//        });
//        fileMenu.add(loadItem);

        // --- New Composite Save/Load for Model + Layout in a Single File ---

        // Save All (model and layout)
        JMenuItem saveAllItem = new JMenuItem("Salva Tutto");
        saveAllItem.addActionListener(e -> {
            JFileChooser fileChooser = new JFileChooser();
            int option = fileChooser.showSaveDialog(PWSEditor.this);
            if (option == JFileChooser.APPROVE_OPTION) {
                File file = fileChooser.getSelectedFile();
                try (ObjectOutputStream oos = new ObjectOutputStream(new FileOutputStream(file))) {
                    // Write the model first
                    oos.writeObject(pwsStateMachine);
                    // Write the layout data from the state machine panel.
                    // Note: Ensure that PWSStateMachinePanel has the method saveAnnotationsToStream.
                    ((PWSStateMachinePanel) baseEditor.getStateMachinePanel()).saveAnnotationsToStream(oos);
                    oos.flush();
                    JOptionPane.showMessageDialog(PWSEditor.this, "Modello e layout salvati correttamente.");
                } catch (IOException ex) {
                    ex.printStackTrace();
                    JOptionPane.showMessageDialog(PWSEditor.this, "Errore durante il salvataggio: " + ex.getMessage());
                }
            }
        });
        fileMenu.add(saveAllItem);

        // Load All (model and layout)
        JMenuItem loadAllItem = new JMenuItem("Carica Tutto");
        loadAllItem.addActionListener(e -> {
            JFileChooser fileChooser = new JFileChooser();
            int option = fileChooser.showOpenDialog(PWSEditor.this);
            if (option == JFileChooser.APPROVE_OPTION) {
                File file = fileChooser.getSelectedFile();
                try (ObjectInputStream ois = new ObjectInputStream(new FileInputStream(file))) {
                    Object obj = ois.readObject();
                    if (obj instanceof PWSStateMachine) {
                        pwsStateMachine = (PWSStateMachine) obj;
                        baseEditor.dispose();
                        baseEditor = new PWSStateMachineEditor(pwsStateMachine, "PWSMachine");
                        JPanel editorPanel = new JPanel(new BorderLayout());
                        editorPanel.add(baseEditor.getContentPane(), BorderLayout.CENTER);
                        tabbedPane.setComponentAt(0, editorPanel);
                        assemblyPanel = new PWSPanel(pwsStateMachine.getAssembly());
                        tabbedPane.setComponentAt(1, assemblyPanel);
                        // Now load the layout data.
                        ((PWSStateMachinePanel) baseEditor.getStateMachinePanel()).loadAnnotationsFromStream(ois);
                        revalidate();
                        repaint();
                        JOptionPane.showMessageDialog(PWSEditor.this, "Modello e layout caricati correttamente.");
                    } else {
                        JOptionPane.showMessageDialog(PWSEditor.this, "Il file selezionato non contiene dati validi.");
                    }
                } catch (IOException | ClassNotFoundException ex) {
                    ex.printStackTrace();
                    JOptionPane.showMessageDialog(PWSEditor.this, "Errore durante il caricamento: " + ex.getMessage());
                }
            }
        });
        fileMenu.add(loadAllItem);

        // New: Export as SVG menu item.
        JMenuItem exportSVGItem = new JMenuItem("Esporta come SVG");
        exportSVGItem.addActionListener(e -> {
            // Assume we want to export the "Editor" tab (tab index 0)
            Component comp = tabbedPane.getComponentAt(0);
            if (comp instanceof JPanel) {
                JPanel editorPanel = (JPanel) comp;
                JFileChooser fileChooser = new JFileChooser();
                fileChooser.setFileFilter(new javax.swing.filechooser.FileNameExtensionFilter("File SVG", "svg"));
                int option = fileChooser.showSaveDialog(PWSEditor.this);
                if (option == JFileChooser.APPROVE_OPTION) {
                    File file = fileChooser.getSelectedFile();
                    if (!file.getName().toLowerCase().endsWith(".svg")) {
                        file = new File(file.getAbsolutePath() + ".svg");
                    }
                    editorPanel.revalidate();
                    editorPanel.repaint();
                    // Call the SVGExporter.exportPanelToSVGFile method to save the SVG file.
                    SVGExporter.exportPanelToSVGFile(editorPanel, file);
                    JOptionPane.showMessageDialog(PWSEditor.this, "File SVG salvato correttamente.");
                }
            }
        });
        fileMenu.add(exportSVGItem);

        // Exit item
        JMenuItem exitItem = new JMenuItem("Esci");
        exitItem.addActionListener(e -> System.exit(0));
        fileMenu.addSeparator();
        fileMenu.add(exitItem);

        menuBar.add(fileMenu);

        // --- Edit Menu (existing items) ---
        JMenu editMenu = new JMenu("Modifica");

        JMenuItem addStateItem = new JMenuItem("Aggiungi Stato");
        addStateItem.addActionListener(e -> {
            String name = JOptionPane.showInputDialog(PWSEditor.this, "Inserisci il nome dello stato:");
            if (name != null && !name.trim().isEmpty()) {
                pwsStateMachine.addState(new PWSState(
                        name,
                        new Point(50, 50),
                        pwsStateMachine.getAssembly()
                ));
                baseEditor.getStateMachinePanel().repaint();
            }
        });
        editMenu.add(addStateItem);

        JMenuItem addInitialTransitionItem = new JMenuItem("Aggiungi transizione iniziale");
        addInitialTransitionItem.addActionListener(e ->
                baseEditor.getStateMachinePanel().enableInitialTransitionMode());
        editMenu.add(addInitialTransitionItem);

        editMenu.addSeparator();

//        JMenuItem addTransitionItem = new JMenuItem("Aggiungi Transizione");
//        addTransitionItem.addActionListener(e -> {
//            String sourceName = JOptionPane.showInputDialog(PWSEditor.this, "Inserisci il nome dello stato sorgente:");
//            String targetName = JOptionPane.showInputDialog(PWSEditor.this, "Inserisci il nome dello stato target:");
//            if (sourceName != null && targetName != null) {
//                machinery.StateInterface source = findStateByName(sourceName);
//                machinery.StateInterface target = findStateByName(targetName);
//                if (source != null && target != null) {
//                    String trigger = JOptionPane.showInputDialog(PWSEditor.this, "Inserisci il trigger event (lascia vuoto per interna):");
//                    boolean autonomous = (trigger == null || trigger.trim().isEmpty());
//                    pws.PWSTransition newTransition = new pws.PWSTransition(source, target, autonomous, trigger);
//                    GuardActionsPair gap = ((Assembly) pwsStateMachine.getAssembly()).askForGuardAndActions();
//                    if (gap != null) {
//                        newTransition.setGuardProposition(gap.getGuard());
//                        for (assembly.Action act : gap.getActions()) {
//                            newTransition.addAction(act);
//                        }
//                    }
//                    pwsStateMachine.addTransition(newTransition);
//                    baseEditor.getStateMachinePanel().repaint();
//                } else {
//                    JOptionPane.showMessageDialog(PWSEditor.this, "Stato sorgente o target non trovato.");
//                }
//            }
//        });
//        editMenu.add(addTransitionItem);

        JMenuItem linkModeItem = new JMenuItem("Crea transizione (modalità collega)");
        linkModeItem.addActionListener(e -> baseEditor.getStateMachinePanel().enableLinkMode());
        editMenu.add(linkModeItem);

        JCheckBoxMenuItem editModeItem = new JCheckBoxMenuItem("Modalità modifica", true);
        editModeItem.addActionListener(e -> baseEditor.getStateMachinePanel().setShowControlHandles(editModeItem.isSelected()));
        editMenu.add(editModeItem);

        menuBar.add(editMenu);

        // --- View menu: toggle state annotations ---
        JMenu viewMenu = new JMenu("View");
        JCheckBoxMenuItem showStateAnn = new JCheckBoxMenuItem("Show State Annotations", false);
        showStateAnn.addActionListener(e -> {
            boolean show = showStateAnn.isSelected();
            // Retrieve the PWSStateMachinePanel and toggle annotations
            PWSStateMachinePanel panel =
                (PWSStateMachinePanel)((PWSStateMachineEditor) baseEditor).getStateMachinePanel();
            panel.setShowStateAnnotations(show);
            panel.repaint();
        });
        viewMenu.add(showStateAnn);
        menuBar.add(viewMenu);
        return menuBar;
    }

    private machinery.StateInterface findStateByName(String name) {
        for (machinery.StateInterface s : pwsStateMachine.getStates()) {
            if (s.getName().equalsIgnoreCase(name)) {
                return s;
            }
        }
        return null;
    }

    public static void main(String[] args) {
        // Simplify logs: only show the message text
        System.setProperty("java.util.logging.SimpleFormatter.format", "%5$s%n");
        Logger rootLogger = Logger.getLogger("");
        for (Handler handler : rootLogger.getHandlers()) {
            handler.setFormatter(new SimpleFormatter() {
                @Override
                public String format(LogRecord record) {
                    return record.getMessage() + System.lineSeparator();
                }
            });
        }
        PWSStateMachine pwsStateMachine = new PWSStateMachine("Whole");

        // Here I create a state machine for adding to the assembly with id "m1"
        StateMachine stateMachine1 = new StateMachine("M1");
        pwsStateMachine.getAssembly().addStateMachine("m1", stateMachine1);
        SwingUtilities.invokeLater(() -> {
            PWSEditor editor = new PWSEditor(pwsStateMachine);
            editor.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
            editor.setSize(1000, 600);
            editor.setLocationRelativeTo(null);
            editor.setVisible(true);
        });
    }
}