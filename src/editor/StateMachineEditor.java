package editor;

import assembly.Assembly;
import machinery.*;
import pws.PWSStateMachine;
import utility.SVGExporter;

import javax.swing.*;
import java.awt.*;
import java.io.*;

public class StateMachineEditor extends JFrame {

    protected StateMachine stateMachine;
    protected StateMachinePanel statePanel;
    protected Assembly assembly;

    // Costruttore predefinito (usa titolo "StateMachine Editor")
    public StateMachineEditor(StateMachine stateMachine, String title) {
        super(title);
        this.stateMachine = stateMachine;
        initComponents();
    }

    // Nuovo costruttore che permette di specificare il titolo (ad es. "id : M")
    public StateMachineEditor(StateMachine stateMachine, Assembly assembly, String title) {
        super(title);
        this.stateMachine = stateMachine;
        this.assembly = assembly;
        initComponents();
    }

    private void initComponents() {
        statePanel = new StateMachinePanel(stateMachine);
        getContentPane().add(statePanel, BorderLayout.CENTER);
        setJMenuBar(createMenuBar());
        setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        setSize(800, 600);
        setLocationRelativeTo(null);
    }

    protected JMenuBar createMenuBar() {
        JMenuBar menuBar = new JMenuBar();

        // Menu File
        JMenu fileMenu = new JMenu("File");
// --- Existing File Menu Items above ---

// Load Single Machine
        JMenuItem loadMachineItem = new JMenuItem("Carica Macchina Singola");
        loadMachineItem.addActionListener(e -> {
            JFileChooser fileChooser = new JFileChooser();
            fileChooser.setFileFilter(new javax.swing.filechooser.FileNameExtensionFilter("File Macchina (sm)", "sm"));
            int option = fileChooser.showOpenDialog(StateMachineEditor.this);
            if (option == JFileChooser.APPROVE_OPTION) {
                File file = fileChooser.getSelectedFile();
                try (ObjectInputStream ois = new ObjectInputStream(new FileInputStream(file))) {
                    // Assume the file contains a serialized StateMachine object.
                    StateMachine loadedMachine = (StateMachine) ois.readObject();

                    // Create a deep clone using your new clone() method.
                    StateMachine clonedMachine = loadedMachine.clone();

                    // Option B: Update the current state machine with the clone's data.
                    stateMachine.setStates(clonedMachine.getStates());
                    stateMachine.setTransitions(clonedMachine.getTransitions());
                    stateMachine.setEvents(clonedMachine.getEvents());
                    stateMachine.setName(clonedMachine.getName());

                    // If pseudoState is accessible via a getter, update it as well:
                    // (Alternatively, ensure that your clone() method already updates the pseudoState field.)
                    stateMachine.setPseudoState(clonedMachine.getPseudoState());
                    // Or if pseudoState is a protected field you can do:
                    // stateMachine.pseudoState = clonedMachine.getPseudoState();

                    JOptionPane.showMessageDialog(StateMachineEditor.this,
                            "Macchina caricata correttamente: " + clonedMachine.getName());
                    statePanel.repaint();
                } catch (Exception ex) {
                    ex.printStackTrace();
                    JOptionPane.showMessageDialog(StateMachineEditor.this,
                            "Errore nel caricamento della macchina: " + ex.getMessage());
                }
            }
        });

// Save Single Machine
        JMenuItem saveMachineItem = new JMenuItem("Salva Macchina Singola");
        saveMachineItem.addActionListener(e -> {
            JFileChooser fileChooser = new JFileChooser();
            fileChooser.setFileFilter(new javax.swing.filechooser.FileNameExtensionFilter("File Macchina (sm)", "sm"));
            int option = fileChooser.showSaveDialog(StateMachineEditor.this);
            if (option == JFileChooser.APPROVE_OPTION) {
                File file = fileChooser.getSelectedFile();
                if (!file.getName().toLowerCase().endsWith(".sm")) {
                    file = new File(file.getAbsolutePath() + ".sm");
                }
                try (ObjectOutputStream oos = new ObjectOutputStream(new FileOutputStream(file))) {
                    oos.writeObject(stateMachine);
                    oos.flush();
                    JOptionPane.showMessageDialog(StateMachineEditor.this,
                            "Macchina salvata: " + stateMachine.getName());
                } catch (Exception ex) {
                    ex.printStackTrace();
                    JOptionPane.showMessageDialog(StateMachineEditor.this,
                            "Errore nel salvataggio della macchina: " + ex.getMessage());
                }
            }
        });
        fileMenu.add(saveMachineItem);

// --- Then the existing Exit menu item follows ---

        JMenuItem exitItem = new JMenuItem("Esci");
        exitItem.addActionListener(e -> System.exit(0));
        fileMenu.add(loadMachineItem);
        fileMenu.add(saveMachineItem);
        fileMenu.addSeparator();
        JMenuItem exportSVGItem = new JMenuItem("Esporta come SVG");
        exportSVGItem.addActionListener(e -> {
            // Export the statePanel (graph content) as SVG.
            JFileChooser fileChooser = new JFileChooser();
            fileChooser.setFileFilter(new javax.swing.filechooser.FileNameExtensionFilter("File SVG", "svg"));
            int option = fileChooser.showSaveDialog(StateMachineEditor.this);
            if (option == JFileChooser.APPROVE_OPTION) {
                File file = fileChooser.getSelectedFile();
                if (!file.getName().toLowerCase().endsWith(".svg")) {
                    file = new File(file.getAbsolutePath() + ".svg");
                }
                statePanel.revalidate();
                statePanel.repaint();
                SVGExporter.exportPanelToSVGFile(statePanel, file);
                JOptionPane.showMessageDialog(StateMachineEditor.this, "File SVG salvato correttamente.");
            }
        });
        fileMenu.add(exportSVGItem);
        fileMenu.add(exitItem);
        menuBar.add(fileMenu);

        // Menu Modifica
        JMenu editMenu = new JMenu("Modifica");

// 1. Aggiungi Stato
        JMenuItem addStateItem = new JMenuItem("Aggiungi Stato");
        addStateItem.addActionListener(e -> {
            String name = JOptionPane.showInputDialog(this, "Inserisci il nome dello stato:");
            if (name != null && !name.trim().isEmpty()) {
                stateMachine.addState(new State(name, new Point(50, 50)));
                statePanel.repaint();
            }
        });
        editMenu.add(addStateItem);

// 2. Aggiungi transizione iniziale
        JMenuItem addInitialTransitionItem = new JMenuItem("Aggiungi transizione iniziale");
        addInitialTransitionItem.addActionListener(e -> statePanel.enableInitialTransitionMode());
        editMenu.add(addInitialTransitionItem);

        editMenu.addSeparator();

// 3. Aggiungi transizione
//        JMenuItem addTransitionItem = new JMenuItem("Aggiungi Transizione");
//        addTransitionItem.addActionListener(e -> {
//            String sourceName = JOptionPane.showInputDialog(this, "Inserisci il nome dello stato sorgente:");
//            String targetName = JOptionPane.showInputDialog(this, "Inserisci il nome dello stato target:");
//            if (sourceName != null && targetName != null) {
//                StateInterface source = findStateByName(sourceName);
//                StateInterface target = findStateByName(targetName);
//                if (source != null && target != null) {
//                    String trigger = JOptionPane.showInputDialog(this, "Inserisci il trigger event (lascia vuoto per autonoma):");
//                    boolean autonomous = (trigger == null || trigger.trim().isEmpty());
//                    TransitionInterface newTransition = new Transition(source, target, autonomous, trigger);
//                    stateMachine.addTransition(newTransition);
//                    statePanel.repaint();
//                } else {
//                    JOptionPane.showMessageDialog(this, "Stato sorgente o target non trovato.");
//                }
//            }
//        });
//        editMenu.add(addTransitionItem);

// 4. Crea transizione (modalità collega)
        JMenuItem linkModeItem = new JMenuItem("Crea transizione (modalità collega)");
        linkModeItem.addActionListener(e -> statePanel.enableLinkMode());
        editMenu.add(linkModeItem);

// 5. Modalità modifica (checkbox)
        JCheckBoxMenuItem editModeItem = new JCheckBoxMenuItem("Modalità modifica", true);
        editModeItem.addActionListener(e -> statePanel.setShowControlHandles(editModeItem.isSelected()));
        editMenu.add(editModeItem);

        menuBar.add(editMenu);
        return menuBar;
    }

    private StateInterface findStateByName(String name) {
        for (StateInterface s : stateMachine.getStates()) {
            if (s.getName().equalsIgnoreCase(name)) {
                return s;
            }
        }
        return null;
    }

    public StateMachinePanel    getStateMachinePanel() {
        return statePanel;
    }

    public void setStateMachine(PWSStateMachine stateMachine) {
        this.stateMachine = stateMachine;
    }
}