package assembly;

import machinery.StateInterface;
import machinery.StateMachine;
import pws.editor.semantics.Configuration;
import pws.editor.semantics.Semantics;
import smalgebra.BasicStateProposition;

import java.util.*;
public class Assembly implements AssemblyInterface {
    private String assemblyId;
    private Map<String, StateMachine> stateMachines;

    public Assembly(String assemblyId) {
        this.assemblyId = assemblyId;
        stateMachines = new LinkedHashMap<>();
    }

    @Override
    public Map<String, StateMachine> getStateMachines() {
        return stateMachines;
    }

    public String getAssemblyId() {
        return assemblyId;
    }


    @Override
    public void addStateMachine(String identifier, StateMachine machine) {
        stateMachines.put(identifier, machine);
    }

    @Override
    public List<AssemblyInterface> getAllConcreteAssemblies() {
        // Implementazione a piacere
        return new ArrayList<>();
    }

    /**
     * Restituisce un elenco completo di azioni generabili.
     * Per ogni state machine m nell'assembly e per ogni evento e in m.getEvents(),
     * crea un'azione con identificatore m ed evento e.
     *
     * Esempio: se l'assembly contiene macchine "t1" e "t2" con trigger {e, f},
     * verrà restituita la lista: [ t1.e, t1.f, t2.e, t2.f ].
     */
    public List<Action> getAllPossibleActions() {
        List<Action> actions = new ArrayList<>();
        for (Map.Entry<String, StateMachine> entry : stateMachines.entrySet()) {
            String machineId = entry.getKey();
            StateMachine machine = entry.getValue();
            // Si assume che machine.getEvents() restituisca un Set o List di String.
            for (String event : machine.getEvents()) {
                actions.add(new Action(machineId, event));
            }
        }
        return actions;
    }

    @Override
    public Semantics calculateInitialStateSemantics() {
        // Generiamo un assemblyId: se l'Assembly ha un identificatore proprio, usalo; altrimenti,
        // qui viene usato un valore costante.
        String assemblyId = this.getAssemblyId();
        Semantics semantics = new Semantics(assemblyId);

        // Per ciascuna state machine, raccogliamo le proposizioni che rappresentano gli stati iniziali.
        List<List<BasicStateProposition>> machineInitialProps = new ArrayList<>();
        for (Map.Entry<String, StateMachine> entry : getStateMachines().entrySet()) {
            String machineId = entry.getKey();
            StateMachine machine = entry.getValue();
            List<BasicStateProposition> initialProps = new ArrayList<>();
            for (StateInterface s : machine.getStates()) {
                if (machine.getInitialStates().contains(s)) {
                    // Creiamo la proposizione iniziale per questa macchina
                    initialProps.add(new BasicStateProposition(machineId, s.getName()));
                }
            }
            // Se per la macchina sono stati trovati stati iniziali, li aggiungiamo al nostro elenco
            if (!initialProps.isEmpty()) {
                machineInitialProps.add(initialProps);
            }
        }

        // Se non sono state trovate proposizioni iniziali in nessuna macchina,
        // restituiamo una Semantics contenente una Configuration "vuota" (che può essere interpretata come true).
        if (machineInitialProps.isEmpty()) {
            semantics.addConfiguration(new Configuration(assemblyId));
            return semantics;
        }

        // Calcoliamo il prodotto cartesiano delle liste di proposizioni iniziali,
        // ottenendo così tutte le possibili configurazioni iniziali.
        List<List<BasicStateProposition>> cartesian = cartesianProduct(machineInitialProps);
        for (List<BasicStateProposition> combination : cartesian) {
            // Costruiamo una Configuration a partire dalla combinazione ordinata delle BasicStateProp.
            // Si sfrutta il metodo fromBasicStatePropositions per garantire l'ordinamento.
            List<BasicStateProposition> props = new ArrayList<>(combination);
            Configuration config = Configuration.fromBasicStatePropositions(assemblyId, props);
            semantics.addConfiguration(config);
        }

        return semantics;
    }



    /**
     * Restituisce la lista delle guardie disponibili come BasicStateProposition.
     * Per ogni state machine (machineId) dell'assembly, per ogni stato,
     * viene creato un BasicStateProposition nella forma "machineId.stateName".
     */
    @Override
    public List<BasicStateProposition> getAssemblyGuards() {
        List<BasicStateProposition> guardList = new ArrayList<>();
        for (Map.Entry<String, StateMachine> entry : getStateMachines().entrySet()) {
            String machineId = entry.getKey();
            StateMachine machine = entry.getValue();
            for (StateInterface s : machine.getStates()) {
                String stateName = s.getName();
                // Skip the pseudostate in guard propositions
                if ("PseudoState".equals(stateName)) {
                    continue;
                }
                guardList.add(new BasicStateProposition(machineId, stateName));
            }
        }
        return guardList;
    }

    /**
     * Restituisce la lista delle azioni disponibili come oggetti Action.
     * Per ogni state machine (machineId) dell'assembly, per ogni evento in machine.getEvents(),
     * viene creato un oggetto Action nella forma "machineId.event".
     */
    @Override
    public List<Action> getAssemblyActions() {
        List<Action> actionList = new ArrayList<>();
        for (Map.Entry<String, StateMachine> entry : getStateMachines().entrySet()) {
            String machineId = entry.getKey();
            StateMachine machine = entry.getValue();
            if (machine.getEvents() != null) {
                for (String event : machine.getEvents()) {
                    actionList.add(new Action(machineId, event));
                }
            }
        }
        return actionList;
    }

    /**
     * Mostra un dialogo per la scelta della guardia e delle azioni.
     * Il dialogo presenta:
     * - Un JComboBox per selezionare una guardia (BasicStateProposition) dalla lista restituita da getAssemblyGuards().
     * - Un JList per selezionare una o più azioni (Action) dalla lista restituita da getAssemblyActions().
     *
     * Restituisce un oggetto GuardActionsPair contenente la guardia scelta e la lista delle azioni selezionate.
     */
//    public GuardActionsPair askForGuardAndActions() {
//        List<BasicStateProposition> guardOptions = getAssemblyGuards();
//        List<Action> actionOptions = getAssemblyActions();
//
//        JPanel panel = new JPanel(new GridBagLayout());
//        GridBagConstraints gbc = new GridBagConstraints();
//        gbc.insets = new Insets(5, 5, 5, 5);
//
//        // Selezione della guardia
//        gbc.gridx = 0;
//        gbc.gridy = 0;
//        panel.add(new JLabel("Seleziona una guardia (m.S):"), gbc);
//        gbc.gridx = 1;
//        JComboBox<BasicStateProposition> guardCombo = new JComboBox<>(guardOptions.toArray(new BasicStateProposition[0]));
//        guardCombo.setPreferredSize(new Dimension(200, 25));
//        panel.add(guardCombo, gbc);
//
//        // Selezione delle azioni (lista multipla)
//        gbc.gridx = 0;
//        gbc.gridy = 1;
//        panel.add(new JLabel("Seleziona azioni (m.e):"), gbc);
//        gbc.gridx = 1;
//        JList<Action> actionList = new JList<>(actionOptions.toArray(new Action[0]));
//        actionList.setSelectionMode(ListSelectionModel.MULTIPLE_INTERVAL_SELECTION);
//        JScrollPane scroll = new JScrollPane(actionList);
//        scroll.setPreferredSize(new Dimension(200, 100));
//        panel.add(scroll, gbc);
//
//        int result = JOptionPane.showConfirmDialog(null, panel, "Seleziona Guardia e Azioni",
//                JOptionPane.OK_CANCEL_OPTION, JOptionPane.PLAIN_MESSAGE);
//        if (result == JOptionPane.OK_OPTION) {
//            BasicStateProposition selectedGuard = (BasicStateProposition) guardCombo.getSelectedItem();
//            List<Action> selectedActions = actionList.getSelectedValuesList();
//            return new GuardActionsPair(selectedGuard, selectedActions);
//        } else {
//            return new GuardActionsPair(null, new ArrayList<>());
//        }
//    }


    /**
     * Generates the universe of fully-specified configurations for the given assemblyId.
     * It retrieves the Assembly instance using a registry (assumed to be available).
     */
    public Set<Configuration> generateUniverse() {
        Set<Configuration> universe = new HashSet<>();
        Map<String, StateMachine> machines = this.getStateMachines();
        Map<String, List<String>> machineStates = new LinkedHashMap<>();
        for (Map.Entry<String, StateMachine> entry : machines.entrySet()) {
            String machineId = entry.getKey();
            StateMachine machine = entry.getValue();
            List<String> stateNames = new ArrayList<>();
            for (StateInterface s : machine.getStates()) {
                String stateName = s.getName();
                if ( !stateName.equals("PseudoState") ) {
                    stateNames.add(stateName);
                }
            }
            machineStates.put(machineId, stateNames);
        }
// Build a list of lists of BasicStateProposition for each machine.
        List<List<BasicStateProposition>> listOfPropLists = new ArrayList<>();
        for (Map.Entry<String, List<String>> entry : machineStates.entrySet()) {
            String machineId = entry.getKey();
            List<String> states = entry.getValue();
            // If a machine has no states, skip it.
            if (states.isEmpty()) {
                continue;
            }
            List<BasicStateProposition> propList = new ArrayList<>();
            for (String state : states) {
                propList.add(new BasicStateProposition(machineId, state));
            }
            listOfPropLists.add(propList);
        }
        List<List<BasicStateProposition>> cartesian = cartesianProduct(listOfPropLists);
        for (List<BasicStateProposition> combination : cartesian) {
            Configuration config = Configuration.fromBasicStatePropositions(this.assemblyId, combination);
            universe.add(config);
        }
        return universe;
    }

    private static List<List<BasicStateProposition>> cartesianProduct(List<List<BasicStateProposition>> lists) {
        List<List<BasicStateProposition>> result = new ArrayList<>();
        if (lists.isEmpty()) {
            result.add(new ArrayList<>());
            return result;
        }
        cartesianProductHelper(lists, result, 0, new ArrayList<>());
        return result;
    }

    private static void cartesianProductHelper(List<List<BasicStateProposition>> lists,
                                               List<List<BasicStateProposition>> result,
                                               int depth,
                                               List<BasicStateProposition> current) {
        if (depth == lists.size()) {
            result.add(new ArrayList<>(current));
            return;
        }
        for (BasicStateProposition element : lists.get(depth)) {
            current.add(element);
            cartesianProductHelper(lists, result, depth + 1, current);
            current.remove(current.size() - 1);
        }
    }

}