package utility;

import pws.editor.semantics.Configuration;
import pws.editor.semantics.Semantics;
import smalgebra.AndProposition;
import smalgebra.BasicStateProposition;
import smalgebra.OrProposition;
import smalgebra.SMProposition;

import java.util.*;

/**
 * La classe ConfigurationExtractor trasforma una SMProposition (formula logica)
 * in un insieme di configurazioni possibili.
 *
 * Ogni configurazione è rappresentata come una mappa (Map<String, String>)
 * che associa a ciascuna macchina il nome dello stato in cui essa si trova.
 *
 * L'algoritmo prevede:
 *   1. Conversione della formula in forma DNF (disgiunzione di congiunzioni) tramite il metodo toDNF().
 *   2. Appiattimento della disgiunzione in una lista di termini.
 *   3. Per ciascun termine (cioè, ciascun prodotto) vengono estratti i literali.
 *      Se per una macchina compaiono due condizioni contrastanti, il termine viene scartato.
 *   4. L'insieme dei termini "validi" viene restituito come insieme di configurazioni.
 */
public class ConfigurationExtractor {

//    public static Semantics ConvertToSemantics(SMProposition proposition) {
//        // Convertiamo la formula in DNF (forma disgiuntiva di congiunzioni)
//        SMProposition dnf = proposition.toDNF();
//        // Appiattiamo la disgiunzione: se la DNF è una OR, otteniamo tutti i termini
//        List<SMProposition> terms = flattenOr(dnf);
//        Set<Configuration> configSet = new LinkedHashSet<>();
//
//        // Per ciascun termine, estraiamo i literali e costruiamo la configurazione
//        for (SMProposition term : terms) {
//            Map<String, String> configMapping = new HashMap<>();
//            boolean valid = true;
//            // Se il termine è una congiunzione, lo appiattiamo in una lista di literali;
//            // altrimenti, consideriamo il termine stesso come letterale
//            List<SMProposition> literals = flattenAnd(term);
//            for (SMProposition lit : literals) {
//                // Assumiamo che ogni letterale sia una BasicStateProposition
//                if (lit instanceof BasicStateProposition) {
//                    BasicStateProposition bsp = (BasicStateProposition) lit;
//                    String machineId = bsp.getMachineId();
//                    String stateName = bsp.getStateName();
//                    // Se per la stessa macchina sono presenti valori diversi, il termine è incoerente
//                    if (configMapping.containsKey(machineId)) {
//                        if (!configMapping.get(machineId).equals(stateName)) {
//                            valid = false;
//                            break;
//                        }
//                    } else {
//                        configMapping.put(machineId, stateName);
//                    }
//                } else {
//                    valid = false;
//                    break;
//                }
//            }
//            if (valid) {
//                configSet.add(new Configuration(configMapping));
//            }
//        }
//        return new Semantics(configSet);
//    }

    /**
     * Appiattisce una formula OR in una lista di termini.
     * Se l'espressione è una OR, restituisce ricorsivamente tutti i suoi componenti;
     * altrimenti, restituisce una lista contenente l'espressione stessa.
     */
    private static List<SMProposition> flattenOr(SMProposition expr) {
        List<SMProposition> result = new ArrayList<>();
        if (expr instanceof OrProposition) {
            OrProposition op = (OrProposition) expr;
            result.addAll(flattenOr(op.getLeft()));
            result.addAll(flattenOr(op.getRight()));
        } else {
            result.add(expr);
        }
        return result;
    }

    /**
     * Appiattisce una formula AND in una lista di literali.
     * Se l'espressione è una AND, restituisce ricorsivamente tutti i suoi componenti;
     * altrimenti, restituisce una lista contenente l'espressione stessa.
     */
    private static List<SMProposition> flattenAnd(SMProposition expr) {
        List<SMProposition> result = new ArrayList<>();
        if (expr instanceof AndProposition) {
            AndProposition ap = (AndProposition) expr;
            result.addAll(flattenAnd(ap.getLeft()));
            result.addAll(flattenAnd(ap.getRight()));
        } else {
            result.add(expr);
        }
        return result;
    }}