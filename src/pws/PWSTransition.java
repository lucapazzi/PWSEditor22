package pws;

import assembly.Action;
import assembly.ActionList;
import assembly.Assembly;
import machinery.StateInterface;
import machinery.Transition;
import pws.editor.annotation.ActionAnnotation;
import pws.editor.annotation.GuardAnnotation;
import pws.editor.annotation.TransitionSemanticsAnnotation;
import pws.editor.semantics.Semantics;
import smalgebra.SMProposition;
import smalgebra.TrueProposition;

import java.io.Serializable;

public class PWSTransition extends Transition implements Serializable {
    // Nuovi campi semantici
    private Assembly assembly;
    private SMProposition guardProposition;
    private ActionList actionList;  // o List<Action>
    private Semantics transitionSemantics;

    // Componenti per annotazioni interattive (utilizzeremo le nuove sottoclassi)
    private transient GuardAnnotation guardAnnotation;
    private transient ActionAnnotation actionAnnotation;
    private transient TransitionSemanticsAnnotation semanticsAnnotation;

    public PWSTransition(Assembly assembly) {
        super();
        this.assembly = assembly;
        guardProposition = new TrueProposition();
        actionList = new ActionList();
        transitionSemantics = Semantics.bottom(assembly.getAssemblyId());
    }

    public PWSTransition(StateInterface source, StateInterface target, boolean autonomous, String triggerEvent, Assembly assembly) {
        super(source, target, autonomous, triggerEvent);
        this.assembly = assembly;
        guardProposition = new TrueProposition();
        actionList = new ActionList();
        transitionSemantics = Semantics.bottom(assembly.getAssemblyId());
    }

    public PWSTransition(StateInterface source, StateInterface target, boolean autonomous, Assembly assembly) {
        super(source, target, autonomous);
        this.assembly = assembly;
        guardProposition = new TrueProposition();
        actionList = new ActionList();
        transitionSemantics = Semantics.bottom(assembly.getAssemblyId());;
    }

    public SMProposition getGuardProposition() {
        return guardProposition;
    }

    public void setGuardProposition(SMProposition guardProposition) {
        this.guardProposition = guardProposition;
    }

    public ActionList getActionList() {
        return actionList;
    }

    public void addAction(Action action) {
        actionList.add(action);
    }

    public void setActionList(ActionList actionList) {
        this.actionList = actionList;
    }

    public Semantics getTransitionSemantics() {
        return transitionSemantics;
    }

    public void setTransitionSemantics(Semantics transitionSemantics) {
        this.transitionSemantics = transitionSemantics;
        if (semanticsAnnotation != null) {
            semanticsAnnotation.setContent(transitionSemantics);
            semanticsAnnotation.repaint();
        }
    }

    public GuardAnnotation getGuardAnnotation() {
        return guardAnnotation;
    }

    public void setGuardAnnotation(GuardAnnotation guardAnnotation) {
        this.guardAnnotation = guardAnnotation;
    }

    public ActionAnnotation getActionAnnotation() {
        return actionAnnotation;
    }

    public void setActionAnnotation(ActionAnnotation actionAnnotation) {
        this.actionAnnotation = actionAnnotation;
    }

    public TransitionSemanticsAnnotation getSemanticsAnnotation() {
        return semanticsAnnotation;
    }

    public void setSemanticsAnnotation(TransitionSemanticsAnnotation semanticsAnnotation) {
        this.semanticsAnnotation = semanticsAnnotation;
    }
}