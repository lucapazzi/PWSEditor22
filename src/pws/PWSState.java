package pws;

import assembly.Assembly;
import machinery.State;
import pws.editor.annotation.StateSemanticsAnnotation;
import pws.editor.semantics.ExitZone;
import pws.editor.semantics.Semantics;
import smalgebra.BasicStateProposition;

import java.awt.*;
import java.util.ArrayList;
import java.util.HashSet;

public class PWSState extends State {
    private transient StateSemanticsAnnotation annotation;
    private boolean annotationVisible = false; // Di default nascosta.
    // State semantics
    private Semantics stateSemantics;
    // Constraints semantics.
    private Semantics constraintsSemantics;
    // Reactive semantics.
    private HashSet<ExitZone> reactiveSemantics;
    // Stores the raw constraint text entered by the user
    private String rawConstraintText;

    public PWSState(String name, Point position, Assembly assembly) {
        super(name, position);
        stateSemantics = new Semantics(assembly.getAssemblyId());
        // Initialize new semantics fields to default bottom semantics.
        constraintsSemantics = Semantics.bottom(assembly.getAssemblyId());
        reactiveSemantics = new HashSet<ExitZone>();
    }

    // Getters and setters for constraints semantics.
    public Semantics getConstraintsSemantics() {
        return constraintsSemantics;
    }

    public void setConstraintsSemantics(Semantics constraintsSemantics) {
        this.constraintsSemantics = constraintsSemantics;
        if (annotation != null) {
            annotation.setContent(this); // Updated to use 'this'
            annotation.repaint();
        }
    }

    // Getters and setters for autonomous semantics.
    public HashSet<ExitZone> getReactiveSemantics() {
        return reactiveSemantics;
    }

    public void setReactiveSemantics(HashSet<ExitZone> reactiveSemantics) {
        this.reactiveSemantics = reactiveSemantics;
        if (annotation != null) {
            annotation.setContent(this); // Updated to use 'this'
            annotation.repaint();
        }
    }

    public StateSemanticsAnnotation getAnnotation() {
        return annotation;
    }

    public void setAnnotation(StateSemanticsAnnotation annotation) {
        this.annotation = annotation;
    }

    public boolean isAnnotationVisible() {
        return annotationVisible;
    }

    public void setAnnotationVisible(boolean visible) {
        this.annotationVisible = visible;
        if (annotation != null) {
            annotation.setVisible(visible);
        }
    }

    public Semantics getStateSemantics() {
        return stateSemantics;
    }

    // Metodo per identificare in modo univoco il pseudostato
    public boolean isPseudoState() {
        // Assicurati che il nome del pseudostato sia esattamente "PseudoState"
        return "PseudoState".equals(getName());
    }

    public void setStateSemantics(Semantics stateSemantics) {
        this.stateSemantics = stateSemantics;
        if (annotation != null) {
            annotation.setContent(this); // Updated to use 'this'
            annotation.repaint();
        }
    }

    /** Sets the raw constraint text for this state (compact form). */
    public void setRawConstraintText(String text) {
        this.rawConstraintText = text;
    }

    /** Returns the raw constraint text, or null if none was set. */
    public String getRawConstraintText() {
        return rawConstraintText;
    }
}