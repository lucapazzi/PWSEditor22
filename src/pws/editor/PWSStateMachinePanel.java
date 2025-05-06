package pws.editor;

import assembly.ActionList;
import assembly.Assembly;
import assembly.AssemblyInterface;
import editor.StateMachinePanel;
import machinery.StateInterface;
import machinery.Transition;
import machinery.TransitionInterface;
import pws.PWSState;
import pws.PWSStateMachine;
import pws.PWSTransition;
import pws.editor.annotation.ActionAnnotation;
import pws.editor.annotation.GuardAnnotation;
import pws.editor.annotation.StateSemanticsAnnotation;
import pws.editor.annotation.TransitionSemanticsAnnotation;
import pws.editor.semantics.Semantics;
import smalgebra.SMProposition;

import javax.swing.*;
import java.awt.*;
import java.awt.event.MouseEvent;
import java.awt.font.TextAttribute;
import java.awt.geom.Point2D;
import java.awt.geom.QuadCurve2D;
import java.text.AttributedString;
import java.util.Iterator;
import java.util.List;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.EOFException;
import java.io.IOException;

// ... rest of your imports ...

public class PWSStateMachinePanel extends StateMachinePanel {

    public PWSStateMachinePanel(PWSStateMachine stateMachine) {
        super(stateMachine);
        setLayout(null);
        // Enable keyboard focus so arrow keys translate the whole diagram
        setFocusable(true);
        requestFocusInWindow();
        // Mouse listeners are inherited from StateMachinePanel.
    }

    /** Allow annotations to find the underlying state machine. */
    public PWSStateMachine getStateMachine() {
        return (PWSStateMachine) stateMachine;
    }

    @Override
    protected void paintComponent(Graphics g) {
        super.paintComponent(g);
        drawStateAnnotations(g);
        drawTransitions(g);
    }

    // -------------------- DRAWING METHODS --------------------

    /**
     * Draw dotted lines connecting each state to its annotation (if visible).
     */
    private void drawStateAnnotations(Graphics g) {
        List<StateInterface> states = stateMachine.getStates();
        for (StateInterface s : states) {
            if (s instanceof PWSState) {
                PWSState pwsState = (PWSState) s;
                if (pwsState.isAnnotationVisible() && pwsState.getAnnotation() != null) {
                    Point statePos = ((machinery.State) pwsState).getPosition();
                    int stateDiam = pwsState.getName().equals("PseudoState") ? PSEUDO_DIAMETER : DIAMETER;
                    int centerX = statePos.x + stateDiam / 2;
                    int centerY = statePos.y + stateDiam / 2;
                    Rectangle annotBounds = pwsState.getAnnotation().getBounds();
                    int annotCenterX = annotBounds.x + annotBounds.width / 2;
                    int annotCenterY = annotBounds.y + annotBounds.height / 2;
                    Graphics2D g2d = (Graphics2D) g;
                    Stroke oldStroke = g2d.getStroke();
                    float[] dashPattern = {2f, 4f};
                    g2d.setStroke(new BasicStroke(
                        1.0f,
                        BasicStroke.CAP_ROUND,
                        BasicStroke.JOIN_ROUND,
                        1.0f,
                        dashPattern,
                        0.0f
                    ));
                    g2d.setColor(new Color(150, 150, 150));  // darker grey for better visibility
                    g2d.drawLine(centerX, centerY, annotCenterX, annotCenterY);
                    g2d.setStroke(oldStroke);
                }
            }
        }
    }

    /**
     * Draws all transitions.
     */
    protected void drawTransitions(Graphics g) {
        Graphics2D g2d = (Graphics2D) g;
        g2d.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
        List<TransitionInterface> transitions = stateMachine.getTransitions();
        for (TransitionInterface t : transitions) {
            drawSingleTransition(g2d, t);
        }
    }

    /**
     * Draw a single transition, including its curve, arrowhead and annotations.
     */
    protected void drawSingleTransition(Graphics2D g2d, TransitionInterface t) {
        // Calcola i centri dei nodi sorgente e target.
        machinery.State sourceState = (machinery.State) t.getSource();
        machinery.State targetState = (machinery.State) t.getTarget();
        Point sourcePos = sourceState.getPosition();
        Point targetPos = targetState.getPosition();
        int sourceCenterOffset = sourceState.getName().equals("PseudoState") ? PSEUDO_RADIUS : RADIUS;
        int targetCenterOffset = targetState.getName().equals("PseudoState") ? PSEUDO_RADIUS : RADIUS;
        Point centerSource = new Point(sourcePos.x + sourceCenterOffset, sourcePos.y + sourceCenterOffset);
        Point centerTarget = new Point(targetPos.x + targetCenterOffset, targetPos.y + targetCenterOffset);

        // Recupera o calcola il control point.
        Point cp = ((Transition) t).getControlPoint();
        if (cp == null) {
            cp = computeControlPoint(centerSource, centerTarget);
            ((Transition) t).setControlPoint(cp);
        }

        Point p0 = computeStartPoint(centerSource, cp, sourceCenterOffset);
        Point p2 = computeEndPoint(centerTarget, cp, targetCenterOffset);

        // Disegna la curva della transizione.
        QuadCurve2D.Double curve = new QuadCurve2D.Double();
        curve.setCurve(p0.x, p0.y, cp.x, cp.y, p2.x, p2.y);
        g2d.setColor(Color.BLACK);
        g2d.draw(curve);
        drawArrowHead(g2d, p0, p2, cp);

        // Disegna l'annotazione del trigger o, se vuota (transizione autonoma), un pallino bianco.
        String trigger = t.getTriggerEvent();
        if (trigger != null && !trigger.trim().isEmpty() && t.isTriggerable()) {
            // Fixed trigger labels are no longer drawn here because triggers are shown as draggable labels.
            // (The draggable labels are handled separately in updateTriggerLabels().)
            // drawTriggerAnnotation(g2d, t, p0, cp, p2);
        } else {
            int circleRadius = 5;
            // Gray for autonomous initial transitions from PseudoState, white otherwise
            if (!t.isTriggerable()
                && t.getSource() instanceof PWSState
                && ((PWSState) t.getSource()).isPseudoState()) {
                g2d.setColor(Color.LIGHT_GRAY);
            } else {
                g2d.setColor(Color.WHITE);
            }
            g2d.fillOval(p0.x - circleRadius, p0.y - circleRadius, circleRadius * 2, circleRadius * 2);
            g2d.setColor(Color.BLACK);
            g2d.drawOval(p0.x - circleRadius, p0.y - circleRadius, circleRadius * 2, circleRadius * 2);
        }

        // Se la transizione è una PWSTransition, aggiorna/disegna le annotazioni.
        PWSTransition pt = null;
        if (t instanceof PWSTransition) {
            pt = (PWSTransition) t;
            drawPWSTransitionAnnotations(g2d, pt, p0, cp, p2);
        }

        if (showControlHandles) {
            drawControlHandle(g2d, cp);
        }

        // Disegna le linee di collegamento tra le annotazioni e l'arco,
        // se la transizione è PWSTransition (pt non è null).
        if (pt != null) {
            Stroke oldStroke = g2d.getStroke();
            float[] dashPattern = {2f, 4f};
            Stroke dashed = new BasicStroke(1, BasicStroke.CAP_ROUND, BasicStroke.JOIN_ROUND, 1.0f, dashPattern, 0.0f);
            g2d.setStroke(dashed);
            g2d.setColor(new Color(180, 180, 180)); // Colore chiaro per le linee

            // GuardAnnotation: linea dal punto a t = 0.8 (verso il target) al centro dell'annotazione.
            if (pt.getGuardAnnotation() != null && pt.getGuardAnnotation().isVisible()) {
                Point guardPoint = computePointOnCurve(p0, cp, p2, 0.2);
                Rectangle guardBounds = pt.getGuardAnnotation().getBounds();
                Point guardCenter = new Point(guardBounds.x + guardBounds.width / 2, guardBounds.y + guardBounds.height / 2);
                g2d.drawLine(guardPoint.x, guardPoint.y, guardCenter.x, guardCenter.y);
            }
            // ActionAnnotation: linea dal punto a t = 0.5 (punto medio) al centro dell'annotazione.
            if (pt.getActionAnnotation() != null && pt.getActionAnnotation().isVisible()) {
                Point actionPoint = computePointOnCurve(p0, cp, p2, 0.5);
                Rectangle actionBounds = pt.getActionAnnotation().getBounds();
                Point actionCenter = new Point(actionBounds.x + actionBounds.width / 2, actionBounds.y + actionBounds.height / 2);
                g2d.drawLine(actionPoint.x, actionPoint.y, actionCenter.x, actionCenter.y);
            }
            // TransitionSemanticsAnnotation: linea dal punto a t = 0.2 (verso il sorgente) al centro dell'annotazione.
            if (pt.getSemanticsAnnotation() != null && pt.getSemanticsAnnotation().isVisible()) {
                Point semPoint = computePointOnCurve(p0, cp, p2, 0.8);
                Rectangle semBounds = pt.getSemanticsAnnotation().getBounds();
                Point semCenter = new Point(semBounds.x + semBounds.width / 2, semBounds.y + semBounds.height / 2);
                g2d.drawLine(semPoint.x, semPoint.y, semCenter.x, semCenter.y);
            }
            g2d.setStroke(oldStroke);
        }
    }

    // Metodo helper per calcolare un punto sulla curva Bézier quadratica dato un parametro t.
    private Point computePointOnCurve(Point p0, Point cp, Point p2, double t) {
        double oneMinusT = 1.0 - t;
        int x = (int) (oneMinusT * oneMinusT * p0.x + 2 * oneMinusT * t * cp.x + t * t * p2.x);
        int y = (int) (oneMinusT * oneMinusT * p0.y + 2 * oneMinusT * t * cp.y + t * t * p2.y);
        return new Point(x, y);
    }

    private Point computeControlPoint(Point centerSource, Point centerTarget) {
        int midX = (centerSource.x + centerTarget.x) / 2;
        int midY = (centerSource.y + centerTarget.y) / 2;
        int offset = 20;
        double dx = centerTarget.x - centerSource.x;
        double dy = centerTarget.y - centerSource.y;
        double distance = Math.sqrt(dx * dx + dy * dy);
        if (distance == 0) distance = 1;
        int controlX = (int) (midX - offset * (dy / distance));
        int controlY = (int) (midY + offset * (dx / distance));
        return new Point(controlX, controlY);
    }

    private Point computeStartPoint(Point centerSource, Point cp, int offset) {
        double d0x = cp.x - centerSource.x;
        double d0y = cp.y - centerSource.y;
        Point2D.Double norm = normalize(d0x, d0y);
        int x = (int) (centerSource.x + norm.x * offset);
        int y = (int) (centerSource.y + norm.y * offset);
        return new Point(x, y);
    }

    private Point computeEndPoint(Point centerTarget, Point cp, int offset) {
        double d1x = centerTarget.x - cp.x;
        double d1y = centerTarget.y - cp.y;
        Point2D.Double norm = normalize(d1x, d1y);
        int x = (int) (centerTarget.x - norm.x * offset);
        int y = (int) (centerTarget.y - norm.y * offset);
        return new Point(x, y);
    }

    protected Point2D.Double normalize(double dx, double dy) {
        double length = Math.sqrt(dx * dx + dy * dy);
        if (length == 0) return new Point2D.Double(0, 0);
        return new Point2D.Double(dx / length, dy / length);
    }

    protected void drawArrowHead(Graphics2D g2d, Point p0, Point p2, Point control) {
        double tangentX = p2.x - control.x;
        double tangentY = p2.y - control.y;
        double theta = Math.atan2(tangentY, tangentX);
        int arrowHeadLength = 10;
        int arrowHeadAngle = 45;
        int x1 = (int) (p2.x - arrowHeadLength * Math.cos(theta - Math.toRadians(arrowHeadAngle)));
        int y1 = (int) (p2.y - arrowHeadLength * Math.sin(theta - Math.toRadians(arrowHeadAngle)));
        int x2 = (int) (p2.x - arrowHeadLength * Math.cos(theta + Math.toRadians(arrowHeadAngle)));
        int y2 = (int) (p2.y - arrowHeadLength * Math.sin(theta + Math.toRadians(arrowHeadAngle)));
        g2d.drawLine(p2.x, p2.y, x1, y1);
        g2d.drawLine(p2.x, p2.y, x2, y2);
    }

    private void drawControlHandle(Graphics2D g2d, Point cp) {
        g2d.setColor(Color.GREEN);
        int handleRadius = 5;
        g2d.fillOval(cp.x - handleRadius, cp.y - handleRadius, handleRadius * 2, handleRadius * 2);
    }

    /**
     * Draws the trigger annotation for a transition.
     */
    protected void drawTriggerAnnotation(Graphics2D g2d, TransitionInterface t, Point p0, Point cp, Point p2) {
        String trigger = t.getTriggerEvent();
        if (trigger == null || trigger.length() == 0) {
            return; // Skip drawing if trigger is empty.
        }
        int textX = (int) ((p0.x + 2 * cp.x + p2.x) / 4.0);
        int textY = (int) ((p0.y + 2 * cp.y + p2.y) / 4.0) - 5;
        AttributedString attrTrigger = new AttributedString(trigger);
        attrTrigger.addAttribute(TextAttribute.FONT, g2d.getFont().deriveFont(Font.BOLD));
        attrTrigger.addAttribute(TextAttribute.UNDERLINE, TextAttribute.UNDERLINE_ON);
        g2d.drawString(attrTrigger.getIterator(), textX, textY);
    }

    /**
     * Draws separate annotations for a PWSTransition: guard, actions, and transition semantics.
     */
    private void drawPWSTransitionAnnotations(Graphics2D g2d, PWSTransition pt, Point p0, Point cp, Point p2) {
        // Recupera l'assembly dal stateMachine
        Assembly assembly = ((PWSStateMachine) stateMachine).getAssembly();

        // ---- Guard Annotation ----
        SMProposition guardProp = pt.getGuardProposition();
        if (pt.getGuardAnnotation() == null) {
            // Compute the point on the curve for the GuardAnnotation (using t = 0.2)
            Point guardPoint = computePointOnCurve(p0, cp, p2, 0.2);
            int guardX = guardPoint.x - 60; // adjust horizontal offset
            int guardY = guardPoint.y - 20; // adjust vertical offset
            GuardAnnotation guardAnnot = new GuardAnnotation(guardProp, assembly, newGuard -> {
                pt.setGuardProposition(newGuard);
            });
            guardAnnot.setBounds(guardX, guardY, 120, 20);
            // For both reactive and triggerable transitions, pass guardProp directly.
            guardAnnot.setContent(guardProp);
            pt.setGuardAnnotation(guardAnnot);
            add(guardAnnot);
        } else {
            pt.getGuardAnnotation().setContent(guardProp);
        }

        // ---- Action Annotation ----
        ActionList actions = pt.getActionList();
        if (pt.getActionAnnotation() == null) {
            Point actionPoint = computePointOnCurve(p0, cp, p2, 0.5);
            int actionX = actionPoint.x - 75; // adatta l'offset orizzontale
            int actionY = actionPoint.y + 20; // adatta l'offset verticale
            ActionAnnotation actionAnnot = new ActionAnnotation(actions, assembly, newActions -> {
                pt.setActionList(newActions);
            });
            actionAnnot.setBounds(actionX, actionY, 150, 20);
            pt.setActionAnnotation(actionAnnot);
            add(actionAnnot);
        } else {
            pt.getActionAnnotation().setContent(actions);
        }

        // ---- Transition Semantics Annotation ----
        Semantics semProp = pt.getTransitionSemantics();
        if (pt.getSemanticsAnnotation() == null) {
            Point semPoint = computePointOnCurve(p0, cp, p2, 0.8);
            int semX = semPoint.x - 50; // adatta l'offset orizzontale
            int semY = semPoint.y - 40; // adatta l'offset verticale
            TransitionSemanticsAnnotation semAnnot = new TransitionSemanticsAnnotation(semProp);
            semAnnot.setBounds(semX, semY, 150, 20);
            semAnnot.setVisible(false);
            pt.setSemanticsAnnotation(semAnnot);
            add(semAnnot);
        } else {
            pt.getSemanticsAnnotation().setContent(semProp);
        }
    }

    // -------------------- MOUSE EVENT HANDLING --------------------

    @Override
    public void mousePressed(MouseEvent e) {
        Point p = e.getPoint();
        System.out.println("mousePressed: button=" + e.getButton() + ", point=" + p + ", isPopupTrigger=" + e.isPopupTrigger());

        // Check if left-click is near a transition control handle for bending.
        if (e.getButton() == MouseEvent.BUTTON1) {
            for (TransitionInterface t : stateMachine.getTransitions()) {
                Point cp = ((Transition) t).getControlPoint();
                if (cp != null && p.distance(cp) <= 8) {
                    selectedTransitionForControl = t;
                    controlDragOffset = new Point(e.getX() - cp.x, e.getY() - cp.y);
                    return;
                }
            }
        }

        // Handle initial transition mode.
        if (initialTransitionMode) {
            handleInitialTransitionMode(e);
            return;
        }

        // Handle link mode.
        if (linkMode) {
            handleLinkMode(e);
            return;
        }

        // Handle right-click events.
        if (SwingUtilities.isRightMouseButton(e)) {
            handleRightClick(e);
            return;
        }

        // Otherwise, select a state for dragging.
        StateInterface state = getStateAt(p);
        if (state != null) {
            selectedState = state;
            Point pos = ((machinery.State) state).getPosition();
            dragOffset = new Point(p.x - pos.x, p.y - pos.y);
        } else {
            selectedState = null;
        }
        repaint();
    }

    @Override
    public void mouseReleased(MouseEvent e) {
        if (SwingUtilities.isRightMouseButton(e) || e.isPopupTrigger()) {
            handleRightClick(e);
            return;
        }
        selectedTransitionForControl = null;
        controlDragOffset = null;
        selectedState = null;
        dragOffset = null;
        repaint();
    }

    @Override
    public void mouseDragged(MouseEvent e) {
        if (selectedTransitionForControl != null && controlDragOffset != null) {
            Point newPoint = e.getPoint();
            Point newControlPoint = new Point(newPoint.x - controlDragOffset.x, newPoint.y - controlDragOffset.y);
            ((Transition) selectedTransitionForControl).setControlPoint(newControlPoint);
            repaint();
        } else if (selectedState != null && dragOffset != null) {
            Point newPoint = e.getPoint();
            ((machinery.State) selectedState).setPosition(new Point(newPoint.x - dragOffset.x, newPoint.y - dragOffset.y));
            repaint();
        }
    }

    @Override
    public void mouseClicked(MouseEvent e) {
    }

    @Override
    public void mouseEntered(MouseEvent e) {
    }

    @Override
    public void mouseExited(MouseEvent e) {
    }

    @Override
    public void mouseMoved(MouseEvent e) {
    }

    // -------------------- HELPER METHODS FOR MOUSE --------------------

    /**
     * Handles initial transition mode: creates an autonomous transition from the pseudo‑state.
     */
    private void handleInitialTransitionMode(MouseEvent e) {
        StateInterface clickedState = getStateAt(e.getPoint());
        if (clickedState != null && !clickedState.getName().equals("PseudoState")) {
            // Trova il Pseudostato (assumendo che esista sempre e abbia nome "PseudoState")
            StateInterface pseudo = stateMachine.getStates().stream()
                    .filter(s -> s.getName().equals("PseudoState"))
                    .findFirst().orElse(null);
            if (pseudo != null) {
                // Verifica se esiste già una transizione autonoma dal Pseudostato al target
                boolean exists = stateMachine.getTransitions().stream()
                        .anyMatch(t -> t.getSource() == pseudo
                                && t.getTarget() == clickedState
                                && t.isAutonomous());
                if (!exists) {
                    // Crea la transizione iniziale come PWSTransition (trigger vuoto, modalità autonoma)
                    PWSTransition newTransition = new PWSTransition(pseudo, clickedState, true, "",((PWSStateMachine)stateMachine).getAssembly());
                    // I campi della transizione (guardProposition, actionList, transitionSemantics) sono
                    // inizializzati ai valori di default (TrueProposition, lista vuota, TrueProposition).
                    stateMachine.addTransition(newTransition);
                    System.out.println("Initial transition created: PseudoState -> " + clickedState.getName());
                } else {
                    JOptionPane.showMessageDialog(this, "An initial transition for this state already exists.");
                }
            } else {
                JOptionPane.showMessageDialog(this, "PseudoState not found.");
            }
        } else {
            JOptionPane.showMessageDialog(this, "Select a valid state (not PseudoState).");
        }
        initialTransitionMode = false;
        revalidate();
        repaint();
    }

    /**
     * Handles link mode: first click selects source state; second click creates a new PWSTransition.
     */
    private void handleLinkMode(MouseEvent e) {
        StateInterface clickedState = getStateAt(e.getPoint());
        if (clickedState != null) {
            if (transitionSourceState == null) {
                transitionSourceState = clickedState;
                System.out.println("Link mode: Source state selected: " + transitionSourceState.getName());
            } else {
                if (clickedState != transitionSourceState) {
                    String trigger = JOptionPane.showInputDialog(this, "Enter trigger event (leave blank for internal):");
                    boolean autonomous = transitionSourceState.getName().equals("PseudoState") ||
                            (trigger == null || trigger.trim().isEmpty());
                    PWSTransition newTransition = new PWSTransition(transitionSourceState, clickedState, autonomous, trigger,((PWSStateMachine)stateMachine).getAssembly());

                    // Here, we no longer use a single dialog; the guard remains default (TRUE) and action list empty,
                    // and the transition semantics default as well.
                    // The user can later modify them by clicking on the corresponding annotations.

                    stateMachine.addTransition(newTransition);
                    System.out.println("Link mode: Transition created from " +
                            transitionSourceState.getName() + " to " + clickedState.getName());
                } else {
                    System.out.println("Link mode: Target same as source. Ignored.");
                }
                linkMode = false;
                transitionSourceState = null;
            }
            repaint();
        } else {
            System.out.println("Link mode: No state found at " + e.getPoint());
        }
    }

    /**
     * Handles right-click events: if near a transition control handle, shows transition popup;
     * otherwise, shows a popup for the state.
     */
    private void handleRightClick(MouseEvent e) {
        Point p = e.getPoint();
        // Check transition control handle first.
        for (TransitionInterface t : stateMachine.getTransitions()) {
            Point cp = ((Transition) t).getControlPoint();
            if (cp != null && p.distance(cp) <= 8) {
                showTransitionPopup(e, t);
                return;
            }
        }
        // Otherwise, show state popup.
        StateInterface state = getStateAt(p);
        if (state != null) {
            showPopupMenuForState(e, state);
        }
    }

    private void showTransitionPopup(MouseEvent e, TransitionInterface t) {
        JPopupMenu popup = new JPopupMenu();

        // Elemento per eliminare la transizione
        JMenuItem deleteItem = new JMenuItem("Elimina Transizione");
        deleteItem.addActionListener(ae -> {
            int confirm = JOptionPane.showConfirmDialog(
                    this,
                    "Sei sicuro di voler cancellare la transizione?",
                    "Conferma cancellazione",
                    JOptionPane.YES_NO_OPTION);
            if(confirm == JOptionPane.YES_OPTION) {
                deleteTransition(t); // Metodo helper che rimuove la transizione e i suoi riferimenti.
                revalidate();
                repaint();
            }
        });
        popup.add(deleteItem);

        // Aggiungi qui eventuali altre voci di menu per le annotazioni, ecc.
        if (t instanceof PWSTransition) {
            PWSTransition pt = (PWSTransition) t;

            // Toggle per la Guard Annotation
            JMenuItem toggleGuardItem = new JMenuItem("Toggle Guard Annotation");
            toggleGuardItem.addActionListener(ae -> {
                if (pt.getGuardAnnotation() != null) {
                    pt.getGuardAnnotation().setVisible(!pt.getGuardAnnotation().isVisible());
                    revalidate();
                    repaint();
                }
            });
            popup.add(toggleGuardItem);

            // Toggle per l'Action Annotation
            JMenuItem toggleActionItem = new JMenuItem("Toggle Action Annotation");
            toggleActionItem.addActionListener(ae -> {
                if (pt.getActionAnnotation() != null) {
                    pt.getActionAnnotation().setVisible(!pt.getActionAnnotation().isVisible());
                    revalidate();
                    repaint();
                }
            });
            popup.add(toggleActionItem);

            // Toggle per la Transition Semantics Annotation
            JMenuItem toggleSemanticsItem = new JMenuItem("Toggle Semantics Annotation");
            toggleSemanticsItem.addActionListener(ae -> {
                if (pt.getSemanticsAnnotation() != null) {
                    pt.getSemanticsAnnotation().setVisible(!pt.getSemanticsAnnotation().isVisible());
                    revalidate();
                    repaint();
                }
            });
            popup.add(toggleSemanticsItem);
        }

        popup.show(this, e.getX(), e.getY());
    }

    protected  void showPopupMenuForState(MouseEvent e, StateInterface state) {
        System.out.println("showPopupMenuForState: Stato rilevato: " + state.getName()
                + " - Tipo: " + state.getClass().getName());
        JPopupMenu popup = new JPopupMenu();

        if (state instanceof PWSState && ((PWSState) state).isPseudoState()) {
            PWSState pwsState = (PWSState) state;
            // Usa un menu item di toggle per il pseudostato
            String toggleText = pwsState.isAnnotationVisible() ? "Nascondi annotazione" : "Mostra annotazione";
            JMenuItem toggleAnnotItem = new JMenuItem(toggleText);
            toggleAnnotItem.addActionListener(ae -> {
                if (!pwsState.isAnnotationVisible()) {
                    System.out.println("Mostra annotazione pseudostato invoked");
                    // Crea l'annotazione se non esiste e la rende visibile
                    StateSemanticsAnnotation annot = pwsState.getAnnotation();
                    if (annot == null) {
                        annot = new StateSemanticsAnnotation(pwsState);
                        // Posiziona l'annotazione vicino al pseudostato
                        Point pos = ((machinery.State) pwsState).getPosition();
                        annot.setBounds(pos.x, pos.y - 40, 120, 30);
                        pwsState.setAnnotation(annot);
                        add(annot);
                        System.out.println("Creato nuovo StateAnnotation per " + pwsState.getName());
                    } else {
                        annot.setVisible(true);
                        System.out.println("Impostata visibilità StateAnnotation a true");
                    }
                    pwsState.setAnnotationVisible(true);
                } else {
                    // Se l'annotazione è visibile, la nasconde
                    if (pwsState.getAnnotation() != null) {
                        pwsState.getAnnotation().setVisible(false);
                        System.out.println("Annotazione pseudostato nascosta");
                    }
                    pwsState.setAnnotationVisible(false);
                }
                revalidate();
                repaint();
            });
            popup.add(toggleAnnotItem);

            JMenuItem infoItem = new JMenuItem("Pseudostato non eliminabile");
            infoItem.setEnabled(false);
            popup.add(infoItem);
        } else {
            // Caso stato normale
            JMenuItem editItem = new JMenuItem("Modifica");
            editItem.addActionListener(ae -> {
                String newName = JOptionPane.showInputDialog(this, "Nuovo nome per lo stato:", state.getName());
                if (newName != null && !newName.trim().isEmpty()) {
                    ((machinery.State) state).setName(newName);
                    repaint();
                }
            });
            popup.add(editItem);

            if (state instanceof PWSState) {
                JMenuItem editConstraintsItem = new JMenuItem("Edit Constraints Semantics");
                editConstraintsItem.addActionListener(ae -> {
                    ConstraintsEditorDialog dialog = new ConstraintsEditorDialog((PWSState) state,((PWSStateMachine) stateMachine).getAssembly());
                    dialog.setVisible(true);
                });
                popup.add(editConstraintsItem);
            }

            if (state instanceof PWSState) {
                PWSState pwsState = (PWSState) state;
                JMenuItem toggleAnnot;
                if (pwsState.isAnnotationVisible()) {
                    toggleAnnot = new JMenuItem("Nascondi Annotazione");
                } else {
                    toggleAnnot = new JMenuItem("Mostra Annotazione");
                }
                toggleAnnot.addActionListener(ae -> {
                    boolean newVisible = !pwsState.isAnnotationVisible();
                    pwsState.setAnnotationVisible(newVisible);
                    if (newVisible) {
                        if (pwsState.getAnnotation() == null) {
                            StateSemanticsAnnotation annot = new StateSemanticsAnnotation(pwsState);
                            Point pos = ((machinery.State) pwsState).getPosition();
                            annot.setBounds(pos.x, pos.y - 40, 120, 30);
                            pwsState.setAnnotation(annot);
                            add(annot);
                            System.out.println("Creato nuovo StateAnnotation per " + pwsState.getName());
                        } else {
                            pwsState.getAnnotation().setVisible(true);
                        }
                    } else {
                        if (pwsState.getAnnotation() != null) {
                            pwsState.getAnnotation().setVisible(false);
                        }
                    }
                    revalidate();
                    repaint();
                });
                popup.add(toggleAnnot);
            }

            JMenuItem deleteItem = new JMenuItem("Elimina");
            deleteItem.addActionListener(ae -> {
                int confirm = JOptionPane.showConfirmDialog(this,
                        "Sei sicuro di voler cancellare lo stato \"" + state.getName() + "\"?",
                        "Conferma cancellazione", JOptionPane.YES_NO_OPTION);
                if (confirm == JOptionPane.YES_OPTION) {
                    // In the PWS case, remove the state's annotation if it exists.
                    if (state instanceof PWSState) {
                        PWSState pwsState = (PWSState) state;
                        if (pwsState.getAnnotation() != null) {
                            remove(pwsState.getAnnotation());
                        }
                    }
                    // Remove the state from the data structure.
                    stateMachine.getStates().remove(state);
                    // Remove any transitions related to the state.
                    Iterator<TransitionInterface> it = stateMachine.getTransitions().iterator();
                    while (it.hasNext()) {
                        TransitionInterface t = it.next();
                        if (t.getSource() == state || t.getTarget() == state) {
                            // For PWS, clear annotations if necessary
                            if (state instanceof PWSState && t instanceof PWSTransition) {
                                clearAnnotationsForTransition((PWSTransition) t);
                            }
                            // Remove t from the global transitions list
                            it.remove();

                            // Remove t from the source state's outgoing transitions
                            StateInterface source = t.getSource();
                            if (source != null && source.getOutgoingTransitions() != null) {
                                source.getOutgoingTransitions().remove(t);
                            }

                            // Remove t from the target state's incoming transitions
                            StateInterface target = t.getTarget();
                            if (target != null && target.getIncomingTransitions() != null) {
                                target.getIncomingTransitions().remove(t);
                            }

                            // Also remove t from the 'state' itself (both incoming and outgoing)
                            if (state.getIncomingTransitions() != null) {
                                state.getIncomingTransitions().remove(t);
                            }
                            if (state.getOutgoingTransitions() != null) {
                                state.getOutgoingTransitions().remove(t);
                            }

//                            // Optional debugging: print if t is still associated with state
//                            if (state.getIncomingTransitions() != null && state.getIncomingTransitions().contains(t)) {
//                                System.out.println(t.toString() + " is still associated to state " + state.getName() + " in incoming transitions");
//                            }
//                            if (state.getOutgoingTransitions() != null && state.getOutgoingTransitions().contains(t)) {
//                                System.out.println(t.toString() + " is still associated to state " + state.getName() + " in outgoing transitions");
//                            }
                        }
                    }
                    repaint();
                }
            });
            popup.add(deleteItem);
        }
        popup.show(this, e.getX(), e.getY());
    }

    // Metodo privato in PWSStateMachine per pulire le annotations di una transizione
    private void clearAnnotationsForTransition(PWSTransition pt) {
        if (pt.getGuardAnnotation() != null) {
            remove(pt.getGuardAnnotation());
            pt.setGuardAnnotation(null);
        }
        if (pt.getActionAnnotation() != null) {
            remove(pt.getActionAnnotation());
            pt.setActionAnnotation(null);
        }
        if (pt.getSemanticsAnnotation() != null) {
            remove(pt.getSemanticsAnnotation());
            pt.setSemanticsAnnotation(null);
        }
    }

    // -------------------- SERIALIZATION METHODS --------------------



    public void saveAnnotationsToStream(ObjectOutputStream oos) throws IOException {
        // Save state annotations.
        for (StateInterface s : stateMachine.getStates()) {
            if (s instanceof PWSState) {
                PWSState pState = (PWSState) s;
                String stateName = pState.getName();
                Rectangle annotBounds = (pState.getAnnotation() != null) ? pState.getAnnotation().getBounds() : null;
                oos.writeUTF(stateName);
                oos.writeObject(annotBounds);
            }
        }
        oos.writeUTF("END_STATES");

        // Save transition annotations.
        for (TransitionInterface t : stateMachine.getTransitions()) {
            if (t instanceof PWSTransition) {
                PWSTransition pt = (PWSTransition) t;
                String transitionId = pt.getId();
                Rectangle guardBounds = (pt.getGuardAnnotation() != null) ? pt.getGuardAnnotation().getBounds() : null;
                Rectangle actionBounds = (pt.getActionAnnotation() != null) ? pt.getActionAnnotation().getBounds() : null;
                Rectangle semanticsBounds = (pt.getSemanticsAnnotation() != null) ? pt.getSemanticsAnnotation().getBounds() : null;
                oos.writeUTF(transitionId);
                oos.writeObject(guardBounds);
                oos.writeObject(actionBounds);
                oos.writeObject(semanticsBounds);
            }
        }
    }

    public void loadAnnotationsFromStream(ObjectInputStream ois) throws IOException, ClassNotFoundException {
        // Restore state annotations.
        String stateName = ois.readUTF();
        while (!"END_STATES".equals(stateName)) {
            Rectangle annotBounds = (Rectangle) ois.readObject();
            for (StateInterface s : stateMachine.getStates()) {
                if (s instanceof PWSState && s.getName().equals(stateName)) {
                    PWSState pState = (PWSState) s;
                    if (annotBounds != null) {
                        if (pState.getAnnotation() == null) {
                            StateSemanticsAnnotation annot = new StateSemanticsAnnotation(pState);
                            annot.setBounds(annotBounds);
                            annot.setVisible(false);
                            pState.setAnnotation(annot);
                            add(annot);
                        } else {
                            pState.getAnnotation().setBounds(annotBounds);
                            pState.getAnnotation().setVisible(false);
                        }
                    }
                    break;
                }
            }
            stateName = ois.readUTF();
        }
        // Restore transition annotations.
        while (true) {
            try {
                String transitionId = ois.readUTF();
                Rectangle guardBounds = (Rectangle) ois.readObject();
                Rectangle actionBounds = (Rectangle) ois.readObject();
                Rectangle semanticsBounds = (Rectangle) ois.readObject();
                for (TransitionInterface t : stateMachine.getTransitions()) {
                    if (t instanceof PWSTransition && ((PWSTransition) t).getId().equals(transitionId)) {
                        PWSTransition pt = (PWSTransition) t;
                        // Guard Annotation
                        if (guardBounds != null) {
                            if (pt.getGuardAnnotation() == null) {
                                SMProposition guardProp = pt.getGuardProposition();
                                GuardAnnotation guardAnnot = new GuardAnnotation(guardProp, ((PWSStateMachine)stateMachine).getAssembly(), newGuard -> pt.setGuardProposition(newGuard));
                                guardAnnot.setBounds(guardBounds);
                                pt.setGuardAnnotation(guardAnnot);
                                add(guardAnnot);
                                // Hide TRUE guards when loading saved annotations
                                if (pt.getGuardProposition() instanceof smalgebra.TrueProposition) {
                                    guardAnnot.setVisible(false);
                                }
                            } else {
                                pt.getGuardAnnotation().setBounds(guardBounds);
                                // Hide TRUE guards when loading saved annotations
                                if (pt.getGuardProposition() instanceof smalgebra.TrueProposition) {
                                    pt.getGuardAnnotation().setVisible(false);
                                }
                            }
                        }
                        // Action Annotation
                        if (actionBounds != null) {
                            if (pt.getActionAnnotation() == null) {
                                ActionAnnotation actionAnnot = new ActionAnnotation(pt.getActionList(), ((PWSStateMachine)stateMachine).getAssembly(), newActions -> pt.setActionList(newActions));
                                actionAnnot.setBounds(actionBounds);
                                pt.setActionAnnotation(actionAnnot);
                                add(actionAnnot);
                                // Hide empty action lists when loading saved annotations
                                if (pt.getActionList().isEmpty()) {
                                    actionAnnot.setVisible(false);
                                }
                            } else {
                                pt.getActionAnnotation().setBounds(actionBounds);
                                // Hide empty action lists when loading saved annotations
                                if (pt.getActionAnnotation().getContent().isEmpty()) {
                                    pt.getActionAnnotation().setVisible(false);
                                }
                            }
                        }
                        // Transition Semantics Annotation
                        if (semanticsBounds != null) {
                            if (pt.getSemanticsAnnotation() == null) {
                                Semantics semProp = pt.getTransitionSemantics();
                                TransitionSemanticsAnnotation semAnnot = new TransitionSemanticsAnnotation(semProp);
                                semAnnot.setBounds(semanticsBounds);
                                semAnnot.setVisible(false);
                                pt.setSemanticsAnnotation(semAnnot);
                                add(semAnnot);
                            } else {
                                pt.getSemanticsAnnotation().setBounds(semanticsBounds);
                                pt.getSemanticsAnnotation().setVisible(false);
                            }
                        }
                        break;
                    }
                }
            } catch (EOFException eof) {
                break;
            }
        }
        revalidate();
        repaint();
    }

    /**
            * Rimuove la transizione t dalla state machine e cancella i riferimenti ad essa:
            * - Rimuove le annotazioni associate (se la transizione è una PWSTransition)
            * - Rimuove t dalla lista globale delle transizioni
            * - Rimuove t dalle liste delle transizioni in uscita dello stato sorgente
            *   e dalle transizioni in ingresso dello stato target.
            */
    public void deleteTransition(TransitionInterface t) {
        // Se t è di tipo PWSTransition, pulisci le annotazioni associate.
        if (t instanceof PWSTransition) {
            clearAnnotationsForTransition((PWSTransition) t);
        }
        // Rimuove la transizione dalla lista globale.
        stateMachine.getTransitions().remove(t);

        // Rimuove la transizione dalla lista delle transizioni in uscita dello stato sorgente.
        StateInterface source = t.getSource();
        if (source != null && source.getOutgoingTransitions() != null) {
            source.getOutgoingTransitions().remove(t);
        }

        // Rimuove la transizione dalla lista delle transizioni in ingresso dello stato target.
        StateInterface target = t.getTarget();
        if (target != null && target.getIncomingTransitions() != null) {
            target.getIncomingTransitions().remove(t);
        }

        // After removing the transition, update and remove its trigger label
        updateTriggerLabels();
        revalidate();
        repaint();
    }
}