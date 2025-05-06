package editor;

import machinery.*;
import pws.PWSTransition;
import utility.DraggableTriggerLabel;

import javax.swing.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.Stroke;
import java.awt.geom.Point2D;
import java.awt.geom.QuadCurve2D;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

public class StateMachinePanel extends JPanel implements MouseListener, MouseMotionListener {

    protected StateMachine stateMachine;
    protected StateInterface selectedState = null;
    protected Point dragOffset = null;

    // Link mode fields
    protected boolean linkMode = false;
    protected StateInterface transitionSourceState = null;

    // Fields for control handle (for bending transitions)
    protected TransitionInterface selectedTransitionForControl = null;
    protected Point controlDragOffset = null;

    // Flag to show control handles
    protected boolean showControlHandles = true;

    // Initial transition mode flag
    protected boolean initialTransitionMode = false;

    // Graphic constants
    protected final int DIAMETER = 50;
    protected final int RADIUS = DIAMETER / 2;
    // Reduce pseudostate diameter to one third of the normal diameter.
    protected final int PSEUDO_DIAMETER = DIAMETER / 3;
    protected final int PSEUDO_RADIUS = PSEUDO_DIAMETER / 2;

    // Map to hold trigger labels for transitions
    protected Map<TransitionInterface, DraggableTriggerLabel> triggerLabels = new HashMap<>();

    public StateMachinePanel(StateMachine stateMachine) {
        this.stateMachine = stateMachine;
        setBackground(Color.WHITE);
        // Using null layout to allow absolute positioning of draggable labels.
        setLayout(null);
        addMouseListener(this);
        addMouseMotionListener(this);
        // Enable keyboard focus so we can capture arrow keys
        setFocusable(true);
        // --- WASD-key bindings to pan the entire diagram ---
        InputMap im = getInputMap(JComponent.WHEN_IN_FOCUSED_WINDOW);
        ActionMap am = getActionMap();

        im.put(KeyStroke.getKeyStroke(KeyEvent.VK_A, 0), "moveLeft");   // A = left
        im.put(KeyStroke.getKeyStroke(KeyEvent.VK_D, 0), "moveRight");  // D = right
        im.put(KeyStroke.getKeyStroke(KeyEvent.VK_W, 0), "moveUp");     // W = up
        im.put(KeyStroke.getKeyStroke(KeyEvent.VK_S, 0), "moveDown");   // S = down

        am.put("moveLeft",  new AbstractAction() { public void actionPerformed(ActionEvent e){ translateAllStates(-1, 0); }});
        am.put("moveRight", new AbstractAction() { public void actionPerformed(ActionEvent e){ translateAllStates( 1, 0); }});
        am.put("moveUp",    new AbstractAction() { public void actionPerformed(ActionEvent e){ translateAllStates(0,-1); }});
        am.put("moveDown",  new AbstractAction() { public void actionPerformed(ActionEvent e){ translateAllStates(0, 1); }});
    }

    public void setStateMachine(StateMachine sm) {
        this.stateMachine = sm;
    }

    public boolean isShowControlHandles() {
        return showControlHandles;
    }

    public void setShowControlHandles(boolean showControlHandles) {
        this.showControlHandles = showControlHandles;
        repaint();
    }

    public void enableLinkMode() {
        linkMode = true;
        transitionSourceState = null;
        System.out.println("Link mode activated. Select source node, then target node.");
    }

    public void enableInitialTransitionMode() {
        initialTransitionMode = true;
        System.out.println("Initial transition mode activated: click on a target to create an autonomous transition from the pseudo‑state.");
    }

    @Override
    protected void paintComponent(Graphics g) {
        super.paintComponent(g);
        // Remove previous trigger labels before redrawing
        // removeAllTriggerLabels();
        drawStates(g);
        drawTransitions(g);
        updateTriggerLabels(); // Add draggable labels for transitions with triggers
    }

    // Remove and clear all trigger labels
    private void removeAllTriggerLabels() {
        for (DraggableTriggerLabel label : triggerLabels.values()) {
            remove(label);
        }
        triggerLabels.clear();
    }

    /**
     * Updates/creates draggable trigger labels for each triggerable transition.
     */
    protected void updateTriggerLabels() {
        // Remove labels for transitions no longer triggerable or removed
        Iterator<Map.Entry<TransitionInterface, DraggableTriggerLabel>> it = triggerLabels.entrySet().iterator();
        while (it.hasNext()) {
            Map.Entry<TransitionInterface, DraggableTriggerLabel> entry = it.next();
            TransitionInterface t = entry.getKey();
            if (!t.isTriggerable() || !stateMachine.getTransitions().contains(t)) {
                remove(entry.getValue());
                it.remove();
            }
        }
        // Iterate over transitions to update or create trigger labels.
        for (TransitionInterface t : stateMachine.getTransitions()) {
            if (t.isTriggerable()) {
                // Get the label for this transition, if it exists.
                DraggableTriggerLabel label = triggerLabels.get(t);
                if (label == null) {
                    // Create a new label, associating it with the transition.
                    label = new DraggableTriggerLabel(t.getTriggerEvent(), t);
                    // Compute default position.
                    State sourceState = (State) t.getSource();
                    State targetState = (State) t.getTarget();
                    Point sourcePos = sourceState.getPosition();
                    Point targetPos = targetState.getPosition();
                    int sourceCenterOffset = sourceState.getName().equals("PseudoState") ? PSEUDO_RADIUS : RADIUS;
                    int targetCenterOffset = targetState.getName().equals("PseudoState") ? PSEUDO_RADIUS : RADIUS;
                    Point centerSource = new Point(sourcePos.x + sourceCenterOffset, sourcePos.y + sourceCenterOffset);
                    Point centerTarget = new Point(targetPos.x + targetCenterOffset, targetPos.y + targetCenterOffset);
                    Point cp = ((Transition) t).getControlPoint();
                    if (cp == null) {
                        cp = computeControlPoint(centerSource, centerTarget);
                        ((Transition) t).setControlPoint(cp);
                    }
                    Point p0 = computeStartPoint(centerSource, cp, sourceCenterOffset);
                    Point p2 = computeEndPoint(centerTarget, cp, targetCenterOffset);
                    int defaultX = (int) ((p0.x + 2 * cp.x + p2.x) / 4.0) + 5;
                    int defaultY = (int) ((p0.y + 2 * cp.y + p2.y) / 4.0) - 5;
                    Dimension size = label.getPreferredSize();
                    label.setBounds(defaultX, defaultY, size.width, size.height);
                    label.setVisible(true);
                    add(label);
                    triggerLabels.put(t, label);
                } else {
                    // Update text in case it changed.
                    label.setText("<html><b><u>" + t.getTriggerEvent() + "</u></b></html>");
                    // If the transition already has a stored trigger offset, use it.
                    Point offset = t.getTriggerOffset();
                    if (offset != null) {
                        Dimension size = label.getPreferredSize();
                        label.setBounds(offset.x, offset.y, size.width, size.height);
                    }
                    // Otherwise, do not modify its location; let it remain at the user-defined position.
                }
            }
        }
    }

    protected void drawStates(Graphics g) {
        List<StateInterface> states = stateMachine.getStates();
        for (StateInterface state : states) {
            Point pos = ((State) state).getPosition();
            int x = pos.x;
            int y = pos.y;
            if (state.getName().equals("PseudoState")) {
                g.setColor(Color.BLACK);
                g.fillOval(x, y, PSEUDO_DIAMETER, PSEUDO_DIAMETER);
                g.setColor(Color.BLACK);
                g.drawOval(x, y, PSEUDO_DIAMETER, PSEUDO_DIAMETER);
            } else {
                g.setColor(Color.WHITE);
                g.fillOval(x, y, DIAMETER, DIAMETER);
                if (state == selectedState || state == transitionSourceState) {
                    g.setColor(Color.RED);
                } else {
                    g.setColor(Color.BLACK);
                }
                g.drawOval(x, y, DIAMETER, DIAMETER);
                String name = state.getName();
                FontMetrics fm = g.getFontMetrics();
                int textWidth = fm.stringWidth(name);
                int textHeight = fm.getHeight();
                int textX = x + (DIAMETER - textWidth) / 2;
                int textY = y + (DIAMETER - textHeight) / 2 + fm.getAscent();
                g.drawString(name, textX, textY);
            }
        }
    }

    protected void drawTransitions(Graphics g) {
        Graphics2D g2d = (Graphics2D) g;
        g2d.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
        List<TransitionInterface> transitions = stateMachine.getTransitions();
        for (TransitionInterface t : transitions) {
            drawSingleTransition(g2d, t);
        }
    }

    protected void drawSingleTransition(Graphics2D g2d, TransitionInterface t) {
        // Get centers of source and target.
        State sourceState = (State) t.getSource();
        State targetState = (State) t.getTarget();
        Point sourcePos = sourceState.getPosition();
        Point targetPos = targetState.getPosition();
        int sourceCenterOffset = sourceState.getName().equals("PseudoState") ? PSEUDO_RADIUS : RADIUS;
        int targetCenterOffset = targetState.getName().equals("PseudoState") ? PSEUDO_RADIUS : RADIUS;
        Point centerSource = new Point(sourcePos.x + sourceCenterOffset, sourcePos.y + sourceCenterOffset);
        Point centerTarget = new Point(targetPos.x + targetCenterOffset, targetPos.y + targetCenterOffset);

        // Compute control point for the curve.
        Point cp = ((Transition) t).getControlPoint();
        if (cp == null) {
            cp = computeControlPoint(centerSource, centerTarget);
            ((Transition) t).setControlPoint(cp);
        }
        Point p0 = computeStartPoint(centerSource, cp, sourceCenterOffset);
        Point p2 = computeEndPoint(centerTarget, cp, targetCenterOffset);

        // Draw the transition curve.
        QuadCurve2D.Double curve = new QuadCurve2D.Double();
        curve.setCurve(p0.x, p0.y, cp.x, cp.y, p2.x, p2.y);
        g2d.setColor(Color.BLACK);
        g2d.draw(curve);
        drawArrowHead(g2d, p0, p2, cp);

        // For triggerable transitions, the draggable label is now used.
        if (!t.isTriggerable()) {
            int circleRadius = 5;
            // Gray for initial transition from pseudostate, white otherwise
            if (sourceState.getName().equals("PseudoState")) {
                g2d.setColor(Color.LIGHT_GRAY);
            } else {
                g2d.setColor(Color.WHITE);
            }
            g2d.fillOval(p0.x - circleRadius, p0.y - circleRadius, circleRadius * 2, circleRadius * 2);
            g2d.setColor(Color.BLACK);
            g2d.drawOval(p0.x - circleRadius, p0.y - circleRadius, circleRadius * 2, circleRadius * 2);
        }

        // Draw control handles if enabled.
        if (showControlHandles) {
            drawControlHandle(g2d, cp);
        }
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

    private void drawArrowHead(Graphics2D g2d, Point p0, Point p2, Point control) {
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

    protected StateInterface getStateAt(Point p) {
        List<StateInterface> states = stateMachine.getStates();
        for (StateInterface state : states) {
            Point pos = ((State) state).getPosition();
            int diam = state.getName().equals("PseudoState") ? PSEUDO_DIAMETER : DIAMETER;
            Rectangle rect = new Rectangle(pos.x, pos.y, diam, diam);
            if (rect.contains(p)) {
                return state;
            }
        }
        return null;
    }

    /**
     * Shift every state position and transition control point by the given delta.
     */
    private void translateAllStates(int dx, int dy) {
        for (StateInterface s : stateMachine.getStates()) {
            State st = (State) s;
            // Move state position
            Point pos = st.getPosition();
            st.setPosition(new Point(pos.x + dx, pos.y + dy));

            /* ---- Move state‑level annotations if present ---- */
            // Works only if we’re in a PWS environment, but safe to attempt cast
            if (st instanceof pws.PWSState pwsSt) {
                if (pwsSt.getAnnotation() != null) {
                    Rectangle r = pwsSt.getAnnotation().getBounds();
                    pwsSt.getAnnotation().setBounds(r.x + dx, r.y + dy, r.width, r.height);
                }
            }
        }

        for (TransitionInterface t : stateMachine.getTransitions()) {
            Transition tr = (Transition) t;
            // Move Bézier control point
            Point cp = tr.getControlPoint();
            if (cp != null) cp.translate(dx, dy);

            // Move trigger label offset (for draggable trigger labels)
            if (t.getTriggerOffset() != null) {
                Point off = t.getTriggerOffset();
                t.setTriggerOffset(new Point(off.x + dx, off.y + dy));
            }

            /* ---- Move transition‑level annotations if present ---- */
            if (t instanceof PWSTransition pwt) {
                // Guard annotation
                if (pwt.getGuardAnnotation() != null) {
                    Rectangle r = pwt.getGuardAnnotation().getBounds();
                    pwt.getGuardAnnotation().setBounds(r.x + dx, r.y + dy, r.width, r.height);
                }
                // Action annotation
                if (pwt.getActionAnnotation() != null) {
                    Rectangle r = pwt.getActionAnnotation().getBounds();
                    pwt.getActionAnnotation().setBounds(r.x + dx, r.y + dy, r.width, r.height);
                }
                // Transition semantics annotation
                if (pwt.getSemanticsAnnotation() != null) {
                    Rectangle r = pwt.getSemanticsAnnotation().getBounds();
                    pwt.getSemanticsAnnotation().setBounds(r.x + dx, r.y + dy, r.width, r.height);
                }
            }
        }
        repaint();
    }

    // --------------- MOUSE EVENT HANDLING ---------------

    @Override
    public void mousePressed(MouseEvent e) {
        Point p = e.getPoint();
        // Ensure the panel gains focus so its arrow‑key bindings have priority
        if (!hasFocus()) {
            requestFocusInWindow();
        }
        System.out.println("mousePressed: button=" + e.getButton() + ", point=" + p + ", isPopupTrigger=" + e.isPopupTrigger());
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
        if (initialTransitionMode) {
            handleInitialTransitionMode(e);
            return;
        }
        if (linkMode) {
            handleLinkMode(e);
            return;
        }
        if (SwingUtilities.isRightMouseButton(e)) {
            handleRightClick(e);
            return;
        }
        StateInterface state = getStateAt(p);
        if (state != null) {
            selectedState = state;
            Point posState = ((State) state).getPosition();
            dragOffset = new Point(p.x - posState.x, p.y - posState.y);
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
            ((State) selectedState).setPosition(new Point(newPoint.x - dragOffset.x, newPoint.y - dragOffset.y));
            repaint();
        }
    }

    @Override public void mouseClicked(MouseEvent e) { }
    @Override public void mouseEntered(MouseEvent e) { }
    @Override public void mouseExited(MouseEvent e) { }
    @Override public void mouseMoved(MouseEvent e) { }

    private void handleInitialTransitionMode(MouseEvent e) {
        StateInterface clickedState = getStateAt(e.getPoint());
        if (clickedState != null && !clickedState.getName().equals("PseudoState")) {
            StateInterface pseudo = stateMachine.getStates().stream()
                    .filter(s -> s.getName().equals("PseudoState"))
                    .findFirst().orElse(null);
            if (pseudo != null) {
                boolean exists = stateMachine.getTransitions().stream()
                        .anyMatch(t -> t.getSource() == pseudo && t.getTarget() == clickedState && t.isAutonomous());
                if (!exists) {
                    TransitionInterface newTransition = new Transition(pseudo, clickedState, true, "");
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
        repaint();
    }

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
                    TransitionInterface newTransition = new Transition(transitionSourceState, clickedState, autonomous, trigger);
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

    private void handleRightClick(MouseEvent e) {
        Point p = e.getPoint();
        for (TransitionInterface t : stateMachine.getTransitions()) {
            Point cp = ((Transition) t).getControlPoint();
            if (cp != null && p.distance(cp) <= 8) {
                showTransitionPopup(e, t);
                return;
            }
        }
        StateInterface state = getStateAt(p);
        if (state != null) {
            showPopupMenuForState(e, state);
        }
    }

    private void showTransitionPopup(MouseEvent e, TransitionInterface t) {
        JPopupMenu popup = new JPopupMenu();

        // Voce di menu per eliminare la transizione
        JMenuItem deleteItem = new JMenuItem("Elimina Transizione");
        deleteItem.addActionListener(ae -> {
            // Utilizza il metodo helper per rimuovere la transizione e tutti i riferimenti associati
            deleteTransition(t);
            revalidate();
            repaint();
        });
        popup.add(deleteItem);

        // Se necessario, qui puoi aggiungere ulteriori voci per gestire annotazioni (guard, action, semantics),
        // per esempio "Toggle Guard Annotation", "Toggle Action Annotation", ecc.
        // (Queste voci potrebbero essere identiche per transizioni iniziali e normali se il comportamento deve essere uniforme.)

        popup.show(this, e.getX(), e.getY());
    }

    private void showPopupMenuForState(MouseEvent e, StateInterface state) {
        System.out.println("showPopupMenuForState invoked for state: " + state.getName());
        JPopupMenu popup = new JPopupMenu();
        JMenuItem editItem = new JMenuItem("Modifica");
        editItem.addActionListener(ae -> {
            String newName = JOptionPane.showInputDialog(this, "Nuovo nome per lo stato:", state.getName());
            if (newName != null && !newName.trim().isEmpty()) {
                ((State) state).setName(newName);
                repaint();
            }
        });
        popup.add(editItem);
        if (!state.getName().equals("PseudoState")) {
            JMenuItem deleteItem = new JMenuItem("Elimina");
            deleteItem.addActionListener(ae -> {
                System.out.println("Delete menu item clicked for state: " + state.getName());
                int confirm = JOptionPane.showConfirmDialog(this,
                        "Sei sicuro di voler cancellare lo stato \"" + state.getName() + "\"?",
                        "Conferma cancellazione", JOptionPane.YES_NO_OPTION);
                if (confirm == JOptionPane.YES_OPTION) {
                    boolean removed = stateMachine.getStates().remove(state);
                    if (removed) {
                        stateMachine.getTransitions().removeIf(t -> t.getSource() == state || t.getTarget() == state);
                        System.out.println("Lo stato e le transizioni correlate sono stati rimossi dalla struttura dati.");
                    } else {
                        System.out.println("Errore: lo stato non è stato rimosso dalla struttura dati.");
                    }
                    repaint();
                }
            });
            popup.add(deleteItem);
        } else {
            JMenuItem infoItem = new JMenuItem("Pseudostato non eliminabile");
            infoItem.setEnabled(false);
            popup.add(infoItem);
        }
        System.out.println("Showing popup menu for state: " + state.getName());
        popup.show(this, e.getX(), e.getY());
    }

    /**
     * Rimuove la transizione t dalla state machine e cancella i riferimenti ad essa:
     * - Rimuove le annotazioni associate (se la transizione è una PWSTransition)
     * - Rimuove t dalla lista globale delle transizioni
     * - Rimuove t dalle liste delle transizioni in uscita dello stato sorgente
     *   e dalle transizioni in ingresso dello stato target.
     */
    private void deleteTransition(TransitionInterface t) {
//        // Se t è di tipo PWSTransition, pulisci le annotazioni associate.
//        if (t instanceof PWSTransition) {
//            clearAnnotationsForTransition((PWSTransition) t);
//        }
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
    }
}