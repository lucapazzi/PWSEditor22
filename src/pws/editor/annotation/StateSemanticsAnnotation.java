package pws.editor.annotation;

import pws.PWSState;
import pws.editor.PWSStateMachinePanel;
import pws.PWSStateMachine;
import java.util.*;
import java.util.List;
import java.util.ArrayList;

import javax.swing.*;
import java.awt.*;
import java.awt.event.MouseEvent;
import java.util.List;
import java.util.Collection;
import java.util.StringJoiner;
import pws.editor.semantics.Semantics;
import java.awt.Color;

public class StateSemanticsAnnotation extends Annotation<PWSState> {

    public StateSemanticsAnnotation(PWSState content) {
        super(content);
        setOpaque(true);
        setBackground(Color.WHITE);
        setBorder(BorderFactory.createLineBorder(Color.red, 1));
    }

    @Override
    protected void showPopup(MouseEvent e) {
        // Create a popup with a single disabled menu item.
        JPopupMenu popup = new JPopupMenu();
        JMenuItem notModifiable = new JMenuItem("Annotazione non modificabile");
        notModifiable.setEnabled(false);
        popup.add(notModifiable);
        popup.show(this, e.getX(), e.getY());
    }

    @Override
    protected String buildDisplayText() {
        return "";
    }

    @Override
    protected void paintComponent(Graphics g) {
        if (isOpaque()) {
            g.setColor(getBackground());
            g.fillRect(0, 0, getWidth(), getHeight());
        }
        super.paintComponent(g);
        Graphics2D g2d = (Graphics2D) g;
        g2d.setFont(getFont().deriveFont(Font.PLAIN, 12f));
        g2d.setColor(Color.BLACK);

        if (content == null) return;

        PWSState state = content;
        FontMetrics fm = g2d.getFontMetrics();

        int padding = 4;
        int y = fm.getHeight() + padding;
        // 1) Constraint semantics (blue, centered)
        String constraintSem;
        String raw = state.getRawConstraintText();
        if (state.isPseudoState()) {
            // Pseudostate always shows "ANY"
            constraintSem = "ANY";
        } else if (raw != null && !raw.isBlank()) {
            // Show the user-entered compact constraints as (line1), (line2), ...
            String[] lines = raw.split("\\r?\\n");
            StringJoiner sjRaw = new StringJoiner(", ");
            for (String line : lines) {
                String s = line.trim();
                if (!s.startsWith("(")) s = "(" + s;
                if (!s.endsWith(")")) s = s + ")";
                sjRaw.add(s);
            }
            constraintSem = sjRaw.toString();
        } else {
            // Build a parenthesized OR‑joined constraint string
            Semantics cs = state.getConstraintsSemantics();
            if (cs == null) {
                constraintSem = "";
            } else {
                Collection<?> configs = cs.getConfigurations();
                if (configs.size() <= 1) {
                    // Single or none: show directly
                    constraintSem = configs.isEmpty()
                        ? ""
                        : configs.iterator().next().toString();
                } else {
                    // Multiple: wrap each in parentheses and join with OR
                    // Join multiple configurations with spaces, each wrapped in parentheses
                    StringJoiner sj = new StringJoiner(" ");
                    for (Object cfg : configs) {
                        String s = cfg.toString();
                        if (!s.startsWith("(") || !s.endsWith(")")) {
                            s = "(" + s + ")";
                        }
                        sj.add(s);
                    }
                    constraintSem = sj.toString();
                }
            }
        }
        g2d.setColor(Color.BLUE);
        int w1 = fm.stringWidth(constraintSem);
        g2d.drawString(constraintSem, (getWidth() - w1) / 2, y);

        // 2) Actual state semantics: each configuration green if in constraints, red otherwise
        y += fm.getHeight();
        Set<?> constraintsConfigs = state.getConstraintsSemantics() == null
                ? Collections.emptySet()
                : state.getConstraintsSemantics().getConfigurations();
        Set<?> stateConfigs = state.getStateSemantics() == null
                ? Collections.emptySet()
                : state.getStateSemantics().getConfigurations();
        // prepare string set of constraint configurations
        Set<String> constraintStrs = new HashSet<>();
        for (Object cfg : constraintsConfigs) {
            constraintStrs.add(cfg.toString());
        }
        List<String> cfgStrs = new ArrayList<>();
        for (Object cfg : stateConfigs) {
            cfgStrs.add(cfg.toString());
        }
        int totalWidth = 0;
        for (String s : cfgStrs) {
            totalWidth += fm.stringWidth(s) + fm.charWidth(' ');
        }
        int x = (getWidth() - totalWidth) / 2;
        for (String s : cfgStrs) {
            // Always paint green for the pseudostate’s actual semantics
            boolean isGreen = state.isPseudoState() || constraintStrs.contains(s);
            g2d.setColor(isGreen ? Color.GREEN.darker() : Color.RED);
            g2d.drawString(s, x, y);
            x += fm.stringWidth(s) + fm.charWidth(' ');
        }

        // 3) Reactive exit zones: centered, comma-separated, colored by coverage
        y += fm.getHeight();
        try {
            PWSStateMachine sm = ((PWSStateMachinePanel) getParent()).getStateMachine();
            // Determine covered guards for coloring
            Set<smalgebra.BasicStateProposition> covered = new HashSet<>();
            for (machinery.TransitionInterface ti : sm.getTransitions()) {
                if (ti instanceof pws.PWSTransition) {
                    pws.PWSTransition pt = (pws.PWSTransition) ti;
                    if (!pt.isTriggerable() && pt.getSource() == state
                            && pt.getGuardProposition() instanceof smalgebra.BasicStateProposition) {
                        covered.add((smalgebra.BasicStateProposition) pt.getGuardProposition());
                    }
                }
            }
            // Prepare list of exit-zones
            List<pws.editor.semantics.ExitZone> zones = new ArrayList<>(state.getReactiveSemantics());
            // Compute total width of comma-separated exit-zone list
            int exitTotalWidth = 0;
            for (int i = 0; i < zones.size(); i++) {
                String txt = zones.get(i).toString();
                exitTotalWidth += fm.stringWidth(txt);
                if (i < zones.size() - 1) {
                    exitTotalWidth += fm.stringWidth(", ");
                }
            }
            int exitX = (getWidth() - exitTotalWidth) / 2;
            // Draw each exit-zone with comma separators
            for (int i = 0; i < zones.size(); i++) {
                pws.editor.semantics.ExitZone ez = zones.get(i);
                String txt = ez.toString();
                boolean isCovered = covered.contains(ez.getTarget());
                g2d.setColor(isCovered ? Color.GREEN.darker() : Color.RED);
                g2d.drawString(txt, exitX, y);
                exitX += fm.stringWidth(txt);
                if (i < zones.size() - 1) {
                    String sep = ", ";
                    g2d.setColor(Color.BLACK);
                    g2d.drawString(sep, exitX, y);
                    exitX += fm.stringWidth(sep);
                }
            }
        } catch (Exception ignored) {
        }
    }

    @Override
    public Dimension getPreferredSize() {
        if (content == null) return new Dimension(100, 50);

        PWSState state = content;
        // Determine constraint text for sizing, matching paintComponent logic
        String raw = state.getRawConstraintText();
        String constraintSem;
        if (state.isPseudoState()) {
            constraintSem = "ANY";
        } else if (raw != null && !raw.isBlank()) {
            // Show compact user-entered constraints wrapped in parentheses
            String[] linesRaw = raw.split("\\r?\\n");
            StringJoiner sjRaw = new StringJoiner(", ");
            for (String line : linesRaw) {
                String s = line.trim();
                if (!s.startsWith("(")) s = "(" + s;
                if (!s.endsWith(")")) s = s + ")";
                sjRaw.add(s);
            }
            constraintSem = sjRaw.toString();
        } else {
            // Fallback to full expanded semantics only if no raw text
            Semantics cs = state.getConstraintsSemantics();
            constraintSem = (cs == null) ? "" : cs.toString();
        }
        String actualSem = (state.getStateSemantics() == null)
            ? ""
            : state.getStateSemantics().toString();
        String autonomousSem = (state.getReactiveSemantics() == null)
            ? ""
            : state.getReactiveSemantics().toString();

        String[] lines = new String[] { constraintSem, actualSem, autonomousSem };
        FontMetrics fm = getFontMetrics(getFont().deriveFont(Font.PLAIN, 12f));
        int maxWidth = 0;
        for (String line : lines) {
            maxWidth = Math.max(maxWidth, fm.stringWidth(line));
        }
        int totalHeight = fm.getHeight() * lines.length;
        // Add padding
        return new Dimension(maxWidth + 10, totalHeight + 10);
    }
}