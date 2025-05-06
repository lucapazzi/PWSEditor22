package pws.editor.annotation;

import assembly.Action;
import assembly.ActionList;
import assembly.AssemblyInterface;

import javax.swing.*;
import java.awt.*;
import java.awt.event.MouseEvent;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Consumer;

public class ActionAnnotation extends Annotation<ActionList> {
    private AssemblyInterface assembly;
    private Consumer<ActionList> updateCallback; // Callback per aggiornare il modello

    public ActionAnnotation(ActionList content, AssemblyInterface assembly, Consumer<ActionList> updateCallback) {
        super(content);
        this.assembly = assembly;
        this.updateCallback = updateCallback;
    }

    @Override
    protected void showPopup(MouseEvent e) {
        JPopupMenu popup = new JPopupMenu();

        // Sezione "Inserisci"
        JMenuItem insertLabel = new JMenuItem("Inserisci");
        insertLabel.setEnabled(false);
        popup.add(insertLabel);

        List<Action> allActions = assembly.getAssemblyActions();
        ActionList current = getContent();
        List<Action> actionsToInsert = new ArrayList<>();
        for (Action a : allActions) {
            boolean alreadyPresent = false;
            for (Action act : current) {
                if (act.getMachineId().equals(a.getMachineId())) {
                    alreadyPresent = true;
                    break;
                }
            }
            if (!alreadyPresent) {
                actionsToInsert.add(a);
            }
        }
        if (actionsToInsert.isEmpty()) {
            JMenuItem noInsert = new JMenuItem("Nessuna azione disponibile");
            noInsert.setEnabled(false);
            popup.add(noInsert);
        } else {
            for (Action a : actionsToInsert) {
                JMenuItem item = new JMenuItem(a.toString());
                item.addActionListener(ev -> {
                    current.add(a);
                    setContent(current);
                    updateCallback.accept(current);
                    revalidate();
                    repaint();
                });
                popup.add(item);
            }
        }

        popup.addSeparator();

        // Sezione "Rimuovi"
        JMenuItem removeLabel = new JMenuItem("Rimuovi");
        removeLabel.setEnabled(false);
        popup.add(removeLabel);
        if (current.isEmpty()) {
            JMenuItem noRemove = new JMenuItem("Nessuna azione inserita");
            noRemove.setEnabled(false);
            popup.add(noRemove);
        } else {
            for (Action a : current) {
                JMenuItem item = new JMenuItem(a.toString());
                item.addActionListener(ev -> {
                    current.remove(a);
                    setContent(current);
                    updateCallback.accept(current);
                    revalidate();
                    repaint();
                });
                popup.add(item);
            }
        }

        popup.show(this, e.getX(), e.getY());
    }

    protected String buildDisplayText() {
        return (content == null ? "" : content.toString());
    }

//    @Override
//    protected void paintComponent(Graphics g) {
//        super.paintComponent(g);
//        // Draw the string representation of the content centered in the component.
//        Graphics2D g2d = (Graphics2D) g;
//        g2d.setFont(getFont().deriveFont(Font.PLAIN, 12f));
//        g2d.setColor(Color.BLACK);
//        String text = (content == null ? "" : content.toString());
//        FontMetrics fm = g2d.getFontMetrics();
//        int textWidth = fm.stringWidth(text);
//        int textHeight = fm.getAscent();
//        int x = (getWidth() - textWidth) / 2;
//        int y = (getHeight() + textHeight) / 2 - 2;
//        g2d.drawString(text, x, y);
//    }
}