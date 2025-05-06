package pws.editor.annotation;

import pws.editor.semantics.Semantics;
import smalgebra.SMProposition;

import javax.swing.*;
import java.awt.*;
import java.awt.event.MouseEvent;

public class TransitionSemanticsAnnotation extends Annotation<Semantics> {
    public TransitionSemanticsAnnotation(Semantics content) {
        super(content);
    }

//    @Override
//    protected void showPopup(java.awt.event.MouseEvent e) {
//        // Implement specific popup for transition semantics.
//        super.showPopup(e);
//    }

    @Override
    protected void showPopup(MouseEvent e) {
        // Create a popup with a single disabled menu item.
        JPopupMenu popup = new JPopupMenu();
        JMenuItem notModifiable = new JMenuItem("Annotazione non modificabile");
        notModifiable.setEnabled(false);
        popup.add(notModifiable);
        popup.show(this, e.getX(), e.getY());
    }

    protected String buildDisplayText() {
        return (content == null ? "" : content.toString());
    }

//    @Override
//    protected void paintComponent(Graphics g) {
//        super.paintComponent(g);
//        Graphics2D g2d = (Graphics2D) g;
//        g2d.setFont(getFont().deriveFont(Font.PLAIN, 12f));
//        g2d.setColor(Color.BLACK);
//        // Usa toConfig() per la visualizzazione della semantica
//        String text = (content == null ? "" : content.toSem().toString());
//        FontMetrics fm = g2d.getFontMetrics();
//        int textWidth = fm.stringWidth(text);
//        int textHeight = fm.getAscent();
//        int x = (getWidth() - textWidth) / 2;
//        int y = (getHeight() + textHeight) / 2 - 2;
//        g2d.drawString(text, x, y);
//    }
}