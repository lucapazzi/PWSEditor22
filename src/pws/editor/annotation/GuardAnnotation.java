package pws.editor.annotation;

import assembly.Assembly;
import assembly.AssemblyInterface;
import smalgebra.SMProposition;
import smalgebra.TrueProposition;

import javax.swing.*;
import java.awt.*;
import java.awt.event.MouseEvent;
import java.util.List;
import java.util.function.Consumer;

public class GuardAnnotation extends Annotation<SMProposition> {
    private Assembly assembly;
    private Consumer<SMProposition> updateCallback;

    public GuardAnnotation(SMProposition content, Assembly assembly, Consumer<SMProposition> updateCallback) {
        super(content);
        this.assembly = assembly;
        this.updateCallback = updateCallback;
    }

    @Override
    protected String buildDisplayText() {
        // Return the text with square brackets.
        return "[" + (content == null ? "" : content.toString()) + "]";
    }

    @Override
    protected void showPopup(MouseEvent e) {
        JPopupMenu popup = new JPopupMenu();

        if (content instanceof TrueProposition) {
            List list = assembly.getAssemblyGuards();
            if (list.isEmpty()) {
                JMenuItem none = new JMenuItem("Nessuna guardia disponibile");
                none.setEnabled(false);
                popup.add(none);
            } else {
                for (SMProposition guardOption : (List<SMProposition>) list) {
                    JMenuItem item = new JMenuItem(guardOption.toString());
                    item.addActionListener(ev -> {
                        setContent(guardOption);
                        updateCallback.accept(guardOption);
                        revalidate();
                        repaint();
                        if (getParent() != null) {
                            getParent().revalidate();
                            getParent().repaint();
                        }
                    });
                    popup.add(item);
                }
            }
        } else {
            JMenuItem removeItem = new JMenuItem("Rimuovi guardia");
            removeItem.addActionListener(ev -> {
                SMProposition defaultGuard = new TrueProposition();
                setContent(defaultGuard);
                updateCallback.accept(defaultGuard);
                repaint();
            });
            popup.add(removeItem);
        }
        popup.show(this, e.getX(), e.getY());
    }

//    @Override
//    protected void paintComponent(Graphics g) {
//        super.paintComponent(g);
//        Graphics2D g2d = (Graphics2D) g;
//        g2d.setFont(getFont().deriveFont(Font.PLAIN, 12f));
//        g2d.setColor(Color.BLACK);
//        String text = buildDisplayText();
//        FontMetrics fm = g2d.getFontMetrics();
//        int textWidth = fm.stringWidth(text);
//        int textHeight = fm.getAscent();
//        int x = (getWidth() - textWidth) / 2;
//        int y = (getHeight() + textHeight) / 2 - 2;
//        g2d.drawString(text, x, y);
//    }
}