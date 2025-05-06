package pws.editor.annotation;

import javax.swing.*;
import java.awt.*;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.io.Serializable;

public class Annotation<T> extends JComponent implements Serializable {
    protected T content; // Generic content field.
    protected Point dragOffset;

    public Annotation(T content) {
        this.content = content;
//        setOpaque(true);
//        setBackground(Color.CYAN);
//        setBorder(BorderFactory.createLineBorder(Color.white, 1));

        MouseAdapter ma = new MouseAdapter() {
            @Override
            public void mousePressed(MouseEvent e) {
                if (e.isPopupTrigger()) {
                    showPopup(e);
                } else {
                    dragOffset = e.getPoint();
                }
            }
            @Override
            public void mouseReleased(MouseEvent e) {
                if (e.isPopupTrigger()) {
                    showPopup(e);
                }
                dragOffset = null;
            }
            @Override
            public void mouseDragged(MouseEvent e) {
                if (dragOffset != null && getParent() != null) {
                    Point parentPoint = SwingUtilities.convertPoint(Annotation.this, e.getPoint(), getParent());
                    setLocation(parentPoint.x - dragOffset.x, parentPoint.y - dragOffset.y);
                    getParent().repaint();
                }
            }
        };
        addMouseListener(ma);
        addMouseMotionListener(ma);
    }

    public T getContent() {
        return content;
    }

    public void setContent(T content) {
        this.content = content;
        // calls setSize(getPreferredSize()) after updating the content
        Dimension d = getPreferredSize();
        setSize(d);
        revalidate();
        repaint();
    }

    /**
     * Method to build the text for display.
     * Subclasses can override this to add extra formatting.
     */
    protected String buildDisplayText() {
        return (content == null ? "" : content.toString());
    }

    @Override
    public Dimension getPreferredSize() {
        // Ottieni il font attualmente impostato
        Font f = getFont();
        if (f == null) {
            // Se il font è null, fornisce un font di default.
            f = new Font("Dialog", Font.PLAIN, 12);
            setFont(f);
        }
        Font derived = f.deriveFont(Font.PLAIN, 12f);
        FontMetrics fm = getFontMetrics(derived);
        // Use buildDisplayText() instead of getContentAsString()
        int width = fm.stringWidth(buildDisplayText()) + 10;
        int height = fm.getHeight() + 10;
        return new Dimension(width, height);
    }

    // Default popup behavior: do nothing.
    protected void showPopup(MouseEvent e) {
        // No popup defined in base class.
    }

    @Override
    protected void paintComponent(Graphics g) {
        super.paintComponent(g);
        Graphics2D g2d = (Graphics2D) g;
        g2d.setFont(getFont().deriveFont(Font.PLAIN, 12f));
        g2d.setColor(Color.BLACK);
        String text = buildDisplayText();
        FontMetrics fm = g2d.getFontMetrics();
        int textWidth = fm.stringWidth(text);
        int textHeight = fm.getAscent();
        int x = (getWidth() - textWidth) / 2;
        int y = (getHeight() + textHeight) / 2 - 2;
        g2d.drawString(text, x, y);
    }
}