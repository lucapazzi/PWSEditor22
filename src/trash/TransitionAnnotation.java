package trash;

import javax.swing.*;
import java.awt.*;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;

public class TransitionAnnotation extends JComponent {
    private String annotationText;
    private Point dragOffset;

    public TransitionAnnotation(String text) {
        this.annotationText = text;
        // Make the component non-opaque so that its background doesn't obscure other graphics.
        setOpaque(false);
        // Add mouse listeners for dragging and for showing a popup menu.
        MouseAdapter ma = new MouseAdapter() {
            @Override
            public void mousePressed(MouseEvent e) {
                // If right-click, show popup for modifying annotation.
                if (SwingUtilities.isRightMouseButton(e)) {
                    showPopup(e);
                } else {
                    dragOffset = e.getPoint();
                }
            }
            @Override
            public void mouseDragged(MouseEvent e) {
                if (dragOffset != null) {
                    Point parentPoint = SwingUtilities.convertPoint(TransitionAnnotation.this, e.getPoint(), getParent());
                    setLocation(parentPoint.x - dragOffset.x, parentPoint.y - dragOffset.y);
                    // Repaint parent so connecting lines update.
                    if(getParent()!=null){
                        getParent().repaint();
                    }
                }
            }
            @Override
            public void mouseReleased(MouseEvent e) {
                dragOffset = null;
            }
        };
        addMouseListener(ma);
        addMouseMotionListener(ma);
    }

    public void setAnnotationText(String text) {
        this.annotationText = text;
        repaint();
    }

    public String getAnnotationText() {
        return annotationText;
    }

    @Override
    protected void paintComponent(Graphics g) {
        super.paintComponent(g);
        // Draw the annotation text centered in this component.
        Graphics2D g2d = (Graphics2D) g;
        g2d.setFont(getFont().deriveFont(Font.PLAIN, 12f));
        g2d.setColor(Color.BLACK);
        FontMetrics fm = g2d.getFontMetrics();
        int textWidth = fm.stringWidth(annotationText);
        int textHeight = fm.getAscent();
        int x = (getWidth() - textWidth) / 2;
        int y = (getHeight() + textHeight) / 2 - 2;
        g2d.drawString(annotationText, x, y);
    }

    private void showPopup(MouseEvent e) {
        JPopupMenu popup = new JPopupMenu();
        JMenuItem modifyItem = new JMenuItem("Modify annotation");
        modifyItem.addActionListener(ev -> {
            String newText = JOptionPane.showInputDialog(TransitionAnnotation.this, "Modify annotation text:", annotationText);
            if (newText != null) {
                setAnnotationText(newText);
                // Here you might also update the associated PWSTransition data if needed.
            }
        });
        popup.add(modifyItem);
        popup.show(this, e.getX(), e.getY());
    }
}