package utility;

import machinery.TransitionInterface;

import javax.swing.*;
import java.awt.*;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;

public class DraggableTriggerLabel extends JLabel {
    private Point initialClick;
    private TransitionInterface associatedTransition;

    // Constructor that associates this label with a transition.
    public DraggableTriggerLabel(String text, TransitionInterface associatedTransition) {
        // Use HTML to style as bold and underlined.
        super("<html><b><u>" + text + "</u></b></html>");
        setOpaque(false);  // Transparent background
        this.associatedTransition = associatedTransition;
        initDrag();
    }

    // Convenience constructor if no transition is provided.
    public DraggableTriggerLabel(String text) {
        this(text, null);
    }

    private void initDrag() {
        addMouseListener(new MouseAdapter() {
            @Override
            public void mousePressed(MouseEvent e) {
                initialClick = e.getPoint();
            }
        });
        addMouseMotionListener(new MouseAdapter() {
            @Override
            public void mouseDragged(MouseEvent e) {
                int thisX = getX();
                int thisY = getY();
                int xMoved = e.getX() - initialClick.x;
                int yMoved = e.getY() - initialClick.y;
                int newX = thisX + xMoved;
                int newY = thisY + yMoved;
                setLocation(newX, newY);
                // Update the associated transition's trigger offset, if available.
                if (associatedTransition != null) {
                    associatedTransition.setTriggerOffset(new Point(newX, newY));
                }
            }
        });
    }
}