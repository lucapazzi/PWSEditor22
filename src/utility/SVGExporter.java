package utility;

import org.apache.batik.dom.GenericDOMImplementation;
import org.apache.batik.svggen.SVGGraphics2D;
import org.w3c.dom.DOMImplementation;
import org.w3c.dom.Document;
import javax.swing.*;
import java.awt.*;
import java.awt.datatransfer.StringSelection;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

public class SVGExporter {

    public static void exportPanelToSVG(JPanel panel) {
        // Existing method: export to clipboard (if needed)
        DOMImplementation domImpl = GenericDOMImplementation.getDOMImplementation();
        String svgNS = "http://www.w3.org/2000/svg";
        Document document = domImpl.createDocument(svgNS, "svg", null);
        SVGGraphics2D svgGenerator = new SVGGraphics2D(document);
        panel.print(svgGenerator);
        String svgContent;
        try {
            java.io.StringWriter writer = new java.io.StringWriter();
            svgGenerator.stream(writer, true);
            svgContent = writer.toString();
        } catch (IOException ex) {
            ex.printStackTrace();
            return;
        }
        StringSelection selection = new StringSelection(svgContent);
        Toolkit.getDefaultToolkit().getSystemClipboard().setContents(selection, null);
        JOptionPane.showMessageDialog(panel, "SVG esportato negli appunti.");
    }

    public static void exportPanelToSVGFile(JPanel panel, File file) {
        // Export the content of 'panel' to an SVG file.
        DOMImplementation domImpl = GenericDOMImplementation.getDOMImplementation();
        String svgNS = "http://www.w3.org/2000/svg";
        Document document = domImpl.createDocument(svgNS, "svg", null);
        SVGGraphics2D svgGenerator = new SVGGraphics2D(document);

        // Have the panel render its content to the SVG Graphics2D context.
        panel.print(svgGenerator);

        // Write the SVG content to the chosen file.
        try (FileWriter writer = new FileWriter(file)) {
            svgGenerator.stream(writer, true);
        } catch (IOException ex) {
            ex.printStackTrace();
            JOptionPane.showMessageDialog(panel, "Errore nel salvataggio del file SVG: " + ex.getMessage());
        }
    }
}