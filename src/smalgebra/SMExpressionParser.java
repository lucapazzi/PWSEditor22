// ================================
// File: SMExpressionParser.java
// ================================
package smalgebra;

import assembly.AssemblyInterface;

/**
 * A simple recursive-descent parser for SM expressions.
 *
 * Supported grammar (roughly):
 *
 *   expression ::= term ( "OR" term )*
 *   term       ::= factor ( "AND" factor )*
 *   factor     ::= "NOT" factor | primary
 *   primary    ::= basic | "(" expression ")"
 *   basic      ::= machineId "." stateName
 *
 * Machine identifiers and state names are assumed to be alphanumeric.
 */
public class SMExpressionParser {
    private final String input;
    private int pos;
    private final AssemblyInterface assembly; // Assembly against which machine IDs are validated

    /**
     * Constructs a parser with the given input and Assembly.
     *
     * @param input    the input expression
     * @param assembly the assembly used for validating machine identifiers
     */
    public SMExpressionParser(String input, AssemblyInterface assembly) {
        this.input = input;
        this.pos = 0;
        this.assembly = assembly;
    }

    /**
     * Parses the input expression and returns an SMProposition.
     *
     * @return the parsed SMProposition
     * @throws IllegalArgumentException if the expression is invalid or a machine identifier is not found
     */
    public SMProposition parse() {
        SMProposition proposition = parseExpression();
        skipWhitespace();
        if (pos < input.length()) {
            throw new IllegalArgumentException("Unexpected characters at end: " + input.substring(pos));
        }
        return proposition;
    }

    // expression ::= term ( "OR" term )*
    private SMProposition parseExpression() {
        SMProposition left = parseTerm();
        while (true) {
            skipWhitespace();
            if (match("OR")) {
                SMProposition right = parseTerm();
                left = new OrProposition(left, right);
            } else {
                break;
            }
        }
        return left;
    }

    // term ::= factor ( "AND" factor )*
    private SMProposition parseTerm() {
        SMProposition left = parseFactor();
        while (true) {
            skipWhitespace();
            if (match("AND")) {
                SMProposition right = parseFactor();
                left = new AndProposition(left, right);
            } else {
                break;
            }
        }
        return left;
    }

    // factor ::= "NOT" factor | primary
    private SMProposition parseFactor() {
        skipWhitespace();
        if (match("NOT")) {
            SMProposition proposition = parseFactor();
            return new NotProposition(proposition);
        } else {
            return parsePrimary();
        }
    }

    // primary ::= "(" expression ")" | constant | basic
    private SMProposition parsePrimary() {
        skipWhitespace();
        // Se troviamo "TRUE", restituiamo una TrueProposition
        if (match("TRUE")) {
            return new TrueProposition();
        }
        // Se troviamo "FALSE", restituiamo una FalseProposition
        if (match("FALSE")) {
            return new FalseProposition();
        }
        if (match("(")) {
            SMProposition proposition = parseExpression();
            skipWhitespace();
            if (!match(")")) {
                throw new IllegalArgumentException("Expected ')' at position " + pos);
            }
            return proposition;
        } else {
            return parseBasic();
        }
    }

    // basic ::= machineId "." stateName
    private SMProposition parseBasic() {
        skipWhitespace();
        String machineId = parseIdentifier();
        // Validate that the machine identifier exists in the provided assembly.
        if (assembly.getStateMachines().get(machineId) == null) {
            throw new IllegalArgumentException("Machine identifier '" + machineId + "' does not exist in the provided Assembly.");
        }
        skipWhitespace();
        if (!match(".")) {
            throw new IllegalArgumentException("Expected '.' at position " + pos);
        }
        skipWhitespace();
        String stateName = parseIdentifier();
        return new BasicStateProposition(machineId, stateName);
    }

    // Parse an identifier (machine id or state name); assume alphanumeric characters.
    private String parseIdentifier() {
        skipWhitespace();
        int start = pos;
        while (pos < input.length() && Character.isLetterOrDigit(input.charAt(pos))) {
            pos++;
        }
        if (start == pos) {
            throw new IllegalArgumentException("Expected identifier at position " + pos);
        }
        return input.substring(start, pos);
    }

    // Skip any whitespace characters.
    private void skipWhitespace() {
        while (pos < input.length() && Character.isWhitespace(input.charAt(pos))) {
            pos++;
        }
    }

    // If the input at the current position starts with token, consume it.
    private boolean match(String token) {
        skipWhitespace();
        if (input.startsWith(token, pos)) {
            pos += token.length();
            return true;
        }
        return false;
    }

    /**
     * A convenience static method to parse an SM expression from a string.
     * The provided Assembly is used to validate machine identifiers.
     *
     * @param expression the string expression to parse
     * @param assembly   the assembly used for validation
     * @return the resulting SMProposition
     */
    public static SMProposition parseExpression(String expression, AssemblyInterface assembly) {
        SMExpressionParser parser = new SMExpressionParser(expression, assembly);
        SMProposition proposition = parser.parse();
        return proposition;
    }
}