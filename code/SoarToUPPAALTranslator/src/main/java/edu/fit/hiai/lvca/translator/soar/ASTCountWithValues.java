package edu.fit.hiai.lvca.translator.soar;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

public class ASTCountWithValues {
    private int numValues;
    private HashSet<String> values;
    private Map<String, ASTCountWithValues> edges;

    ASTCountWithValues() {
        numValues = 0;
        values = new HashSet<>();
        edges = new HashMap<>();
    }

    ASTCountWithValues(String headValue) {
        this();
        values.add(headValue);
    }

    public int getNumValues() { return numValues; }

    public boolean containsValue (String value) { return values.contains(value); }
    public boolean containsEdge (String edge) { return edges.get(edge) != null; }

    public void addValue(String newValue) {
        if (!values.contains(newValue)) {
            numValues++;
        }
        if (!newValue.startsWith("<")) {
            values.add(newValue);
        }
    }

    public ASTCountWithValues addEdge(String edgeName) {
        if (edges.get(edgeName) != null) {
            return edges.get(edgeName);
        } else {
            ASTCountWithValues newEdge = new ASTCountWithValues();
            edges.put(edgeName, newEdge);
            return newEdge;
        }
    }
}
