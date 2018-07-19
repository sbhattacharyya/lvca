package edu.fit.hiai.lvca.translator.soar;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
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
    public int getNumEdges() { return edges.size(); }

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

    public boolean isHead() { return numValues == 0 && values.size() > 0;}
    public String getHeadValue() { return (String)values.toArray()[0]; }

    public void collectEdges(Map<String, String> variablesToPath, Map<String, ASTCountWithValues> condensedAttributesValueCount, ASTCountWithValues currentASTCountWithValues, HashSet<String> attributes) {
        if (isHead()) {
            String firstValue = getHeadValue();
            String simplifiedFirstVariable = variablesToPath.get(firstValue);
            currentASTCountWithValues = condensedAttributesValueCount.get(simplifiedFirstVariable);
            if (currentASTCountWithValues == null || !simplifiedFirstVariable.equals("state_-1")) {
                currentASTCountWithValues = new ASTCountWithValues(simplifiedFirstVariable);
                condensedAttributesValueCount.put(simplifiedFirstVariable, currentASTCountWithValues);
            }
        } else {
            for (String nextValue : values) {
                if (!currentASTCountWithValues.containsValue(nextValue)) {
                    currentASTCountWithValues.addValue(nextValue);
                }
            }
            currentASTCountWithValues.numValues += numValues - values.size();
        }

        for (String edgeName : edges.keySet()) {
            String simplifiedEdgeName = SoarTranslator.simplifiedString(edgeName);
            attributes.add(simplifiedEdgeName);
            if (!currentASTCountWithValues.containsEdge(simplifiedEdgeName)) {
                ASTCountWithValues newEdge = new ASTCountWithValues();
                currentASTCountWithValues.edges.put(simplifiedEdgeName, newEdge);
                edges.get(edgeName).collectEdges(variablesToPath, condensedAttributesValueCount, newEdge,attributes);
            } else {
                edges.get(edgeName).collectEdges(variablesToPath, condensedAttributesValueCount, currentASTCountWithValues.edges.get(simplifiedEdgeName), attributes);
            }
        }
    }

    public void createAVCollection(LinkedList<UppaalAttributeValueTriad> AVCollection, UppaalAttributeValueTriad currentTriad, Map<String, Integer> attributesToIDs) {
        if (isHead()) {
            String variableNameWithID = getHeadValue();
            int lastUnderscoreIndex = variableNameWithID.lastIndexOf('_');
            int operatorIndex = Integer.parseInt(variableNameWithID.substring(lastUnderscoreIndex + 1));
            if (operatorIndex == -1) {
                variableNameWithID = variableNameWithID.substring(0, lastUnderscoreIndex) + "_1";
            }
            currentTriad = new UppaalAttributeValueTriad(variableNameWithID, variableNameWithID.equals("state_1") ? "_state" : variableNameWithID);
        } else {
            String AVName = "AV_" + currentTriad.getName();
            AVCollection.add(new UppaalAttributeValueTriad(AVName, numValues, currentTriad.getAttributeIndex(), currentTriad.getOperatorIndex()));
        }

        for (String edgeName : edges.keySet()) {
            currentTriad.setAttributeIndex(edgeName);
            String temp = currentTriad.getName();
            currentTriad.setName(currentTriad.getName() + "_" + edgeName);
            edges.get(edgeName).createAVCollection(AVCollection, currentTriad, attributesToIDs);
            currentTriad.setName(temp);
        }
    }

    public void copyValues(String[] attributes) {
        HashSet<String> attribute1Values = edges.get(attributes[0]).values;
        attribute1Values.forEach(av -> edges.get(attributes[1]).addValue(av));
    }
}
