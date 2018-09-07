package edu.fit.hiai.lvca.translator.soar;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;

/**
 * Created by Daniel Griessler Summer 2018
 * Structure used to store the collection of all the productions and variables of the productions that were stored in AugmentedSymbolTrees and AugmentedEdges
 * Allows for easy creation of AV templates later on
 */

public class ASTCountWithValues {
    private int numValues;
    private HashSet<String> values;
    private Map<String, ASTCountWithValues> edges;

    /**
     * Creates a new ASTCountWithValues with initially no values or edges
     */
    ASTCountWithValues() {
        numValues = 0;
        values = new HashSet<>();
        edges = new HashMap<>();
    }

    /**
     * Creates a new ASTCountWithValues with the provided name
     * @param headValue Name of the new ASTCountWithValues
     */
    ASTCountWithValues(String headValue) {
        this();
        values.add(headValue);
    }

    /**
     * Returns all of the names of the edges in a LinkedList
     * @return A LinkedList with all the names of the edges
     */
    public LinkedList<String> getEdges() {
        LinkedList<String> topEdges = new LinkedList<>();
        for (Map.Entry<String, ASTCountWithValues> nextEdge : edges.entrySet()) {
            topEdges.add(nextEdge.getKey());
        }
        return topEdges;
    }

    public boolean containsValue (String value) { return values.contains(value); }
    public boolean containsEdge (String edge) { return edges.get(edge) != null; }

    /**
     * Adds the new value into the list if its not a variable.  Also increments number of values if values doesn't have the value already
     * @param newValue Value to be added
     */
    public void addValue(String newValue) {
        if (!values.contains(newValue)) {
            numValues++;
        }
        // Checking if the newValue is a variable
        if (!newValue.startsWith("<")) {
            values.add(newValue);
        }
    }

    /**
     * Adds a new edge with the given name unless it already exists
     * @param edgeName Name of new edge
     * @return The newly created edge or the edge that already exists with that name
     */
    public ASTCountWithValues addEdge(String edgeName) {
        if (edges.get(edgeName) != null) {
            return edges.get(edgeName);
        } else {
            ASTCountWithValues newEdge = new ASTCountWithValues();
            edges.put(edgeName, newEdge);
            return newEdge;
        }
    }

    private boolean isHead() { return numValues == 0 && values.size() > 0;}
    private String getHeadValue() { return (String)values.toArray()[0]; }

    /**
     * Collects the individual ASTCountWithValues into global structure
     * @param variablesToPath Maps between variable name and their path with ID
     * @param condensedAttributesValueCount Global structure that is collecting the values. Map from variable to its ASTCountWithValues
     * @param currentASTCountWithValues Current ASTCountWithValues in condensedAttributesValueCount. Is first provided as null
     */
    public void collectEdges(Map<String, String> variablesToPath, Map<String, ASTCountWithValues> condensedAttributesValueCount, ASTCountWithValues currentASTCountWithValues) {
        if (isHead()) {
            String firstValue = getHeadValue();
            String simplifiedFirstVariable = variablesToPath.get(firstValue);
            currentASTCountWithValues = condensedAttributesValueCount.get(simplifiedFirstVariable);
            // State is going to be assigned to -1, that's why it is state_-1.  It's just a signal that it's the state
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
            // numValues can be different than how many values are actually in there because:
            // numValues goes up every time a value is added that isn't in values
            // variables are never added to values
            currentASTCountWithValues.numValues += numValues - values.size();
        }

        for (String edgeName : edges.keySet()) {
            String simplifiedEdgeName = SoarTranslator.simplifiedString(edgeName);
            if (!currentASTCountWithValues.containsEdge(simplifiedEdgeName)) {
                ASTCountWithValues newEdge = new ASTCountWithValues();
                currentASTCountWithValues.edges.put(simplifiedEdgeName, newEdge);
                edges.get(edgeName).collectEdges(variablesToPath, condensedAttributesValueCount, newEdge);
            } else {
                edges.get(edgeName).collectEdges(variablesToPath, condensedAttributesValueCount, currentASTCountWithValues.edges.get(simplifiedEdgeName));
            }
        }
    }

    /**
     * Converts the ASTCountWithValues into UppaalAttributeValueTriad that can be used quickly and easily in UppaalSemanticVisitor to create the corresponding AV templates
     * Only thing that Uppaal has to know is what identifier is it, what attribute is it, and what is the maximum number of values that the attribute will have during run time
     * @param AVCollection LinkedList of UppaalAttributeValueTriad that are created from ASTCountWithValues
     * @param currentTriad Current UppaalAttributeValueTriad that is being added to. First provided as null
     */
    public void createAVCollection(LinkedList<UppaalAttributeValueTriad> AVCollection, UppaalAttributeValueTriad currentTriad) {
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
            edges.get(edgeName).createAVCollection(AVCollection, currentTriad);
            currentTriad.setName(temp);
        }
    }

    /**
     * Auxiliary method used in applyStateMatchesEdge in Augmented Edge to copy all the values held by the ASTCountWithValues with the name of the 1st element of the array
     * to the ASTCountWithValues with the name of the 2nd element of the array
     * @param attributes Provided by applyStateMatchesEdge.  The 1st element is the name of the ASTCountWithValues to be copied. The 2nd element is the name of the ASTCountWithValues
     *                   to be copied to
     */
    public void copyValues(String[] attributes) {
        HashSet<String> attribute1Values = edges.get(attributes[0]).values;
        attribute1Values.forEach(av -> edges.get(attributes[1]).addValue(av));
    }
}
