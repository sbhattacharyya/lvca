package edu.fit.hiai.lvca.translator.soar;


import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;

/**
 * Created by Daniel Griessler Summer 2018
 * Edge connecting AugmentedSymbolTrees together.  It is called AucmentedEdge because it includes a name on the edge
 */

public class AugmentedEdge {
    private String name;
    private LinkedList<AugmentedSymbolTree> values;

    /**
     * Creates a new AugmentedEdge with the given name
     * @param _name Name of the new AugmentedEdge
     */
    public AugmentedEdge(String _name) {
        name = _name;
        values = new LinkedList<>();
    }

    public String getName() { return name; }
    public LinkedList<AugmentedSymbolTree> getValues() { return values; }

    /**
     * Adds new AugmentedSymbolTree with the given name to its list.  Allows duplicates
     * @param value Name of new AugmentedSymboLTree to be added
     * @return Newly added AugmentedSymbolTree
     */
    public AugmentedSymbolTree addSingleValue(String value) {
        AugmentedSymbolTree AST = new AugmentedSymbolTree(value);
        values.add(AST);
        return AST;
    }

    /**
     * Recursive search using findTree inside AugmentedSymbolTree to check if the structure contains an AugmentedSymbolTree with the provided name
     * @param treeName Name of the AugmentedSymbolTree to be found
     * @return The AugmentedSymbolTree that matches the  treeName if found, otherwise null
     */
    public AugmentedSymbolTree findAugmentedTree(String treeName) {
        for (AugmentedSymbolTree AST : values) {
            AugmentedSymbolTree possibleTree = AST.findTree(treeName);
            if (possibleTree != null) {
                return possibleTree;
            }
        }
        return null;
    }

    /**
     * Works with makeIDs in AugmentedSymbolTree to fill variablesToPathWithID with a mapping between the variable and its original path and its ID used for Uppaal
     * @param takenValues List of constants that are reserved by Soar and can't be used by Uppaal (assumed to all be positive right now)
     * @param variablesToPathWithID Mapping between a variable and its path which includes its ID on the end
     * @param variableIDToIndex Mapping between a variable and its most recent ID which starts from 1 and increases if other variables have the same path
     * @param variablesToPath Mapping between a variable and its path without ID
     * @param actualVariables ProductionVariables which keeps track of which variables are actual variables and which are identifiers later on
     * @param variableNames List of variable paths with ID.
     *                      VariablesToPathWithID will eventually be buried under another mapping with productions and its easier to loop over if I have a second list
     *                      It is a duplicate though, so if space is an issue this parameter can be removed
     * @param seenVariables Mapping between variable and boolean that indicates if I have seen it before.  I don't want to give two different IDs to the same variable in one production
     */
    public void makeIDsEdge(HashSet<Integer> takenValues, Map<String, String> variablesToPathWithID, Map<String, Integer> variableIDToIndex, Map<String, String> variablesToPath, ProductionVariables actualVariables, LinkedList<String> variableNames, Map<String, Boolean> seenVariables) {
        for (AugmentedSymbolTree AST : values) {
            try {
                takenValues.add(Integer.parseInt(AST.getName()));
            } catch(NumberFormatException e) {}
            String variablePath = variablesToPath.get(AST.getName());
            if (variablePath != null && actualVariables.variablesContains(AST.getName()) && seenVariables.get(AST.getName()) == null) {
                Integer variableID = variableIDToIndex.get(variablePath);
                if (variableID == null) {
                    variableID = 1;
                } else {
                    variableID++;
                }
                variableIDToIndex.put(variablePath, variableID);
                String name = variablePath + "_" + variableID;
                variablesToPathWithID.put(AST.getName(), name);
                variableNames.add(name);
                seenVariables.put(AST.getName(), true);
            }
            AST.makeIDs(takenValues, variablesToPathWithID, variableIDToIndex, variablesToPath, actualVariables, variableNames, seenVariables);
        }
    }

    /**
     * Similar to findAugmentedTree except it only searches this edge's list of AugmentedSymbolTrees instead of a full recursive search
     * @param augmentedTreeName Name of the AugmentedSymbolTree to be found
     * @return Either the AugmentedSymbolTree if found, otherwise null
     */
    public AugmentedSymbolTree findAugmentedTreeTop(String augmentedTreeName) {
        for (AugmentedSymbolTree AST : values) {
            if (AST.getName().equals(augmentedTreeName)) {
                return AST;
            }
        }
        return null;
    }

    /**
     * Checks if all of the edges and values in this AugmentedEdge are equal, or at least have corresponding parts, to to the ones in the other provided AugmentedEdge
     * @param otherEdge Other AugmentedEdge to be compared to this one
     * @param productionVariableComparison Mapping from values found here and those in the otherEdge that will need to checked later to see if they match
     * @param attributeVariableToDisjunctionTest Mapping from an attribute value to its list of possible values that it has to be equal to
     * @return If this AugmentedEdge and the otherEdge have all matching values and edges or at least have a possible match stored in productionVariableComparison
     */
    public boolean edgeMatches(AugmentedEdge otherEdge, Map<String, SymbolTree> productionVariableComparison, Map<String, String[]> attributeVariableToDisjunctionTest) {
        //For each AugmentedSymbolTree
            //If the AugmentedSymbolTree is a variable
                //Add it to the productionVariableComparison with its corresponding tree
                //For each of the otherEdge's AugmentedSymbolTrees
                    //Add them as possible matches to be checked later
            //Else
                // check that AugmentedSymbolTree
                    //If that edge doesn't exist in the otherTree or doesn't match
                        //Return false
        //If it got through everything, return true
        for (AugmentedSymbolTree AST : values) {
            if (AST.getName().charAt(0) == '<') {
                SymbolTree tempTree = new SymbolTree(AST.getName());
                productionVariableComparison.put(AST.getName(), tempTree);
                for (AugmentedSymbolTree otherAST : otherEdge.getValues()) {
                    tempTree.addChild(new SymbolTree(otherAST.getName()));
                }
            } else {
                AugmentedSymbolTree otherAST = otherEdge.findAugmentedTreeTop(AST.getName());
                if (otherAST == null || !AST.matches(otherAST, productionVariableComparison, attributeVariableToDisjunctionTest)) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * Collects and condenses edges and values from this AugmentedEdge into the provided currentTree which is an ASTCountWithValues
     * @param currentEdge ASTCountWithValues that represents the full collection of all the separated AugmentedSymbolTrees across all of the productions.
     * @param isUpdated Boolean value that keeps track if anything is actually added to the currentTree
     * @param attributeVariableToDisjunctionTest Mapping from an attribute value to its list of possible values that it has to be equal to
     * @return isUpdated.  It should first be provided as false and if something is added during the course of the method then it will be changed to true
     */
    public boolean makeCountEdge(ASTCountWithValues currentEdge, boolean isUpdated, Map<String, String[]> attributeVariableToDisjunctionTest) {
        for (AugmentedSymbolTree AST : values) {
            if (!currentEdge.containsValue(AST.getName()) && !isUpdated) {
                isUpdated = true;
            }
            String[] additionalValues = attributeVariableToDisjunctionTest.get(AST.getName());
            if (additionalValues != null) {
                for (String nextValue : additionalValues) {
                    currentEdge.addValue(nextValue);
                }
            } else {
                currentEdge.addValue(AST.getName());
            }
            AST.makeCount(currentEdge, isUpdated, attributeVariableToDisjunctionTest);
        }
        return isUpdated;
    }

    /**
     * This method covers when a state is copying values from one edge to another edge it already has.  I don't know which value it will copy so this goes through and copies all
     * of the values between the two edges
     * Recursive matching using applyStateMatches in AugmentedSymbolTree
     * @param attributesAndValuesState Collected ASTCountWithValues that collects all of the attribute and value information about the state between all of the productions
     * @param stateAttributesAndValuesForCheck AugmentedSymbolTree that is being checked
     * @param level Recursive search depends on this being provided as starting at 1
     * @param attributesMatch Keeps track of which edges are matching so that when the level gets down far enough we don't have to try and retrieve it
     * @param attributeMatchIndex Index for attributesMatch to know where to add values.  Search depends on this being provided as 0
     */
    public void applyStateMatchesEdge(ASTCountWithValues attributesAndValuesState, AugmentedSymbolTree stateAttributesAndValuesForCheck, int level, String[] attributesMatch, int attributeMatchIndex) {
        for (AugmentedSymbolTree AST : values) {
            // Level goes to 4 because the structure is attribute -> value for both attributesAndValuesState as well as stateAttributesAndValuesForCheck
            // So level 1 is selecting attribute, level 2 is getting value, level 3 is getting the other attribute, level 4 is copying the values between the attributes
            if (level == 4 && AST.getName().equals(stateAttributesAndValuesForCheck.getName())) {
                attributesAndValuesState.copyValues(attributesMatch);
            } else {
                stateAttributesAndValuesForCheck.applyStateMatches(attributesAndValuesState, AST, level + 1, attributesMatch, attributeMatchIndex);
            }
        }
    }

}
