package edu.fit.hiai.lvca.translator.soar;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;

/**
 * Created by Daniel Griessler Summer 2018
 * Augmented version of the SymbolTree which includes names on the edges connecting the tree of AugmentedSymbolTree
 * Also includes extra restrictions used for when trying to match this AugmentedSymbolTree with another one in the SoarTranslator
 * Works closely with AugmentedEdge
 */

public class AugmentedSymbolTree {


    private String name;
    private LinkedList<AugmentedEdge> edgeNameToEdge;
    private SymbolTree extraRestrictions;

    /**
     * Creates a new AugmentedSymbolTree with the given name
     * @param _name Name of the AugmentedSymbolTree
     */
    public AugmentedSymbolTree(String _name) {
        name = _name;
        edgeNameToEdge = new LinkedList<>();
        // extraRestrictions starts as null so that it saves space on the majority of AugmentedSymbolTrees which don't have extra restrictions
        extraRestrictions = null;
    }

    public String getName() { return name; }
    public void setName(String newName) { name = newName; }
    public LinkedList<AugmentedEdge> getEdgeNameToEdge() { return edgeNameToEdge; }

    /**
     * Checks if there are any edges coming out of this AugmentedSymbolTree
     * @return If there are any edges
     */
    public boolean isEmpty() { return edgeNameToEdge.size() == 0; }

    /**
     * Adds the restrictions in the provided SymbolTree to our SymbolTree if they aren't already in the tree
     * @param restrictions SymbolTree containing the restrictions
     */
    public void addToRestrictions(SymbolTree restrictions) {
        if (extraRestrictions == null) {
            extraRestrictions = new SymbolTree("restrictions");
        }
        if (restrictions.getChildren().size() == 0 && extraRestrictions.DFS(restrictions.name) == null) {
            extraRestrictions.addChild(restrictions);
        }
        for (SymbolTree nextRestriction : restrictions.getChildren()) {
            SymbolTree restrictionBranch = extraRestrictions.DFS(nextRestriction.name);
            if (restrictionBranch == null) {
                restrictionBranch = new SymbolTree(nextRestriction.name);
                extraRestrictions.addChild(restrictionBranch);
            }
            for (SymbolTree nextValue : nextRestriction.getChildren()) {
                SymbolTree valueBranch = restrictionBranch.DFS(nextValue.name);
                if (valueBranch == null) {
                    valueBranch = new SymbolTree(nextValue.name);
                    restrictionBranch.addChild(valueBranch);
                }
            }
        }
    }

    /**
     * Searches the AugmentedSymbolTrees which are the values of the mapping provided to find if any contain an AugmentedSymbolTree with the provided name
     * Uses findTree to do a recursive search through each AugmentedSymbolTree
     * @param productionVariablesToTrees Mapping between a String and an AugmentedSymbolTree where the AugmentedSymbolTree will be searched
     * @param treeName Name of the tree to be found
     * @return If an AugmentedSymbolTree with the given tree name exists in the provided AugmentedSymbolTree
     */
    public boolean recursiveSearch(Map<String, AugmentedSymbolTree> productionVariablesToTrees, String treeName) {
        for (Map.Entry<String, AugmentedSymbolTree> variableAndSymbolTree : productionVariablesToTrees.entrySet()) {
            if (variableAndSymbolTree.getKey().equals(treeName) || variableAndSymbolTree.getValue().findTree(treeName) != null) {
                return true;
            }
        }
        return false;
    }

    /**
     * Works with findAugmentedTree in AugmentedEdge to do a full recursive search of the AugmentedSymbolTree looking for the provided tree name
     * @param treeName Name of the tree to be found
     * @return If a tree exists with the given tree name, otherwise null
     */
    public AugmentedSymbolTree findTree(String treeName) {
        if (name.equals(treeName)) {
            return this;
        } else {
            for (AugmentedEdge AE : edgeNameToEdge) {
                AugmentedSymbolTree possibleTree = AE.findAugmentedTree(treeName);
                if (possibleTree != null) {
                    return possibleTree;
                }
            }
        }
        return null;
    }

    /**
     * Very similar to contains, but it actually returns the edge with the given edgeName or null if not found
     * @param edgeName Edge name to be found
     * @return AugmentedEdge with the given edge name or null if not found
     */
    private AugmentedEdge findEdge(String edgeName) {
        for (AugmentedEdge AE : edgeNameToEdge) {
            if (AE.getName().equals(edgeName)) {
                return AE;
            }
        }
        return null;
    }

    /**
     * Adds a new edge with the provided edge name unless we already have an edge with the provided name
     * @param edgeName Name of the edge to be found or added
     * @return Edge that was either found or just added
     */
    public AugmentedEdge addEdgeWithoutValues(String edgeName) {
        AugmentedEdge AE = findEdge(edgeName);
        if (AE == null) {
            AE = new AugmentedEdge(edgeName);
            edgeNameToEdge.add(AE);
        }
        return AE;
    }

    /**
     * Works with the makeIDsEdge in AugmentedEdge to fill variablesToPathWithID with a mapping between the variable and its original path and its ID used for Uppaal
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
    public void makeIDs(HashSet<Integer> takenValues, Map<String, String> variablesToPathWithID, Map<String, Integer> variableIDToIndex, Map<String, String> variablesToPath, ProductionVariables actualVariables, LinkedList<String> variableNames, Map<String, Boolean> seenVariables) {
        for (AugmentedEdge AE : edgeNameToEdge) {
            AE.makeIDsEdge(takenValues, variablesToPathWithID, variableIDToIndex, variablesToPath, actualVariables, variableNames, seenVariables);
        }
    }

    /**
     * Checks if all of the edges and values in this AugmentedSymbolTree are equal, or at least have corresponding parts, to to the ones in the other provided AugmentedSymbolTree
     * @param otherTree Other AugmentedSymbolTree to be compared to this one
     * @param productionVariableComparison Mapping from values found here and those in the otherTree that will need to checked later to see if they match
     * @param attributeVariableToDisjunctionTest Mapping from an attribute value to its list of possible values that it has to be equal to
     * @return If this AugmentedSymbolTree and the otherTree have all matching edges and values or at least have a possible match stored in productionVariableComparison
     */
    public boolean matches(AugmentedSymbolTree otherTree, Map<String, SymbolTree> productionVariableComparison, Map<String, String[]> attributeVariableToDisjunctionTest) {
        //For each edge
            //If the Edge is a variable
                //If the variable is an attribute with a corresponding list in the attributeVariableToDisjunctionTest
                    //Check for all of the possible values
                //Else
                    //Check any of the possible matches
                //If the edge doesn't at least possibly match with one of the edges in the other tree
                    //Return false
            //Else
                // check that edge
                //If that edge doesn't exist in the otherTree or doesn't match
                    //Return false
        //If it got through everything, return true
        for (AugmentedEdge AE : edgeNameToEdge) {
            AugmentedEdge otherEdge;
            if (AE.getName().charAt(0) == '<') {
                boolean atLeastOneMatches = false;
                if (attributeVariableToDisjunctionTest.get(AE.getName()) != null) {
                    String[] possibleMatches = attributeVariableToDisjunctionTest.get(AE.getName());
                    for (String possibleMatch : possibleMatches) {
                        otherEdge = otherTree.findEdge(possibleMatch);
                        if (otherEdge != null && AE.edgeMatches(otherEdge, productionVariableComparison, attributeVariableToDisjunctionTest)) {
                            atLeastOneMatches = true;
                        }
                    }
                } else {
                    SymbolTree actualMatches = new SymbolTree(AE.getName());
                    for (SymbolTree possibleMatch : productionVariableComparison.get(AE.getName()).getChildren()) {
                        otherEdge = otherTree.findEdge(possibleMatch.name);
                        if (otherEdge != null && AE.edgeMatches(otherEdge, productionVariableComparison, attributeVariableToDisjunctionTest)) {
                            atLeastOneMatches = true;
                            actualMatches.addChild(possibleMatch);
                        }
                    }
                    if (actualMatches.getChildren().size() == 0) {
                        actualMatches = null;
                    }
                    productionVariableComparison.put(AE.getName(), actualMatches);
                }
                if (!atLeastOneMatches) {
                    return false;
                }
            } else {
                otherEdge = otherTree.findEdge(AE.getName());
                if (otherEdge == null || !AE.edgeMatches(otherEdge, productionVariableComparison, attributeVariableToDisjunctionTest)) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * Utility for makeCount which notes if a new edge is added and calls makeEdgeCount in AugmentedEdge to continue
     * @param currentTree ASTCountWithValues that represents the full collection of all the separated AugmentedSymbolTrees across all of the productions.
     * @param isUpdated Boolean value that keeps track if anything is actually added to the currentTree
     * @param attributeVariableToDisjunctionTest Mapping from an attribute value to its list of possible values that it has to be equal to
     * @param edgeName Name of the edge to be checked and added
     * @param AE Current AugmentedEdge
     * @return If a new edge is added to currentTree
     */
    private boolean makeCountUtility(ASTCountWithValues currentTree, boolean isUpdated, Map<String, String[]> attributeVariableToDisjunctionTest, String edgeName, AugmentedEdge AE) {
        if (!currentTree.containsEdge(edgeName) && !isUpdated) {
            isUpdated = true;
        }
        ASTCountWithValues currentEdge = currentTree.addEdge(edgeName);
        AE.makeCountEdge(currentEdge, isUpdated, attributeVariableToDisjunctionTest);
        return isUpdated;
    }

    /**
     * Collects and condenses edges and values from this AugmentedSymbolTree into the provided currentTree which is an ASTCountWithValues
     * @param currentTree ASTCountWithValues that represents the full collection of all the separated AugmentedSymbolTrees across all of the productions.
     * @param isUpdated Boolean value that keeps track if anything is actually added to the currentTree
     * @param attributeVariableToDisjunctionTest Mapping from an attribute value to its list of possible values that it has to be equal to
     * @return isUpdated.  It should first be provided as false and if something is added during the course of the method then it will be changed to true
     */
    public boolean makeCount(ASTCountWithValues currentTree, boolean isUpdated, Map<String, String[]> attributeVariableToDisjunctionTest) {
        for (AugmentedEdge AE : edgeNameToEdge) {
            String[] possibleMatches = attributeVariableToDisjunctionTest.get(AE.getName());
            if (possibleMatches != null) {
                for (String nextMatch : possibleMatches) {
                    isUpdated = makeCountUtility(currentTree, isUpdated, attributeVariableToDisjunctionTest, nextMatch, AE);
                }
            } else {
                isUpdated = makeCountUtility(currentTree, isUpdated, attributeVariableToDisjunctionTest, AE.getName(), AE);
            }
        }
        return isUpdated;
    }

    /**
     * This method covers when a state is copying values from one edge to another edge it already has.  I don't know which value it will copy so this goes through and copies all
     * of the values between the two edges
     * Recursive matching using applyStateMatchesEdge in AugmentedEdge
     * @param attributesAndValuesState Collected ASTCountWithValues that collects all of the attribute and value information about the state between all of the productions
     * @param stateAttributesAndValuesForCheck AugmentedSymbolTree that is being checked
     * @param level Recursive search depends on this being provided as starting at 1
     * @param attributesMatch Keeps track of which edges are matching so that when the level gets down far enough we don't have to try and retrieve it
     * @param attributeMatchIndex Index for attributesMatch to know where to add values.  Search depends on this being provided as 0
     */
    public void applyStateMatches(ASTCountWithValues attributesAndValuesState, AugmentedSymbolTree stateAttributesAndValuesForCheck, int level, String[] attributesMatch, int attributeMatchIndex) {
        for (AugmentedEdge AE : edgeNameToEdge) {
            attributesMatch[attributeMatchIndex] = AE.getName();
            AE.applyStateMatchesEdge(attributesAndValuesState, stateAttributesAndValuesForCheck, level + 1, attributesMatch, attributeMatchIndex + 1);
        }
    }
}
