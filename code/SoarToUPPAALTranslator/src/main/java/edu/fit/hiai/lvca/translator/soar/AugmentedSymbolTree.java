package edu.fit.hiai.lvca.translator.soar;

import sun.awt.Symbol;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;

public class AugmentedSymbolTree {


    private String name;
    private LinkedList<AugmentedEdge> edgeNameToEdge;
    private SymbolTree extraRestrictions;

    public AugmentedSymbolTree(String _name) {
        name = _name;
        edgeNameToEdge = new LinkedList<>();
        extraRestrictions = null;
    }

    public String getName() { return name; }
    public void setName(String newName) { name = newName; }
    public LinkedList<AugmentedEdge> getEdgeNameToEdge() { return edgeNameToEdge; }

    public boolean isEmpty() { return edgeNameToEdge.size() == 0; }

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

    public boolean resursiveSearch(Map<String, AugmentedSymbolTree> productionVariablesToTrees, String treeName) {
        for (Map.Entry<String, AugmentedSymbolTree> variableAndSymbolTree : productionVariablesToTrees.entrySet()) {
            if (variableAndSymbolTree.getKey().equals(treeName) || variableAndSymbolTree.getValue().findTree(treeName) != null) {
                return true;
            }
        }
        return false;
    }

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

    public AugmentedEdge findEdge(String edgeName) {
        for (AugmentedEdge AE : edgeNameToEdge) {
            if (AE.getName().equals(edgeName)) {
                return AE;
            }
        }
        return null;
    }

    public AugmentedEdge addEdge(AugmentedEdge edge) {
        AugmentedEdge AE = findEdge(edge.getName());
        if (AE == null) {
            edgeNameToEdge.add(edge);
            AE = edge;
        }
        return AE;
    }

    public AugmentedEdge addEdgeWithoutValues(String edgeName) {
        AugmentedEdge AE = findEdge(edgeName);
        if (AE == null) {
            AE = new AugmentedEdge(edgeName);
            edgeNameToEdge.add(AE);
        }
        return AE;
    }

    public void makeIDs(HashSet<Integer> takenValues, Map<String, String> variablesToPathWithID, Map<String, Integer> variableIDToIndex, Map<String, String> variablesToPath, ProductionVariables actualVariables, LinkedList<String> variableNames) {
        for (AugmentedEdge AE : edgeNameToEdge) {
            AE.makeIDsEdge(takenValues, variablesToPathWithID, variableIDToIndex, variablesToPath, actualVariables, variableNames);
        }
    }

    private AugmentedEdge findEdgeTop(String edgeName) {
        for (AugmentedEdge AE : edgeNameToEdge) {
            if (AE.getName().equals(edgeName)) {
                return AE;
            }
        }
        return null;
    }

    public boolean matches(AugmentedSymbolTree otherTree, Map<String, SymbolTree> productionVariableComparison, Map<String, String[]> attributeVariableToDisjunctionTest, Map<String, String> currentAttributeValueToSelection) {
        //For each edge
        //If otherTree doesn't have edge
        //return false
        //Else, check that edge
        for (AugmentedEdge AE : edgeNameToEdge) {
            AugmentedEdge otherEdge;
            if (AE.getName().charAt(0) == '<') {
                boolean atLeastOneMatches = false;
                if (attributeVariableToDisjunctionTest.get(AE.getName()) != null) {
                    String[] possibleMatches = attributeVariableToDisjunctionTest.get(AE.getName());
                    for (String possibleMatch : possibleMatches) {
                        otherEdge = otherTree.findEdgeTop(possibleMatch);
                        if (otherEdge != null && AE.edgeMatches(otherEdge, productionVariableComparison, attributeVariableToDisjunctionTest, currentAttributeValueToSelection)) {
                            atLeastOneMatches = true;
                        }
                    }
                } else {
                    for (SymbolTree possibleMatch : productionVariableComparison.get(AE.getName()).getChildren()) {
                        otherEdge = otherTree.findEdgeTop(possibleMatch.name);
                        if (otherEdge != null && AE.edgeMatches(otherEdge, productionVariableComparison, attributeVariableToDisjunctionTest, currentAttributeValueToSelection)) {
                            atLeastOneMatches = true;
                        }
                    }
                }
                if (!atLeastOneMatches) {
                    return false;
                }
//                if (attributeVariableToDisjunctionTest.get(AE.getName()) != null && currentAttributeValueToSelection.get(AE.getName()) == null) {
//                    int index = 0;
//                    String value = "";
//                    boolean checkOtherValues;
//                    do {
//                        for (int i = index; i < attributeVariableToDisjunctionTest.get(AE.getName()).length; i++) {
//                            value = attributeVariableToDisjunctionTest.get(AE.getName())[i];
//                            otherEdge = otherTree.findEdgeTop(value);
//                            index = i;
//                            if (otherEdge != null) {
//                                break;
//                            }
//                        }
//                        if (index == attributeVariableToDisjunctionTest.get(AE.getName()).length - 1 && otherEdge == null) {
//                            return false;
//                        }
//                        currentAttributeValueToSelection.put(AE.getName(), value);
//                        checkOtherValues = !AE.edgeMatches(otherEdge, productionVariableComparison, attributeVariableToDisjunctionTest, currentAttributeValueToSelection);
//                    } while (checkOtherValues);
//                } else {
//                    if (currentAttributeValueToSelection.get(AE.getName()) != null) {
//                        otherEdge = otherTree.findEdgeTop(currentAttributeValueToSelection.get(AE.getName()));
//                    } else {
//                        otherEdge = otherTree.edgeNameToEdge.get(0);
//                        currentAttributeValueToSelection.put(AE.getName(), otherEdge.getName());
//                    }
//                    if (otherEdge == null) {
//                        return false;
//                    } else {
//                        if (!AE.edgeMatches(otherEdge, productionVariableComparison, attributeVariableToDisjunctionTest, currentAttributeValueToSelection)) {
//                            return false;
//                        }
//                    }
//                }
            } else {
                otherEdge = otherTree.findEdgeTop(AE.getName());
                if (otherEdge == null) {
                    return false;
                } else {
                    if (!AE.edgeMatches(otherEdge, productionVariableComparison, attributeVariableToDisjunctionTest, currentAttributeValueToSelection)) {
                        return false;
                    }
                }
            }
        }
        return true;
    }

    public boolean makeCount(ASTCountWithValues currentTree, boolean isUpdated) {
        for (AugmentedEdge AE : edgeNameToEdge) {
            if (!currentTree.containsEdge(AE.getName()) && !isUpdated) {
                isUpdated = true;
            }
            ASTCountWithValues currentEdge = currentTree.addEdge(AE.getName());
            AE.makeCountEdge(currentEdge, isUpdated);
        }
        return isUpdated;
    }
}
