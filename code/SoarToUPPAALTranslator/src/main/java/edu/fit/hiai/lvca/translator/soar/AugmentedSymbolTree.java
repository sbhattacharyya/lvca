package edu.fit.hiai.lvca.translator.soar;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;

public class AugmentedSymbolTree {
    private String name;
    private LinkedList<AugmentedEdge> edgeNameToEdge;

    public AugmentedSymbolTree(String _name) {
        name = _name;
        edgeNameToEdge = new LinkedList<>();
    }

    public String getName() { return name; }
    public void setName(String newName) { name = newName; }
    public LinkedList<AugmentedEdge> getEdgeNameToEdge() { return edgeNameToEdge; }

    public boolean isEmpty() { return edgeNameToEdge.size() == 0; }

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

    public boolean matches(AugmentedSymbolTree otherTree, Map<String, SymbolTree> productionVariableComparison) {
        //For each edge
        //If otherTree doesn't have edge
        //return false
        //Else, check that edge
        for (AugmentedEdge AE : edgeNameToEdge) {
            AugmentedEdge otherEdge = otherTree.findEdgeTop(AE.getName());
            if (otherEdge == null) {
                return false;
            } else {
                if (!AE.edgeMatches(otherEdge, productionVariableComparison)) {
                    return false;
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
