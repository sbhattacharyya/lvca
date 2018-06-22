package edu.fit.hiai.lvca.translator.soar;

import java.util.LinkedList;

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

    public void collectAllBranchPathsUtility(LinkedList<String> allBranchPaths, String currentPath) {
        for (AugmentedEdge AE : edgeNameToEdge) {
            AE.collectAllPaths(allBranchPaths, currentPath);
        }
        if (!currentPath.equals("state")) {
            allBranchPaths.add(currentPath);
        }
    }

    public LinkedList<String> collectAllBranchPaths() {
        LinkedList<String> allBranchPaths = new LinkedList<>();
        collectAllBranchPathsUtility(allBranchPaths, "state");
        return allBranchPaths;
    }

    public void cleanAndJoin(AugmentedSymbolTree newAttributeTree, String productionName, LinkedList<Integer> takenValues) {
        for (AugmentedEdge AE : edgeNameToEdge) {
            AugmentedEdge newAttributeEdge = newAttributeTree.findEdge(AE.getName());
            if (newAttributeEdge == null && !AE.getName().equals("operator")) {
                newAttributeTree.addEdge(AE);
            } else if (AE.getName().equals("operator")) {
                AugmentedEdge newOperatorEdge = new AugmentedEdge(productionName, AE.getValues());
                newAttributeTree.addEdge(newOperatorEdge);
            } else {
                AE.cleanAndJoinEdge(newAttributeEdge, productionName, takenValues);
            }
        }
    }
}
