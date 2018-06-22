package edu.fit.hiai.lvca.translator.soar;


import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;

public class AugmentedEdge {
    private String name;
    private LinkedList<AugmentedSymbolTree> values;

    public AugmentedEdge(String _name) {
        name = _name;
        values = new LinkedList<>();
    }

    public String getName() { return name; }
    public LinkedList<AugmentedSymbolTree> getValues() { return values; }

    public AugmentedEdge(String _name, LinkedList<AugmentedSymbolTree> _values) {
        this(_name);
        values = _values;
    }

    public AugmentedEdge addValues(LinkedList<String> newValues) {
        for (String nextValue : newValues) {
            values.add(new AugmentedSymbolTree(nextValue));
        }
        return this;
    }

    public AugmentedSymbolTree addSingleValue(String value) {
        AugmentedSymbolTree AST = new AugmentedSymbolTree(value);
        values.add(AST);
        return AST;
    }

    public void addAugmentedTree(AugmentedSymbolTree AST) {
        values.add(AST);
    }

    public void collectAllPaths(LinkedList<String> allBranchPaths, String currentPath) {
        for (AugmentedSymbolTree AST : values) {
            AST.collectAllBranchPathsUtility(allBranchPaths, currentPath + "_" + name);
        }
    }

    public AugmentedSymbolTree findAugmentedTree(String treeName) {
        for (AugmentedSymbolTree AST : values) {
            AugmentedSymbolTree possibleTree = AST.findTree(treeName);
            if (possibleTree != null) {
                return possibleTree;
            }
        }
        return null;
    }

    public void cleanAndJoinEdge(AugmentedEdge newAttributeEdge, String productionName, LinkedList<Integer> takenValues) {
        for (AugmentedSymbolTree AST : values) {
            try {
                takenValues.add(Integer.parseInt(AST.getName()));
            } catch (NumberFormatException e) {}
            AugmentedSymbolTree newAttributeSymbolTree = newAttributeEdge.findAugmentedTree(AST.getName());
            if (newAttributeSymbolTree == null) {
                newAttributeEdge.addAugmentedTree(AST);
            } else {
                AST.cleanAndJoin(newAttributeSymbolTree, productionName, takenValues);
            }
        }
    }
}
