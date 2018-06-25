package edu.fit.hiai.lvca.translator.soar;


import java.util.LinkedList;
import java.util.Map;

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
            AST.collectAllBranchPaths(allBranchPaths, currentPath + "_" + name);
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

    public void makeIDsEdge(Map<String, String> variablesToPathWithID, Map<String, Integer> variableIDToIndex, Map<String, String> variablesToPath, ProductionVariables actualVariables) {
        for (AugmentedSymbolTree AST : values) {
            String variablePath = variablesToPath.get(AST.getName());
            if (variablePath != null && actualVariables.rejectedContains(AST.getName())) {
                Integer variableID = variableIDToIndex.get(variablePath);
                if (variableID == null) {
                    variableID = 1;
                    variableIDToIndex.put(variablePath, variableID);
                } else {
                    variableID++;
                }
                variablesToPathWithID.put(AST.getName(), variablePath + "_" + variableID);
            }
            AST.makeIDs(variablesToPathWithID, variableIDToIndex, variablesToPath, actualVariables);
        }
    }

    private AugmentedSymbolTree findAugmentedTreeTop(String augmentedTreeName) {
        for (AugmentedSymbolTree AST : values) {
            if (AST.getName().equals(augmentedTreeName)) {
                return AST;
            }
        }
        return null;
    }

    public boolean edgeMatches(AugmentedEdge otherEdge, Map<String, SymbolTree> productionVariableComparison) {
        for (AugmentedSymbolTree AST : values) {
            if (AST.getName().charAt(0) == '<') {
                SymbolTree tempTree = new SymbolTree(AST.getName());
                productionVariableComparison.put(AST.getName(), tempTree);
                for (AugmentedSymbolTree otherAST : otherEdge.getValues()) {
                    tempTree.addChild(new SymbolTree(otherAST.getName()));
                }
            } else {
                AugmentedSymbolTree otherAST = otherEdge.findAugmentedTreeTop(AST.getName());
                if (otherAST == null) {
                    return false;
                } else if (!AST.matches(otherAST, productionVariableComparison)) {
                    return false;
                }
            }
        }
        return true;
    }

    public boolean makeCountEdge(ASTCountWithValues currentEdge, boolean isUpdated) {
        for (AugmentedSymbolTree AST : values) {
            if (!currentEdge.containsValue(AST.getName()) && !isUpdated) {
                isUpdated = true;
            }
            currentEdge.addValue(AST.getName());
            AST.makeCount(currentEdge, isUpdated);
        }
        return isUpdated;
    }
}
