package edu.fit.hiai.lvca.translator.soar;


import java.util.HashSet;
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

    public AugmentedSymbolTree findAugmentedTree(String treeName) {
        for (AugmentedSymbolTree AST : values) {
            AugmentedSymbolTree possibleTree = AST.findTree(treeName);
            if (possibleTree != null) {
                return possibleTree;
            }
        }
        return null;
    }

    public void makeIDsEdge(HashSet<Integer> takenValues, Map<String, String> variablesToPathWithID, Map<String, Integer> variableIDToIndex, Map<String, String> variablesToPath, ProductionVariables actualVariables, LinkedList<String> variableNames) {
        for (AugmentedSymbolTree AST : values) {
            try {
                takenValues.add(Integer.parseInt(AST.getName()));
            } catch(NumberFormatException e) {}
            String variablePath = variablesToPath.get(AST.getName());
            if (variablePath != null && actualVariables.variablesContains(AST.getName())) {
                Integer variableID = variableIDToIndex.get(variablePath);
                if (variableID == null) {
                    variableID = 1;
                    variableIDToIndex.put(variablePath, variableID);
                } else {
                    variableID++;
                }
                String name = variablePath + "_" + variableID;
                variablesToPathWithID.put(AST.getName(), name);
                variableNames.add(name);
            }
            AST.makeIDs(takenValues, variablesToPathWithID, variableIDToIndex, variablesToPath, actualVariables, variableNames);
        }
    }

    public AugmentedSymbolTree findAugmentedTreeTop(String augmentedTreeName) {
        for (AugmentedSymbolTree AST : values) {
            if (AST.getName().equals(augmentedTreeName)) {
                return AST;
            }
        }
        return null;
    }

    public boolean edgeMatches(AugmentedEdge otherEdge, Map<String, SymbolTree> productionVariableComparison, Map<String, String[]> attributeVariableToDisjunctionTest, Map<String, String> currentAttributeValueToSelection) {
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
                } else if (!AST.matches(otherAST, productionVariableComparison, attributeVariableToDisjunctionTest, currentAttributeValueToSelection)) {
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
