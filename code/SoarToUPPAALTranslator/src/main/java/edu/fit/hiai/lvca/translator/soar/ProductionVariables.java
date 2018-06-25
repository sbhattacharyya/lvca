package edu.fit.hiai.lvca.translator.soar;

import java.util.HashSet;

public class ProductionVariables {
    private final String productionName;
    private HashSet<String> variables;
    private HashSet<String> rejectedVariables;
    ProductionVariables(String _productionName) {
        productionName = _productionName;
        variables = new HashSet<>();
        rejectedVariables = new HashSet<>();
    }

    public void addToVaribles(String variable) {
        variables.add(variable);
    }

    public void addToRejected(String variable) {
        rejectedVariables.add(variable);
    }

    public boolean variablesContains(String variable) {
        return variables.contains(variable);
    }

    public boolean rejectedContains(String variable) { return rejectedVariables.contains(variable); }

    public void clean() {
        for (String rejectedVariable : rejectedVariables) {
            if (variablesContains(rejectedVariable)) {
                variables.remove(rejectedVariable);
            }
        }
    }
}
