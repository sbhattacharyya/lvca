package edu.fit.hiai.lvca.translator.soar;

import java.util.HashSet;

/**
 * Created by Daniel Griessler Summer 2018
 * Data structure to store two sets of variables.  One set that are needed and one set are rejected.  There can be common terms between the two which are separated using "clean()"
 */

public class ProductionVariables {
    private final String productionName;
    private HashSet<String> variables;
    private HashSet<String> rejectedVariables;

    /**
     * Creates a new set of ProductionVariables using the provided name
     * @param _productionName Name of the production to which these variables belong
     */
    ProductionVariables(String _productionName) {
        productionName = _productionName;
        variables = new HashSet<>();
        rejectedVariables = new HashSet<>();
    }

    public HashSet<String> getVariables() { return variables; }

    public void addToVaribles(String variable) {
        variables.add(variable);
    }

    public void addToRejected(HashSet<String> moreRejectedVariables) {
        rejectedVariables.addAll(moreRejectedVariables);
    }

    public void addToRejected(String variable) {
        rejectedVariables.add(variable);
    }

    public boolean variablesContains(String variable) {
        return variables.contains(variable);
    }

    public boolean rejectedContains(String variable) { return rejectedVariables.contains(variable); }

    /**
     * Removes all the values that are rejectedVariables from the list of variables
     */
    public void clean() {
        for (String rejectedVariable : rejectedVariables) {
            if (variablesContains(rejectedVariable)) {
                variables.remove(rejectedVariable);
            }
        }
    }
}
