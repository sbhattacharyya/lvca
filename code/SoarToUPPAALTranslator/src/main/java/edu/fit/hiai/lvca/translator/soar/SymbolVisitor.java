package edu.fit.hiai.lvca.translator.soar;

import edu.fit.hiai.lvca.antlr4.SoarBaseVisitor;
import edu.fit.hiai.lvca.antlr4.SoarParser;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.RuleContext;
import org.antlr.v4.runtime.tree.ParseTree;
import sun.awt.Symbol;

import java.util.*;
import java.util.stream.Collectors;


/**
 * Created by mstafford on 8/4/16.
 *
 * Get all symbols and working memory locations used in the Soar agent. This class produces a single SymbolTree that
 * variablesContains all memory locations used by the Soar agent. Each variable's working memory association is stored. Each
 * string written is stored.
 *
 */
class SymbolVisitor extends SoarBaseVisitor<SymbolTree>
{
    private int operatorCount = 0;
    private Set<String> stringSymbols = new HashSet<>();
    private Set<String> booleanSymbols = new HashSet<>();
    private SymbolTree workingMemoryTree = new SymbolTree("state");
    private Map<String, String> currentVariableDictionary;
    private Set<String> nestedVariableNames = new HashSet<>();
    private Map<String, Map<String, String>> globalVariableDictionary = new HashMap<>();
    private Map<String, Map<String, AugmentedSymbolTree>> attributesAndValuesPerProduction = new HashMap<>();
    private Map<String, AugmentedSymbolTree> productionVariablesToTrees;
    private Map<String, Map<String, AugmentedSymbolTree>> checkAttributesAndValuesPerProduction = new HashMap<>();
    private Map<String, AugmentedSymbolTree> checkProductionVariablesToTrees;
    private Map<String, Map<String, AugmentedSymbolTree>> updateAttributesAndValuesPerProduction = new HashMap<>();
    private Map<String, AugmentedSymbolTree> updateProductionVariablesToTrees;
    private AugmentedSymbolTree productionSource;
    private AugmentedEdge currentBranchInAttributesAndValues;
    private Map<String, LinkedList<String>> variableHierarchy = new HashMap<>();
    private LinkedList<String> currentPlaceInVariableHierarchy;
    private int addLocation;
    private boolean unaryOrBinaryFlag = false;
    private Map<String, ProductionVariables> actualVariablesInProduction = new HashMap<>();
    private ProductionVariables currentVariablesPerProduction;
    private Map<String, ProductionVariables> variablesCreatedOrUpdated = new HashMap<>();
    private ProductionVariables currentVariablesCreatedOrUpdated;
    private boolean isProductionOSupported;
    private String stateVariable;
    private int maxQuerySize = 0;
    private int currentMaxQuerySize;
    private Map<String, Boolean> productionToOSupported = new HashMap<>();
    private Map<String, String[]> arrayNameToDisjunctionTest = new HashMap<>();
    private Map<String, String> attributeVariableToArrayName = new HashMap<>();
    private boolean onAttribute;

    /**
     * Entry point for parsing, get all literal strings, values, and working memory locations used.
     * @param ctx
     */
    public SymbolVisitor(SoarParser.SoarContext ctx)
    {
        // This call also updates stringSymbols, workingMemoryTree, and booleanSymbols
        ctx.accept(this); // Call for side effects
    }

    Set<String> getStringSymbols()
    {
        return stringSymbols;
    }

    SymbolTree getTree()
    {
        return workingMemoryTree;
    }

    public Map<String, Map<String, AugmentedSymbolTree>> getAttributesAndValuesPerProduction() {
        return attributesAndValuesPerProduction;
    }

    public Map<String, Map<String, AugmentedSymbolTree>> getCheckAttributesAndValuesPerProduction() {
        return checkAttributesAndValuesPerProduction;
    }

    public Map<String, Map<String, AugmentedSymbolTree>> getUpdateAttributesAndValuesPerProduction() {
        return updateAttributesAndValuesPerProduction;
    }

    public Map<String, LinkedList<String>> getVariableHierarchy() {
        return variableHierarchy;
    }

    Set<String> getBooleanSymbols()
    {
        return booleanSymbols;
    }

    Map<String, Map<String, String>> getGlobalVariableDictionary()
    {
        return globalVariableDictionary;
    }

    Map<String, ProductionVariables> getActualVariablesInProduction() { return actualVariablesInProduction; }

    public Map<String, ProductionVariables> getVariablesCreatedOrUpdated() { return variablesCreatedOrUpdated; }

    public int getMaxQuerySize() { return maxQuerySize; }

    int getOperatorCount() { return operatorCount; }

    public Map<String, Boolean> getProductionToOSupported() { return productionToOSupported; }

    public Map<String, String[]> getAttributeVariableToDisjunctionTest()
    {
        Map<String, String[]> attributeVariableToDisjunctionTest = new HashMap<>();
        for (Map.Entry<String, String> attributeVariableToArrayName : attributeVariableToArrayName.entrySet()) {
            attributeVariableToDisjunctionTest.put(attributeVariableToArrayName.getKey(), arrayNameToDisjunctionTest.get(attributeVariableToArrayName.getValue()));
        }
        return attributeVariableToDisjunctionTest;
    }

    /**
     * Update the global dictionary of (Soar Production) -> (Variable) -> (Working Memory Path)
     * The global dictionary keeps track of all Soar variable associations
     *
     * @param ctx
     * @return
     */
    @Override
    public SymbolTree visitSoar_production(SoarParser.Soar_productionContext ctx)
    {
        productionVariablesToTrees = new HashMap<>();
        attributesAndValuesPerProduction.put(ctx.sym_constant().getText(), productionVariablesToTrees);

        checkProductionVariablesToTrees = new HashMap<>();
        checkAttributesAndValuesPerProduction.put(ctx.sym_constant().getText(), checkProductionVariablesToTrees);

        updateProductionVariablesToTrees = new HashMap<>();
        updateAttributesAndValuesPerProduction.put(ctx.sym_constant().getText(), updateProductionVariablesToTrees);

        addLocation = 0;
        currentPlaceInVariableHierarchy = new LinkedList<>();
        variableHierarchy.put(ctx.sym_constant().getText(), currentPlaceInVariableHierarchy);

        currentVariablesPerProduction = new ProductionVariables(ctx.sym_constant().getText());
        currentVariablesCreatedOrUpdated = new ProductionVariables(ctx.sym_constant().getText());
        currentVariableDictionary = new HashMap<>();
        isProductionOSupported = false;

        currentMaxQuerySize = 0;
        ctx.condition_side().accept(this);
        ctx.action_side().accept(this);
        maxQuerySize = Math.max(maxQuerySize, currentMaxQuerySize);

        // globalVariableDictionary: production name -> variable id -> variable path

        Map<String, String> variablePaths = new HashMap<>();

        for (HashMap.Entry<String, String> entry : currentVariableDictionary.entrySet())
        {
            variablePaths.put(entry.getKey(), workingMemoryTree.pathTo(entry.getValue()));
        }
        currentVariablesPerProduction.clean();
        actualVariablesInProduction.put(ctx.sym_constant().getText(), currentVariablesPerProduction);

        currentVariablesCreatedOrUpdated.addToRejected(currentVariablesPerProduction.getVariables());
        currentVariablesCreatedOrUpdated.clean();
        variablesCreatedOrUpdated.put(ctx.sym_constant().getText(), currentVariablesCreatedOrUpdated);

        for (int i = 0 ; i < currentPlaceInVariableHierarchy.size(); i++) {
            String variable = currentPlaceInVariableHierarchy.get(i);
            if (currentVariablesPerProduction.variablesContains(variable) || (currentVariableDictionary.get(variable) != null && currentVariableDictionary.get(variable).contains("operator"))) {
                currentPlaceInVariableHierarchy.remove(i);
                i--;
            }
        }

        globalVariableDictionary.put(ctx.sym_constant().getText(), variablePaths);
        productionToOSupported.put(ctx.sym_constant().getText(), isProductionOSupported);
        return null;
    }

    private void setMappingAndSource(String variable, Map<String, AugmentedSymbolTree> map, String treePath) {
        if (map.get(variable) == null) {
            map.put(variable, new AugmentedSymbolTree(treePath));
        }
        productionSource = map.get(variable);
    }

    /**
     * Establish "state" as the root of the working tree with the first variable (usually <s>). Update the working
     * memory with specified attributes.
     *
     * @param ctx
     * @return
     */
    @Override
    public SymbolTree visitState_imp_cond(SoarParser.State_imp_condContext ctx)
    {
        currentVariableDictionary.put(ctx.id_test().getText(), workingMemoryTree.name);

        //State is always updated, at least right now
        currentVariablesCreatedOrUpdated.addToRejected(ctx.id_test().getText());

        setMappingAndSource(ctx.id_test().getText(), checkProductionVariablesToTrees, "state");
        stateVariable = ctx.id_test().getText();

        currentPlaceInVariableHierarchy.add(addLocation++, ctx.id_test().getText());

        // Call for Side Effects
        for (SoarParser.Attr_value_testsContext attr_value_testsContext : ctx.attr_value_tests()) {
            SymbolTree child = attr_value_testsContext.accept(this);
            //gets tree without children
            child = child.getChildren().get(0);
            workingMemoryTree.addChild(child);
        }

        productionSource = null;

        return null;
    }

    @Override
    public SymbolTree visitPositive_cond(SoarParser.Positive_condContext ctx)
    {
        if (ctx.conds_for_one_id() != null) {
            ctx.conds_for_one_id().accept(this);
        } else {
            for (SoarParser.CondContext condContext : ctx.cond()) {
                condContext.accept(this);
            }
        }
        return null;
    }

    /**
     * Based on the variable that starts the Soar condition, store the attributes in the expression.
     *
     * E.g. Given (<o> ^name myop), where <o> points to <s> ^operator, connect the pieces to produce a tree including
     * state, operator, and name as a SymbolTree.
     *
     * @param ctx
     * @return
     */
    @Override
    public SymbolTree visitConds_for_one_id(SoarParser.Conds_for_one_idContext ctx)
    {
        SymbolTree attachPoint = ctx.id_test().accept(this);
        if (currentVariablesPerProduction.variablesContains(ctx.id_test().getText())) {
            currentVariablesPerProduction.addToRejected(ctx.id_test().getText());
        }

        if (currentVariableDictionary.get(ctx.id_test().getText()).equals("state")) {
            addLocation = currentPlaceInVariableHierarchy.size();
        } else {
            addLocation = currentPlaceInVariableHierarchy.indexOf(ctx.id_test().getText()) + 1;
        }

        if (!currentVariableDictionary.get(ctx.id_test().getText()).contains("operator")) {
            setMappingAndSource(ctx.id_test().getText(), checkProductionVariablesToTrees, currentVariableDictionary.get(ctx.id_test().getText()));
        }

        for(SoarParser.Attr_value_testsContext avt : ctx.attr_value_tests())
        {
            SymbolTree child = avt.accept(this);
            if (!child.getChildren().get(0).name.equals("withChildren")) {
                child = child.getChildren().get(0);
            } else {
                child = child.getChildren().get(1);
            }
            attachPoint.addChild(child);
            workingMemoryTree.addChild(child);
        }

        productionSource = null;

        return null;
    }

    private String addAttributeVariableToArrayName(SymbolTree attribute) {
        SymbolTree disjunctionBranch = attribute.DFS("disjunctionArray").getChildren().get(0);
        SymbolTree variableBranch = attribute.DFS("variable").getChildren().get(0);
        attributeVariableToArrayName.put(variableBranch.name, disjunctionBranch.name);
        return variableBranch.name;
    }

    private SymbolTree addAttributeToSubtrees(SymbolTree subtree, SymbolTree subtreeWithChildren, String text) {
        if (subtree == null) {
            subtree = new SymbolTree(text);
        } else {
            subtree.addChild(new SymbolTree(text));
        }
        subtreeWithChildren.addChild(new SymbolTree(text));
        return subtree;
    }

    /**
     * Determine the associations for the variable dictionary.
     *
     * E.g. given (<s> ^operator <o>) save the mapping of <o> to ^operator
     *
     * @param ctx
     * @return
     */
    @Override
    public SymbolTree visitAttr_value_tests(SoarParser.Attr_value_testsContext ctx)
    {
        boolean conditionIsNegated = ctx.getText().charAt(0) == '-';
        //The attribute or list of attributes following the caret. This SymbolTree therefore has no branching
        SymbolTree subtree = null;
        SymbolTree subtreeWithChildren = new SymbolTree("withChildren");

        onAttribute = true;
        for (SoarParser.Attr_testContext attr_testContext : ctx.attr_test()) {
            currentMaxQuerySize++;
            SymbolTree attribute = attr_testContext.accept(this);
            String attributeName = attr_testContext.getText();
            if (productionSource != null) {
                if (attr_testContext.getText().equals("operator")) {
                    currentBranchInAttributesAndValues = null;
                    subtree = addAttributeToSubtrees(subtree, subtreeWithChildren, attributeName);
                    break;
                } else {
                    if (attr_testContext.test().conjunctive_test() != null) {
                        String variableName = addAttributeVariableToArrayName(attribute);
                        currentBranchInAttributesAndValues = productionSource.addEdgeWithoutValues(variableName);
                        attributeName = variableName;
                    } else {
                        subtreeWithChildren.addChild(new SymbolTree(attr_testContext.getText()));
                        currentBranchInAttributesAndValues = productionSource.addEdgeWithoutValues(attribute.name);
                    }
                }
            } else if (attr_testContext.test().conjunctive_test() != null) {
                addAttributeVariableToArrayName(attribute);
            }
            subtree = addAttributeToSubtrees(subtree, subtreeWithChildren, attributeName);
        }
        onAttribute = false;

        if (productionSource != null && currentBranchInAttributesAndValues != null && ctx.value_test().size() == 0) {
            currentBranchInAttributesAndValues.addSingleValue("$EMPTY");
        }

        // Global is changed as a side effect of next line
        nestedVariableNames.clear();
        // Called for side effects
        for (SoarParser.Value_testContext value_testContext : ctx.value_test()) {
            SymbolTree child = value_testContext.accept(this);
            if (child.DFS("relation") != null) {
                SymbolTree variable = child.DFS("variable").getChildren().get(0);
                SymbolTree relations = child.DFS("relation");
                if (productionSource != null) {
                    currentBranchInAttributesAndValues.findAugmentedTree(variable.name).addToRestrictions(relations);
                }
                variable.addChild(relations);
                child = new SymbolTree("multiple");
                child.addChild(variable);
            }
            if (conditionIsNegated) {
                SymbolTree variable = child.DFS("variable");
                if (variable == null) {
                    variable = child;
                } else {
                    variable = variable.getChildren().get(0);
                }
                currentBranchInAttributesAndValues.findAugmentedTree(variable.name).addToRestrictions(new SymbolTree("NEGATED"));
            }
            if (child != null && !subtree.name.equals("operator")) {
                subtreeWithChildren.getChildren().get(0).addChild(child);
            }
        }

        for (String nestedVariableName : nestedVariableNames)
        {
            if (!currentVariableDictionary.containsKey(nestedVariableName))
            {
                // getFirstLeaf() because subtree is really a LinkedList and we want the last element
                currentVariableDictionary.put(nestedVariableName, getFirstLeaf(subtree));
            }
        }

        // this is for translation to Uppaal, which is probably irrelevant at this particular step
        if (ctx.value_test().size() > 0 &&
                (  ctx.value_test(0).getText().equals("true")
                || ctx.value_test(0).getText().equals("false")))
        {
            booleanSymbols.add(subtree.name);
        }
        SymbolTree returnTree = new SymbolTree("pickTheTree");
        returnTree.addChild(subtree);
        returnTree.addChild(subtreeWithChildren);
        if (!isProductionOSupported) {
            isProductionOSupported = ctx.attr_test().stream().map(RuleContext::getText).collect(Collectors.joining("_")).contains("operator");
        }
        return returnTree;
    }

    @Override
    public SymbolTree visitConjunctive_test(SoarParser.Conjunctive_testContext ctx)
    {
        SymbolTree multipleConditions = new SymbolTree("multiple");
        for (SoarParser.Simple_testContext simple_testContext : ctx.simple_test()) {
            if (simple_testContext.relational_test() == null || (simple_testContext.relational_test() != null && simple_testContext.relational_test().relation() == null)) {
                SymbolTree simpleTest = simple_testContext.accept(this);
                SymbolTree disjunctionArray = multipleConditions.getSubtreeNoError("disjunctionArray");
                if (simpleTest.name.startsWith("array")) {
                    if (disjunctionArray == null) {
                        disjunctionArray = new SymbolTree("disjunctionArray");
                        multipleConditions.addChild(disjunctionArray);
                    }
                    disjunctionArray.addChild(simpleTest);
                } else {
                    if (simple_testContext.getText().charAt(0) == '<' && simple_testContext.getText().charAt(simple_testContext.getText().length() - 1) == '>') {
                        SymbolTree variable = new SymbolTree("variable");
                        variable.addChild(new SymbolTree(simple_testContext.getText()));
                        multipleConditions.addChild(variable);
                    }
                }
            } else {
                SymbolTree relationBranch = multipleConditions.DFS("relation");
                if (relationBranch == null) {
                    relationBranch = new SymbolTree("relation");
                    multipleConditions.addChild(relationBranch);
                }
                SymbolTree relation = simple_testContext.relational_test().relation().accept(this);
                relation.addChild(new SymbolTree(simple_testContext.relational_test().single_test().getText()));
                relationBranch.addChild(relation);
            }
        }
        return multipleConditions;
    }


    @Override
    public SymbolTree visitDisjunction_test(SoarParser.Disjunction_testContext ctx)
    {
        String[] notAllBut = new String[ctx.constant().size()];
        for (int i = 0; i < ctx.constant().size(); i++) {
            ctx.constant(i).accept(this);
            notAllBut[i] = ctx.constant(i).getText();
        }
        int latestIndex = 1;
        boolean contains = false;
        for (Map.Entry<String, String[]> stringEntry : arrayNameToDisjunctionTest.entrySet()) {
            int nextIndex = Integer.parseInt(stringEntry.getKey().substring(stringEntry.getKey().lastIndexOf('_') + 1));
            if (stringEntry.getValue().equals(notAllBut)) {
                latestIndex = nextIndex;
                contains = true;
                break;
            } else {
                latestIndex = Math.max(latestIndex, nextIndex + 1);
            }
        }
        String arrayName = "array_" + latestIndex;
        if (!contains) {
            arrayNameToDisjunctionTest.put(arrayName, notAllBut);
        }
        return new SymbolTree(arrayName);
    }


    @Override
    public SymbolTree visitRelational_test(SoarParser.Relational_testContext ctx)
    {
        SymbolTree returnTree;
        SymbolTree singleTest = ctx.single_test().accept(this);

        if (ctx.relation() != null) {
            returnTree = ctx.relation().accept(this);
            returnTree.addChild(singleTest);
        } else {
            returnTree = singleTest;
        }

        return returnTree;
    }


    @Override
    public SymbolTree visitRelation(SoarParser.RelationContext ctx)
    {
        String relationText;
        switch(ctx.getText()) {
            case "<>": relationText = "isNotEqualTo";
                       break;
            case "<": relationText = "isLessThan";
                      break;
            case ">": relationText = "isGreaterThan";
                      break;
            case "<=": relationText = "isLessThanOrEqualTo";
                       break;
            case ">=": relationText = "isGreaterThanOrEqualTo";
                       break;
            case "<=>": relationText = "isSameTypeAs";
                        break;
            default:
                relationText = null;
                break;
        }
        SymbolTree returnTree;
        if (relationText != null) {
            returnTree = new SymbolTree(relationText);
        } else {
            returnTree = null;
        }
        return returnTree;
    }


    @Override public SymbolTree visitSingle_test(SoarParser.Single_testContext ctx) {
        String value;
        if (ctx.variable() != null) {
            ctx.variable().accept(this);
            value = ctx.variable().getText();
            if (!currentPlaceInVariableHierarchy.contains(value)) {
                currentPlaceInVariableHierarchy.add(addLocation++, value);
            }
            currentVariablesCreatedOrUpdated.addToRejected(value);
        } else {
            ctx.constant().accept(this);
            value = ctx.constant().getText();
        }
        if (productionSource != null && currentBranchInAttributesAndValues != null && !onAttribute) {
            currentBranchInAttributesAndValues.addSingleValue(value);
        }
        return new SymbolTree(value);
    }


    /**
     * Supports visitAttr_value_tests() method, takes the SymbolTree and returns the first leaf node it finds.
     *call
     * @param subtree
     * @return
     */
    private String getFirstLeaf(SymbolTree subtree)
    {
        SymbolTree t = subtree;
        while (t.getChildren().size() > 0)
        {
            t = t.getChildren().get(0);
        }
        return t.name;
    }

    /**
     * Supports visitAttr_value_tests() method, produces a SymbolTree representation of attributes written using the dot
     * notation. This tree will have no branching, like that of a LinkedList.
     *
     * E.g. (<s> ^operator.name bob) becomes [operator -- name]
     *
     * @param ctxs
     * @return
     */
    private SymbolTree getTreeFromList(List<? extends ParserRuleContext> ctxs)
    {
        if (ctxs.size() == 1)
        {
            return new SymbolTree(ctxs.get(0).getText());
        }
        else
        {
            SymbolTree t = new SymbolTree(ctxs.get(0).getText());
            t.addChild(getTreeFromList(ctxs.subList(1, ctxs.size())));
            return t;
        }
    }

    /**
     * If a variable is being defined, we want to store it in nestedVariable name for updating the variable
     * dictionary by higher context.  If the variable is already defined and being used here, we should return the
     * associated attribute.
     *
     * @param ctx
     * @return
     */
    @Override
    public SymbolTree visitVariable(SoarParser.VariableContext ctx)
    {
        nestedVariableNames.add(ctx.getText());
        String variableName = currentVariableDictionary.get(ctx.getText());
        currentVariablesPerProduction.addToVaribles(ctx.getText());
        if (variableName != null)
        {
            return workingMemoryTree.getSubtree(variableName);
        }
        return null;
    }

    /**
     * Save constants as singleton SymbolTrees for higher contexts
     *
     * @param ctx
     * @return
     */
    @Override
    public SymbolTree visitConstant(SoarParser.ConstantContext ctx)
    {
        String result = ctx.getText();

        if (ctx.sym_constant() != null)
        {
            stringSymbols.add(ctx.getText());
        }
        else if (ctx.Print_string() != null)
        {
            // Literal Strings in Soar are surrounded by vertical bars
            //This is dumb
            result = UPPAALSemanticVisitor.LITERAL_STRING_PREFIX + ctx.Print_string().getText().split("|")[1];
            stringSymbols.add(result);
        }

        return new SymbolTree(result);
    }

    /**
     * Track changes to working memory, update the SymbolTree
     *
     * @param ctx
     * @return
     */
    @Override
    public SymbolTree visitAction(SoarParser.ActionContext ctx)
    {
        if (ctx.attr_value_make() != null && ctx.variable() != null)
        {
            SymbolTree attachPoint = ctx.variable().accept(this);
            if (currentVariablesPerProduction.variablesContains(ctx.variable().getText())) {
                currentVariablesPerProduction.addToRejected(ctx.variable().getText());
            }

            if (attachPoint == null)
            {
                System.err.printf("Translation Error: Soar variable %s in production %s is not defined.\n",
                        ctx.variable().getText(),
                        ((SoarParser.Soar_productionContext)ctx.parent.parent).sym_constant().getText());
                System.exit(1);
            }

            if (attachPoint.name.equals("state") || (productionVariablesToTrees.get(stateVariable) != null && productionVariablesToTrees.get(stateVariable).resursiveSearch(productionVariablesToTrees, ctx.variable().getText()))) {
                setMappingAndSource(ctx.variable().getText(), productionVariablesToTrees, currentVariableDictionary.get(ctx.variable().getText()));
            } else {
                setMappingAndSource(ctx.variable().getText(), updateProductionVariablesToTrees, currentVariableDictionary.get(ctx.variable().getText()));
            }

            for (SoarParser.Attr_value_makeContext attr_value_makeContext : ctx.attr_value_make()) {
                for (SoarParser.Variable_or_sym_constantContext variable_or_sym_constantContext : attr_value_makeContext.variable_or_sym_constant()) {
                    currentBranchInAttributesAndValues = productionSource.addEdgeWithoutValues(variable_or_sym_constantContext.getText());
                }
                SymbolTree child = attr_value_makeContext.accept(this);
                child = new SymbolTree(child.name);
                attachPoint.addChild(child);
            }

            System.out.println();
        }
        return null;
    }

    @Override
    public SymbolTree visitFunc_call(SoarParser.Func_callContext ctx) {
        if (!ctx.func_name().getText().equals("halt")) {
            return new SymbolTree("ADD_NODE");
        } else {
            return null;
        }
    }

    /**
     * Pass up the value of the child node.
     *
     * @param ctx
     * @return
     */
    @Override
    public SymbolTree visitValue(SoarParser.ValueContext ctx)
    {
        ParseTree node = ctx.children.get(0);
        if (node instanceof SoarParser.VariableContext)
        {
            nestedVariableNames.add(node.getText());
            return new SymbolTree(node.getText());
        }
        else
        {
            return node.accept(this);
        }
    }

    /**
     *
     *
     * @param ctx
     * @return
     */
    @Override
    public SymbolTree visitAttr_value_make(SoarParser.Attr_value_makeContext ctx)
    {
        SymbolTree subtree = getTreeFromList(ctx.variable_or_sym_constant());

        nestedVariableNames.clear();
        for (SoarParser.Variable_or_sym_constantContext variable_or_sym_constantContext : ctx.variable_or_sym_constant()) {
            for (SoarParser.Value_makeContext value_makeContext : ctx.value_make()) {
                currentMaxQuerySize++;
                if (!isProductionOSupported && value_makeContext.value_pref_clause().size() == 0 && value_makeContext.value_pref_binary_value() == null) {
                    currentMaxQuerySize++;
                }
                if (value_makeContext.value().func_call() != null) {
                    currentMaxQuerySize++;
                }
                AugmentedSymbolTree newestValue = currentBranchInAttributesAndValues.findAugmentedTreeTop(value_makeContext.value().getText());
                if (newestValue == null) {
                    newestValue = currentBranchInAttributesAndValues.addSingleValue(value_makeContext.value().getText());
                }
                SymbolTree rightHandTree = value_makeContext.accept(this);
                if (rightHandTree != null) {
                    subtree.addChild(rightHandTree);
                }
                if (!variable_or_sym_constantContext.getText().equals("operator") && rightHandTree.getSubtreeNoError("isRejected") != null) {
                    newestValue.setName("$" + newestValue.getName());
                } else if (variable_or_sym_constantContext.getText().equals("operator")) {
                    operatorCount++;
                }

                if (!nestedVariableNames.isEmpty())
                {
                        for (String nestedVariableName : nestedVariableNames)
                        {
                            if (!currentVariableDictionary.containsKey(nestedVariableName))
                            {
                                currentVariableDictionary.put(nestedVariableName, subtree.name);
                            }

                        }
                }

                if (value_makeContext.value().variable() != null && !currentVariablesCreatedOrUpdated.rejectedContains(value_makeContext.value().variable().getText())) {
                    currentVariablesCreatedOrUpdated.addToVaribles(value_makeContext.value().variable().getText());
                }
            }
        }

        return subtree;
    }

    /**
     * Represents the attribute following the caret on the action side. Can also be a variable, the translator does not
     * handle variable attributes. //fixme
     * Returns a singleton SymbolTree wrapping the text.
     *
     * @param ctx
     * @return
     */
    @Override
    public SymbolTree visitVariable_or_sym_constant(SoarParser.Variable_or_sym_constantContext ctx)
    {
        return new SymbolTree(ctx.getText());
    }

    /**
     * On the action side, this context is everything after the attribute, a combinations of values, variables, and
     * preferences.
     *
     * @param ctx
     * @return
     */
    @Override
    public SymbolTree visitValue_make(SoarParser.Value_makeContext ctx)
    {
        SymbolTree returnTree = ctx.value().accept(this);
        if (ctx.value_pref_binary_value() != null) {
            SymbolTree pref = ctx.value_pref_binary_value().accept(this);
            if (pref != null) {
                returnTree.addChild(pref);
            }
        } else if (ctx.value_pref_clause().size() != 0) {
            for (SoarParser.Value_pref_clauseContext value_pref_clauseContext : ctx.value_pref_clause()) {
                SymbolTree pref = value_pref_clauseContext.accept(this);
                if (pref != null) {
                    returnTree.addChild(pref);
                }
            }
        } else if (((SoarParser.Attr_value_makeContext) ctx.parent).variable_or_sym_constant().get(0).getText().equals("operator")) {
            returnTree.addChild(new SymbolTree("isAcceptable"));
        }
        return returnTree;
    }


    @Override
    public SymbolTree visitValue_pref_binary_value(SoarParser.Value_pref_binary_valueContext ctx)
    {
        SymbolTree returnTree = null;
        if (ctx.unary_or_binary_pref() != null) {
            String isWhat = ctx.unary_or_binary_pref().accept(this).name;
            if (ctx.value() != null) {
                if (isWhat != null) {
                    returnTree = new SymbolTree(isWhat);
                    returnTree.addChild(new SymbolTree(ctx.value().getText()));
                }
            }
        }
        return returnTree;
    }

    @Override
    public SymbolTree visitUnary_or_binary_pref(SoarParser.Unary_or_binary_prefContext ctx) {
        return new SymbolTree(UtilityForVisitors.unaryOrBinaryToString(ctx.getText().charAt(0), unaryOrBinaryFlag));
    }

    @Override
    public SymbolTree visitValue_pref_clause(SoarParser.Value_pref_clauseContext ctx)
    {
        SymbolTree returnTree = null;
        if (ctx.unary_pref() != null) {
            String isWhat = ctx.unary_pref().accept(this).name;
            if (isWhat != null) {
                returnTree = new SymbolTree(isWhat);
            }
        } else if (ctx.unary_or_binary_pref() != null) {
            unaryOrBinaryFlag = true;
            String isWhat = ctx.unary_or_binary_pref().accept(this).name;
            unaryOrBinaryFlag = false;
            if (isWhat != null) {
                returnTree = new SymbolTree(isWhat);
            }
        }
        return returnTree;
    }

    @Override
    public SymbolTree visitUnary_pref(SoarParser.Unary_prefContext ctx) {
        return new SymbolTree(UtilityForVisitors.unaryToString(ctx.getText().charAt(0)));
    }
}
