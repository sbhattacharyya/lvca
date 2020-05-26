package edu.fit.hiai.lvca.translator.soar;

import edu.fit.hiai.lvca.antlr4.SoarBaseVisitor;
import edu.fit.hiai.lvca.antlr4.SoarParser;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.RuleContext;
import org.antlr.v4.runtime.tree.ParseTree;

import java.util.*;
import java.util.stream.Collectors;


/**
 * Created by mstafford on 8/4/16.
 * Updated by Daniel Griessler throughout the summer of 2018
 *
 * Get all symbols and working memory locations used in the Soar agent. This class produces a single SymbolTree that
 * variablesContains all memory locations used by the Soar agent. Each variable's working memory association is stored. Each
 * string written is stored.
 *
 */
class SymbolVisitor extends SoarBaseVisitor<SymbolTree> {
    //Everything is run through the visitor pattern.  The visitor pattern follows the ANTLR grammar and is able to pass ONE data structure UP through the structure
    //This limitation resulted in us adding many global variables that are modified and accessed throughout the visitor pattern.  This eliminates the requirement of sending only one
    //complex data structure and we can add and remove structures as needed.
    //Most of the maps will map production names to another map.  They also often work in pairs, one as the "current" one for the production and one that is the "global" one
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
    private Map<String, Boolean> productionToOSupported = new HashMap<>();
    private Map<String, Map<String, String[]>> attributeVariableToDisjunctionTestPerProduction = new HashMap<>();
    private Map<String, String[]> arrayNameToDisjunctionTest;
    private Map<String, String> attributeVariableToArrayName;
    private boolean onAttribute;

    /**
     * Entry point for parsing, get all literal strings, values, and working memory locations used.
     * @param ctx All of the productions
     */
    public SymbolVisitor(SoarParser.SoarContext ctx) {
        ctx.accept(this); // Call for side effects
    }

    Set<String> getStringSymbols() { return stringSymbols; }

    Map<String, Map<String, AugmentedSymbolTree>> getAttributesAndValuesPerProduction() { return attributesAndValuesPerProduction; }

    Map<String, Map<String, AugmentedSymbolTree>> getCheckAttributesAndValuesPerProduction() { return checkAttributesAndValuesPerProduction; }

    Map<String, Map<String, AugmentedSymbolTree>> getUpdateAttributesAndValuesPerProduction() { return updateAttributesAndValuesPerProduction; }

    Map<String, LinkedList<String>> getVariableHierarchy() {
        return variableHierarchy;
    }

    Set<String> getBooleanSymbols() { return booleanSymbols; }

    Map<String, Map<String, String>> getGlobalVariableDictionary()
    {
        return globalVariableDictionary;
    }

    Map<String, ProductionVariables> getActualVariablesInProduction() { return actualVariablesInProduction; }

    Map<String, ProductionVariables> getVariablesCreatedOrUpdated() { return variablesCreatedOrUpdated; }

    int getOperatorCount() { return operatorCount; }

    Map<String, Boolean> getProductionToOSupported() { return productionToOSupported; }

    Map<String, Map<String, String[]>> getAttributeVariableToDisjunctionTest() { return attributeVariableToDisjunctionTestPerProduction; }


    /**
     * Update the global dictionary of (Soar Production) -> (Variable) -> (Working Memory Path)
     * The global dictionary keeps track of all Soar variable associations
     *
     * @param ctx Views one entire production
     * @return Null
     */
    @Override
    public SymbolTree visitSoar_production(SoarParser.Soar_productionContext ctx) {
        String productionName = ctx.sym_constant().getText(); //Getting the name of the soar production here. Intitially this is empty after the 2 conditions it is then full.
        productionVariablesToTrees = new HashMap<>();
        attributesAndValuesPerProduction.put(productionName, productionVariablesToTrees);

        checkProductionVariablesToTrees = new HashMap<>();
        checkAttributesAndValuesPerProduction.put(productionName, checkProductionVariablesToTrees);

        updateProductionVariablesToTrees = new HashMap<>();
        updateAttributesAndValuesPerProduction.put(productionName, updateProductionVariablesToTrees);

        addLocation = 0;
        currentPlaceInVariableHierarchy = new LinkedList<>();
        variableHierarchy.put(productionName, currentPlaceInVariableHierarchy);

        currentVariablesPerProduction = new ProductionVariables(productionName);
        currentVariablesCreatedOrUpdated = new ProductionVariables(productionName);
        currentVariableDictionary = new HashMap<>();
        isProductionOSupported = false;

        attributeVariableToArrayName = new HashMap<>();
        arrayNameToDisjunctionTest = new HashMap<>();

        //global variables are updated in the lower parts of the pattern.  The following updates after the two accepts rely on those modifications
        // TODO: Throws away output-link currently
        SymbolTree ret = ctx.condition_side().accept(this);
        if (ret != null && ret.name.equals("$output-link$")) {
            return null;
        }
       ctx.action_side().accept(this);

        Map<String, String> variablePaths = new HashMap<>();

        for (HashMap.Entry<String, String> entry : currentVariableDictionary.entrySet())
        {
            variablePaths.put(entry.getKey(), workingMemoryTree.pathTo(entry.getValue()));
        }
        currentVariablesPerProduction.clean();
        actualVariablesInProduction.put(productionName, currentVariablesPerProduction);

        currentVariablesCreatedOrUpdated.addToRejected(currentVariablesPerProduction.getVariables());
        currentVariablesCreatedOrUpdated.clean();
        variablesCreatedOrUpdated.put(productionName, currentVariablesCreatedOrUpdated);

        for (int i = 0 ; i < currentPlaceInVariableHierarchy.size(); i++) {
            String variable = currentPlaceInVariableHierarchy.get(i);
            if (currentVariablesPerProduction.variablesContains(variable) || (currentVariableDictionary.get(variable) != null && currentVariableDictionary.get(variable).contains("operator"))) {
                currentPlaceInVariableHierarchy.remove(i);
                i--;
            }
        }

        globalVariableDictionary.put(productionName, variablePaths);
        if (ctx.flags() != null && !isProductionOSupported) { //if the soar production is not o-Supported and if it has flags and..
            for (ParseTree flag : ctx.flags().children) { //refer ctx.flag from antlr file Soar.g4 line 6,8
                if (flag.getText().equalsIgnoreCase("o-support")) { //..if the flag is o-support, then the production is true. I.e., its o-supported
                    isProductionOSupported = true;
                }
            }
        }
        productionToOSupported.put(productionName, isProductionOSupported);
        Map<String, String[]> attributeVariableToDisjunctionTest = new HashMap<>();
        for (Map.Entry<String, String> attributeVariableToArrayName : attributeVariableToArrayName.entrySet()) {
            attributeVariableToDisjunctionTest.put(attributeVariableToArrayName.getKey(), arrayNameToDisjunctionTest.get(attributeVariableToArrayName.getValue()));
        }
        attributeVariableToDisjunctionTestPerProduction.put(productionName, attributeVariableToDisjunctionTest);
        return null;
    }

    /**
     * Auxiliary function to set the source before more edges and their values are added
     * @param variable Which variable is being added to
     * @param map Maps variables to AugmentedSymbolTree which hold their edges and values
     * @param treePath Variable path
     */
    private void setMappingAndSource(String variable, Map<String, AugmentedSymbolTree> map, String treePath) {
        if (map.get(variable) == null) {
            map.put(variable, new AugmentedSymbolTree(treePath));
        }
        productionSource = map.get(variable);
    }

    @Override
    public SymbolTree visitCondition_side(SoarParser.Condition_sideContext ctx) {
        // TODO: Throws away output-link currently
        SymbolTree ret = ctx.state_imp_cond().accept(this);
        if (ret != null && ret.name.equals("$output-link$")) {
            return ret;
        }
        // TODO: Throws away output-link currently
        for (SoarParser.CondContext condContext : ctx.cond()) {
            ret = condContext.accept(this);
            if (ret != null && ret.name.equals("$output-link$")) {
                return ret;
            }
        }

        return null;
    }

    /**
     * function - visit state implicit condition
     * Establish "state" as the root of the working tree with the first variable (usually &lt;s&gt;). Update the working
     * memory with specified attributes.
     * Establishes variable in the id_test as the state variable
     * Establishes source for lower visits to the attribute values to add to
     *
     * @param ctx Looks at the conditions that are directly attached to the state
     * @return Doesn't need to return anything
     */
    @Override
    public SymbolTree visitState_imp_cond(SoarParser.State_imp_condContext ctx) {
        currentVariableDictionary.put(ctx.id_test().getText(), workingMemoryTree.name);


        //State is always updated, at least right now
        currentVariablesCreatedOrUpdated.addToRejected(ctx.id_test().getText());

        setMappingAndSource(ctx.id_test().getText(), checkProductionVariablesToTrees, "state");
        stateVariable = ctx.id_test().getText();

        currentPlaceInVariableHierarchy.add(addLocation++, ctx.id_test().getText());

        // Call for Side Effects
        for (SoarParser.Attr_value_testsContext attr_value_testsContext : ctx.attr_value_tests()) {
            SymbolTree child = attr_value_testsContext.accept(this);
            // TODO: Throws away output-link currently
            if (child != null && child.name.equals("$output-link$") ) {
                return child;
            }
            workingMemoryTree.addChild(child);
        }

        productionSource = null;

        return null;
    }

    /**
     * Does what the parser would do automatically anyway, but returns null instead of the symbolTree from the lower visits
     * @param ctx Either conjunctive test of other conditions or a conds for one id
     * @return Null
     */
    @Override
    public SymbolTree visitPositive_cond(SoarParser.Positive_condContext ctx) {
        if (ctx.conds_for_one_id() != null) {
            // TODO: Throws away output-link currently
            SymbolTree ret = ctx.conds_for_one_id().accept(this);
            if (ret != null && ret.name.equals("$output-link$")) {
                return ret;
            }
        } else {
            for (SoarParser.CondContext condContext : ctx.cond()) {
                condContext.accept(this);
            }
        }
        return null;
    }

    /**
     * Updates source for lower visits to the attribute values to add to
     * Updates workingMemoryTree with paths retrieved from visiting the attribute value tests
     *
     * @param ctx Set of conditions which is either the state or another main variable
     * @return Null
     */
    @Override
    public SymbolTree visitConds_for_one_id(SoarParser.Conds_for_one_idContext ctx) {
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

        // TODO: Throws away output-link currently
        for(SoarParser.Attr_value_testsContext avt : ctx.attr_value_tests()) {
            SymbolTree child = avt.accept(this);
            if (child != null && child.name.equals("$output-link$")) {
                return child;
            }

            workingMemoryTree.addChild(child);
        }

        productionSource = null;

        return null;
    }

    /**
     * Auxiliary function used to add a mapping between variable and disjunction array
     * @param attribute Tree with variable and disjunction array
     * @return The name of the variable
     */
    private String addAttributeVariableToArrayName(SymbolTree attribute) {
        SymbolTree disjunctionBranch = attribute.DFS("disjunctionArray").getChildren().get(0);
        SymbolTree variableBranch = attribute.DFS("variable").getChildren().get(0);
        attributeVariableToArrayName.put(variableBranch.name, disjunctionBranch.name);
        return variableBranch.name;

    }

    /**
     * Auxiliary function used to create/update subtree with a new subtree with the name of text
     * @param subtree SymbolTree which is either null or initialized
     * @param text Name of new SymbolTree needed to add as a child of the provided subtree
     * @return SymbolTree either now initialized or with a new child
     */
    private SymbolTree addAttributeToSubtrees(SymbolTree subtree, String text) {
        if (subtree == null) {
            subtree = new SymbolTree(text);
        } else {
            subtree.addChild(new SymbolTree(text));
        }
        return subtree;
    }

    /**
     * Determine the associations for the variable dictionary.
     * E.g. given (&lt;s&gt; ^operator <o>) save the mapping of <o> to ^operator
     * Sets the branch of Attributes and Values and then adds values using the lower visits
     * Catches extra restrictions on attributes and values
     *
     * @param ctx at least one attribute with any number of values
     * @return Tree with
     */
    @Override
    public SymbolTree visitAttr_value_tests(SoarParser.Attr_value_testsContext ctx) {
        boolean conditionIsNegated = ctx.getText().charAt(0) == '-';
        SymbolTree subtree = null;

        //Sets a boolean to not add to the currentBranch which is flipped back off after the loop
        //Visits the attributes and handles the conjunctive tests in an attribute
        //Sets the branch for the AVs for the value visits below
        onAttribute = true;
        for (SoarParser.Attr_testContext attr_testContext : ctx.attr_test()) {
            SymbolTree attribute = attr_testContext.accept(this);
            String attributeName = attr_testContext.getText();
            // TODO: Throws away output-link currently
            if (attributeName.equals("output-link")) {
                return new SymbolTree("$output-link$");
            }

            if (productionSource != null) {
                if (attr_testContext.getText().equals("operator")) {
                    currentBranchInAttributesAndValues = null;
                    subtree = addAttributeToSubtrees(subtree, attributeName);
                    break;
                } else {
                    if (attr_testContext.test().conjunctive_test() != null) {
                        String variableName = addAttributeVariableToArrayName(attribute);
                        currentBranchInAttributesAndValues = productionSource.addEdgeWithoutValues(variableName);
                        attributeName = variableName;
                    } else {
                        currentBranchInAttributesAndValues = productionSource.addEdgeWithoutValues(attribute.name);
                    }
                }
            } else if (attr_testContext.test().conjunctive_test() != null) {
                attributeName = addAttributeVariableToArrayName(attribute);
            }
            subtree = addAttributeToSubtrees(subtree, attributeName);
        }
        onAttribute = false;

        //Special value signaling to Uppaal that there aren't any values
        if (productionSource != null && currentBranchInAttributesAndValues != null && ctx.value_test().size() == 0) {
            currentBranchInAttributesAndValues.addSingleValue("$EMPTY");
        }

        // Global is changed as a side effect of next line
        nestedVariableNames.clear();
        // Called for side effects
        for (SoarParser.Value_testContext value_testContext : ctx.value_test()) {
            SymbolTree child = value_testContext.accept(this);
            if (child != null && child.DFS("relation") != null) {
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
        if (!isProductionOSupported) { //checking if condition side contains operator for O-Supported productions
            isProductionOSupported = ctx.attr_test().stream().map(RuleContext::getText).collect(Collectors.joining("_")).contains("operator");
        }
        return subtree;
    }

    /**
     * Collects the different parts of the conjunctive test under one SymbolTree
     * @param ctx Includes several restrictions on what can be matched as well as the variable to which it is binding to
     * @return SymbolTree with all of the different restrictions as children to be parsed and analyzed above
     */
    @Override
    public SymbolTree visitConjunctive_test(SoarParser.Conjunctive_testContext ctx) {
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


    /**
     * Collects all the constants in the disjunction test and creates a mapping between an arbitrary array name and those elements if there isn't already one with the same values
     * @param ctx Collection of constants, one of which that the variable must be equal to
     * @return SymbolTree with the array name for the disjunction values
     */
    @Override
    public SymbolTree visitDisjunction_test(SoarParser.Disjunction_testContext ctx) {
        String[] notAllBut = new String[ctx.constant().size()];
        for (int i = 0; i < ctx.constant().size(); i++) {
            ctx.constant(i).accept(this);
            notAllBut[i] = ctx.constant(i).getText();
        }
        int latestIndex = 1;
        boolean contains = false;
        for (Map.Entry<String, String[]> stringEntry : arrayNameToDisjunctionTest.entrySet()) {
            int nextIndex = Integer.parseInt(stringEntry.getKey().substring(stringEntry.getKey().lastIndexOf('_') + 1));
            if (Arrays.equals(stringEntry.getValue(), notAllBut)) {
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


    /**
     * Collects variable and any relation under one SymbolTree
     * @param ctx Either just a variable or a variable with a relation
     * @return SymbolTree with relation as a child if present to be analyzed above
     */
    @Override
    public SymbolTree visitRelational_test(SoarParser.Relational_testContext ctx) {
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


    /**
     * Uses Utility to get text representation of the relation
     * @param ctx Relation is one of many options
     * @return SymbolTree with relation or null if the relation doesn't match
     */
    @Override
    public SymbolTree visitRelation(SoarParser.RelationContext ctx) {
        String relationText = UtilityForVisitors.relationToText(ctx.getText());
        SymbolTree returnTree;
        if (relationText != null) {
            returnTree = new SymbolTree(relationText);
        } else {
            returnTree = null;
        }
        return returnTree;
    }


    /**
     * Handles both possibilities of constant or variable
     * @param ctx Either a constant or variable
     * @return SymbolTree with the text of either the constant or variable
     */
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
            value = SoarTranslator.simplifiedString(ctx.constant().getText());
        }
        if (productionSource != null && currentBranchInAttributesAndValues != null && !onAttribute) {
            currentBranchInAttributesAndValues.addSingleValue(value);
        }
        return new SymbolTree(value);
    }


    /**
     * Supports visitAttr_value_tests() method, takes the SymbolTree and returns the first leaf node it finds.
     *call
     * @param subtree SymbolTree which is being pulled from
     * @return First leaf node it finds
     */
    private String getFirstLeaf(SymbolTree subtree) {
        SymbolTree t = subtree;
        while (t.getChildren().size() > 0) {
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
     * @param ctxs List of attributes
     * @return SymbolTree with all the attributes stacked as children
     */
    private SymbolTree getTreeFromList(List<? extends ParserRuleContext> ctxs) {
        if (ctxs.size() == 1) {
            return new SymbolTree(ctxs.get(0).getText());
        } else {
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
     * @param ctx Variable includes a sym_constant
     * @return Either the path to the variable or null
     */
    @Override
    public SymbolTree visitVariable(SoarParser.VariableContext ctx) {
        nestedVariableNames.add(ctx.getText());
        String variableName = currentVariableDictionary.get(ctx.getText());
        currentVariablesPerProduction.addToVaribles(ctx.getText());
        if (variableName != null) {
            return workingMemoryTree.getSubtree(variableName);
        }
        return null;
    }

    /**
     * Save constants as singleton SymbolTrees for higher contexts
     *
     * @param ctx Constant as defined in ANTLR with several possibilities
     * @return SymbolTree with the text
     */
    @Override
    public SymbolTree visitConstant(SoarParser.ConstantContext ctx) {
        String result = SoarTranslator.simplifiedString(ctx.getText());

        if (ctx.sym_constant() != null) {
            stringSymbols.add(SoarTranslator.simplifiedString(ctx.getText()));
        } else if (ctx.Print_string() != null) {
            // Literal Strings in Soar are surrounded by vertical bars
            //This is dumb
            result = UPPAALSemanticVisitor.LITERAL_STRING_PREFIX + ctx.Print_string().getText().split("|")[1];
            stringSymbols.add(result);
        }

        return new SymbolTree(result);
    }

    /**
     * Track changes to working memory, update the SymbolTree
     * Sets the source for lower visits
     * @param ctx One of the actions on the action side of a production
     * @return Null
     */
    @Override
    public SymbolTree visitAction(SoarParser.ActionContext ctx) {
        if (ctx.attr_value_make() != null && ctx.variable() != null) {
            SymbolTree attachPoint = ctx.variable().accept(this);
            if (currentVariablesPerProduction.variablesContains(ctx.variable().getText())) {
                currentVariablesPerProduction.addToRejected(ctx.variable().getText());
            }

            if (attachPoint == null) {
                System.err.printf("Translation Error: Soar variable %s in production %s is not defined.\n",
                        ctx.variable().getText(),
                        ((SoarParser.Soar_productionContext)ctx.parent.parent).sym_constant().getText());
               // return null;
               System.exit(1);
            }

            if (attachPoint.name.equals("state") || (productionVariablesToTrees.get(stateVariable) != null && productionVariablesToTrees.get(stateVariable).recursiveSearch(productionVariablesToTrees, ctx.variable().getText()))) {
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
        }
        return null;
    }

    /**
     * At this stage, only checking if the function is halt.
     * @param ctx Function call associated with a value or (halt)
     * @return Special signal that it is halt or Null
     */
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
     * @param ctx Several possibilities outlined in ANTLR
     * @return SymbolTree with value name
     */
    @Override
    public SymbolTree visitValue(SoarParser.ValueContext ctx) {
        ParseTree node = ctx.children.get(0);
        if (node instanceof SoarParser.VariableContext) {
            nestedVariableNames.add(node.getText());
            return new SymbolTree(node.getText());
        } else {
            return node.accept(this);
        }
    }

    /**
     * Updates global values with each pass over the next value associated with its corresponding attribute
     * @param ctx One or more attributes with zero or one values
     * @return SymbolTree with attributes and values
     */
    @Override
    public SymbolTree visitAttr_value_make(SoarParser.Attr_value_makeContext ctx) {
        SymbolTree subtree = getTreeFromList(ctx.variable_or_sym_constant());

        nestedVariableNames.clear();
        for (SoarParser.Variable_or_sym_constantContext variable_or_sym_constantContext : ctx.variable_or_sym_constant()) {

            if (variable_or_sym_constantContext.sym_constant() != null) {
                stringSymbols.add(variable_or_sym_constantContext.getText());
            }
            for (SoarParser.Value_makeContext value_makeContext : ctx.value_make()) {
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
     * Condenses value and its preferences into a SymbolTree for analysis above
     *
     * @param ctx Includes value and, if it has preferences, then either a binary preference with another value or a list of unary preferences
     * @return SymbolTree with value and all of its preferences as children
     */
    @Override
    public SymbolTree visitValue_make(SoarParser.Value_makeContext ctx) {
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

    /**
     * Condenses binary preference with its value
     * @param ctx Binary preference with other value
     * @return SymbolTree with preference and other value as child
     */
    @Override
    public SymbolTree visitValue_pref_binary_value(SoarParser.Value_pref_binary_valueContext ctx) {
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

    /**
     * Uses utility to get String representation of the preference
     * @param ctx Preference that is either unary or binary. Uses global flag to know which one
     * @return SymbolTree with the name of the preference
     */
    @Override
    public SymbolTree visitUnary_or_binary_pref(SoarParser.Unary_or_binary_prefContext ctx) {
        return new SymbolTree(UtilityForVisitors.unaryOrBinaryToString(ctx.getText().charAt(0), unaryOrBinaryFlag));
    }

    /**
     * Uses lower accepts to get String representation of the preference
     * @param ctx Preference that is either unary
     * @return SymbolTree with the name of the preference
     */
    @Override
    public SymbolTree visitValue_pref_clause(SoarParser.Value_pref_clauseContext ctx) {
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

    /**
     * Uses utility to get String representation of the preference
     * @param ctx Preference that is either unary or binary. Uses global flag to know which one
     * @return SymbolTree with the name of the preference
     */
    @Override
    public SymbolTree visitUnary_pref(SoarParser.Unary_prefContext ctx) {
        return new SymbolTree(UtilityForVisitors.unaryToString(ctx.getText().charAt(0)));
    }
}
