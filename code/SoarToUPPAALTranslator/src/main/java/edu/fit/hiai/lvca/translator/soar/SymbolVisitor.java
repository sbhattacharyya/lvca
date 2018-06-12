package edu.fit.hiai.lvca.translator.soar;

import edu.fit.hiai.lvca.antlr4.SoarBaseVisitor;
import edu.fit.hiai.lvca.antlr4.SoarParser;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.tree.ParseTree;

import java.util.*;
import java.util.stream.Collectors;


/**
 * Created by mstafford on 8/4/16.
 *
 * Get all symbols and working memory locations used in the Soar agent. This class produces a single SymbolTree that
 * contains all memory locations used by the Soar agent. Each variable's working memory association is stored. Each
 * string written is stored.
 *
 */
class SymbolVisitor extends SoarBaseVisitor<SymbolTree>
{
    private int OPERATOR_ID = 1;
    private Set<String> stringSymbols = new HashSet<>();
    private Set<String> booleanSymbols = new HashSet<>();
    private SymbolTree workingMemoryTree = new SymbolTree("state");
    private Map<String, String> currentVariableDictionary;
    private Set<String> nestedVariableNames = new HashSet<>();
    private Map<String, Map<String, String>> globalVariableDictionary = new HashMap<>();
    private ArrayList<SymbolTree> operators = new ArrayList<>();
    private Map<String, SymbolTree> currentOperators;
    private ArrayList<ArrayList<String>> operatorAttributesAndValues = new ArrayList<>();
    private boolean unaryOrBinaryFlag = false;

    /**
     * Entry point for parsing, get all literal strings, values, and working memory locations used.
     * @param ctx
     */
    public SymbolVisitor(SoarParser.SoarContext ctx)
    {
        // This call also updates stringSymbols, workingMemoryTree, and booleanSymbols
        ctx.accept(this); // Call for side effects

        stringSymbols.addAll(workingMemoryTree.getAllPaths());

        booleanSymbols = booleanSymbols //todo #what
                .stream()
                .map(attr -> workingMemoryTree.pathTo(attr))
                .collect(Collectors.toSet());

        stringSymbols.removeAll(booleanSymbols);
        stringSymbols.remove("true");
        stringSymbols.remove("false");
    }

    Set<String> getStringSymbols()
    {
        return stringSymbols;
    }

    SymbolTree getTree()
    {
        return workingMemoryTree;
    }

    Set<String> getBooleanSymbols()
    {
        return booleanSymbols;
    }

    Map<String, Map<String, String>> getGlobalVariableDictionary()
    {
        return globalVariableDictionary;
    }

    ArrayList<SymbolTree> getOperators() { return operators; }

    ArrayList<ArrayList<String>> getOperatorAttributesAndValues() { return operatorAttributesAndValues; }

    int getOPERATOR_ID() { return OPERATOR_ID; }

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
        currentVariableDictionary = new HashMap<>();
        currentOperators = new HashMap<>();
        ctx.condition_side().accept(this);
        ctx.action_side().accept(this);
        SymbolTree parent = new SymbolTree(ctx.sym_constant().getText());
        for (Map.Entry<String, SymbolTree> stringSymbolTreeEntry : currentOperators.entrySet()) {
            parent.addChild(stringSymbolTreeEntry.getValue());
        }
        operators.add(parent);

        // globalVariableDictionary: production name -> variable id -> variable path

        Map<String, String> variablePaths = new HashMap<>();

        for (HashMap.Entry<String, String> entry : currentVariableDictionary.entrySet())
        {
            variablePaths.put(entry.getKey(), workingMemoryTree.pathTo(entry.getValue()));
        }


        globalVariableDictionary.put(ctx.sym_constant().getText(), variablePaths);
        return null;
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

        // Call for Side Effects
        for (SoarParser.Attr_value_testsContext attr_value_testsContext : ctx.attr_value_tests()) {
            SymbolTree child = attr_value_testsContext.accept(this);
            //gets tree without children
            child = child.getChildren().get(0);
            workingMemoryTree.addChild(child);
        }

//        ctx.attr_value_tests().forEach(avt -> workingMemoryTree.addChild(avt.accept(this)));
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

        for(SoarParser.Attr_value_testsContext avt : ctx.attr_value_tests())
        {
            SymbolTree child = avt.accept(this);
            SymbolTree childWithChildren = null;
            if (!child.getChildren().get(0).name.equals("withChildren")) {
                childWithChildren = child.getChildren().get(1);
                child = child.getChildren().get(0);
            } else {
                childWithChildren = child.getChildren().get(0);
                child = child.getChildren().get(1);
            }
            attachPoint.addChild(child);

            SymbolTree operator = currentOperators.get(ctx.id_test().getText());
            SymbolTree attributeValue = childWithChildren.getChildren().get(0);
            if (operator != null) {
                operator.addChild(attributeValue);
            }
        }

        return null;
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
        //The attribute or list of attributes following the caret. This SymbolTree therefore has no branching
        SymbolTree subtree = getTreeFromList(ctx.attr_test());
        SymbolTree subtreeWithChildren = new SymbolTree("withChildren");
        subtreeWithChildren.addChild(getTreeFromList(ctx.attr_test()));

        // Global is changed as a side effect of next line
        nestedVariableNames.clear();
        // Called for side effects
        for (SoarParser.Value_testContext value_testContext : ctx.value_test()) {
            SymbolTree child = value_testContext.accept(this);
            if (child != null && !subtree.name.equals("operator")) {
                subtreeWithChildren.getChildren().get(0).addChild(child);
            }
        }

//        ctx.value_test().forEach(vt -> vt.accept(this));

        for (String nestedVariableName : nestedVariableNames)
        {
            if (!currentVariableDictionary.containsKey(nestedVariableName))
            {
                // getFirstLeaf() because subtree is really a LinkedList and we want the last element
                currentVariableDictionary.put(nestedVariableName, getFirstLeaf(subtree));
            }
            if (subtree.name.equals("operator")) {
                if (!currentOperators.containsKey(nestedVariableName)) {
                    SymbolTree child = new SymbolTree(nestedVariableName);
                    child.addChild(new SymbolTree("update"));
                    currentOperators.put(nestedVariableName, child);
                }
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
        return returnTree;
    }

    /**
     * Supports visitAttr_value_tests() method, takes the SymbolTree and returns the first leaf node it finds.
     *
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

    private int findAttributeIndex(String rootName) {
        int attributeIndex = -1;
        for (int i = 0; i < operatorAttributesAndValues.size(); i++) {
            if (operatorAttributesAndValues.get(i).get(0).equals(rootName)) {
                attributeIndex = i;
                break;
            }
        }
        return attributeIndex;
    }

    private int getAttributeIndex(String rootName) {
        int attributeIndex = findAttributeIndex(rootName);
        if (attributeIndex == -1) {
            ArrayList<String> newest = new ArrayList<>();
            newest.add(rootName);
            operatorAttributesAndValues.add(newest);
            attributeIndex = operatorAttributesAndValues.size() - 1;
        }
        return attributeIndex;
    }

    private int findValueIndex(String value, int attributeIndex) {
        int valueIndex = -1;
        ArrayList<String> values = operatorAttributesAndValues.get(attributeIndex);
        for (int i = 1; i < values.size(); i++) {
            if (values.get(i).equals(value)) {
                valueIndex = i;
                break;
            }
        }
        return valueIndex;
    }

    private int getValueIndex(String value, int attributeIndex) {
        int valueIndex = findValueIndex(value, attributeIndex);
        if (valueIndex == -1) {
            operatorAttributesAndValues.get(attributeIndex).add(value);
            valueIndex = operatorAttributesAndValues.get(attributeIndex).size() - 1;
        }
        return valueIndex;
    }

    public void createAttributeValuePair(String attributeName, String valueName, SymbolTree operator) {
        int attributeIndex = getAttributeIndex(attributeName);
        int valueIndex = getValueIndex(valueName, attributeIndex);
        SymbolTree attributeTree = operator.getSubtreeIgnoreUpdateAndCreate("[" + attributeIndex);
        if (attributeTree == null) {
            attributeTree = new SymbolTree("[" + attributeIndex);
            attributeTree.addChild(new SymbolTree(valueIndex + "]"));
            operator.addChild(attributeTree);
        } else {
            SymbolTree valueTree = attributeTree.getSubtreeNoError(valueIndex + "]");
            if (valueTree == null) {
                attributeTree.addChild(new SymbolTree(valueIndex + "]"));
            }
        }
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

            if (attachPoint == null)
            {
                System.err.printf("Translation Error: Soar variable %s in production %s is not defined.\n",
                        ctx.variable().getText(),
                        ((SoarParser.Soar_productionContext)ctx.parent.parent).sym_constant().getText());
                System.exit(1);
            }
            for (SoarParser.Attr_value_makeContext attr_value_makeContext : ctx.attr_value_make()) {
                SymbolTree child = attr_value_makeContext.accept(this);
                if (attachPoint.name.equals("operator")) {
                    SymbolTree operator = null;
                    for (Map.Entry<String, SymbolTree> stringSymbolTreeEntry : currentOperators.entrySet()) {
                        if (stringSymbolTreeEntry.getKey().equals(ctx.variable().getText())) {
                            operator = stringSymbolTreeEntry.getValue();
                            break;
                        }
                    }

                    if (operator != null && operator.pathTo("update") != null) {
                        operator = operator.getSubtree("update");
                    }

                    for (SymbolTree symbolTree : child.getChildren()) {
                        if (operator != null) {
                            createAttributeValuePair(child.name, symbolTree.name, operator);
                        }
                    }
                }
                child = new SymbolTree(child.name);
                attachPoint.addChild(child);
            }

//            ctx.attr_value_make().forEach(avm -> attachPoint.addChild(avm.accept(this)));
            System.out.println();
        }
        return null;
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
                SymbolTree rightHandTree = value_makeContext.accept(this);

                if (variable_or_sym_constantContext.getText().equals("operator")) {
                    if (!currentOperators.containsKey(rightHandTree.name)) {
                        SymbolTree createBranch = new SymbolTree("create");

                        SymbolTree idBranch = new SymbolTree("id");
                        idBranch.addChild(new SymbolTree("" + OPERATOR_ID));
                        OPERATOR_ID++;
                        createBranch.addChild(idBranch);

                        rightHandTree.addChild(createBranch);
                        currentOperators.put(rightHandTree.name, rightHandTree);
                    } else {
                        SymbolTree operatorTree  = currentOperators.get(rightHandTree.name);
                        if (operatorTree.pathTo("update") == null) {
                            for (SymbolTree attribute : rightHandTree.getChildren()) {
                                operatorTree.addChild(attribute);
                            }
                        } else {
                            SymbolTree updateTree = operatorTree.getSubtree("update");
                            for (SymbolTree attribute : rightHandTree.getChildren()) {
                                updateTree.addChild(attribute);
                            }
                        }
                    }
                    rightHandTree = null;
                } else {
                    subtree.addChild(rightHandTree);
                }

                if (!nestedVariableNames.isEmpty())
                {
                    if (rightHandTree == null)
                    {
                        for (String nestedVariableName : nestedVariableNames)
                        {
                            if (!currentVariableDictionary.containsKey(nestedVariableName))
                            {
                                currentVariableDictionary.put(nestedVariableName, subtree.name);
                            }

                        }
                    }
                    else
                    {
                        value_makeContext.accept(this).getChildren()
                                .forEach(subtree::addChild);
                    }
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
