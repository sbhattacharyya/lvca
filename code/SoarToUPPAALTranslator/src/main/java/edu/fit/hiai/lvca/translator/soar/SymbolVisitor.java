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
    private Set<String> stringSymbols = new HashSet<>();
    private Set<String> booleanSymbols = new HashSet<>();
    private SymbolTree workingMemoryTree = new SymbolTree("state");
    private Map<String, String> currentVariableDictionary;
    private String nestedVariableName;
    private Map<String, Map<String, String>> globalVariableDictionary = new HashMap<>();

    /**
     * Entry point for parsing, get all literal strings, values, and working memory locations used.
     * @param ctx
     */
    public SymbolVisitor(SoarParser.SoarContext ctx)
    {
        // This call also updates stringSymbols, workingMemoryTree, and booleanSymbols
        ctx.accept(this); // Call for side effects

        stringSymbols.addAll(workingMemoryTree.getAllPaths());

        booleanSymbols = booleanSymbols
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
        ctx.condition_side().accept(this);
        ctx.action_side().accept(this);

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
        ctx.attr_value_tests().forEach(avt -> workingMemoryTree.addChild(avt.accept(this)));
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
            attachPoint.addChild(avt.accept(this));
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

        // Global is changed as a side effect of next line
        nestedVariableName = null;

        // Called for side effects
        ctx.value_test().forEach(vt -> vt.accept(this));

        if (nestedVariableName != null && !currentVariableDictionary.containsKey(nestedVariableName))
        {
            // getFirstLeaf() because subtree is really a LinkedList and we want the last element
            currentVariableDictionary.put(nestedVariableName, getFirstLeaf(subtree));
        }

        // this is for translation to Uppaal, which is probably irrelevant at this particular step
        if (ctx.value_test().size() > 0 &&
                (  ctx.value_test(0).getText().equals("true")
                || ctx.value_test(0).getText().equals("false")))
        {
            booleanSymbols.add(subtree.name);
        }
        return subtree;
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
        nestedVariableName = ctx.getText();

        String variableName = currentVariableDictionary.get(nestedVariableName);
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
            result = UPPAALCreator.LITERAL_STRING_PREFIX + ctx.Print_string().getText().split("|")[1];
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

            if (attachPoint == null)
            {
                System.err.printf("Translation Error: Soar variable %s in production %s is not defined.\n",
                        ctx.variable().getText(),
                        ((SoarParser.Soar_productionContext)ctx.parent.parent).sym_constant().getText());
                System.exit(1);
            }

            ctx.attr_value_make().forEach(avm -> attachPoint.addChild(avm.accept(this)));
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
            nestedVariableName = node.getText();
            return null;
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

        nestedVariableName = null;
        SymbolTree rightHandTree = ctx.value_make().accept(this);

        if (nestedVariableName != null)
        {
            if (rightHandTree == null)
            {
                if (!currentVariableDictionary.containsKey(nestedVariableName))
                {
                    currentVariableDictionary.put(nestedVariableName, subtree.name);
                }
            }
            else
            {
                ctx.value_make().accept(this).getChildren()
                        .forEach(subtree::addChild);
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
        return ctx.value(0).accept(this);
    }
}
