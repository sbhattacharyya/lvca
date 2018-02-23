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
 * Get all identifiers used in the Soar agent
 */
class SymbolVisitor extends SoarBaseVisitor<SymbolTree>
{
    private Set<String> stringSymbols = new HashSet<>();
    private Set<String> booleanSymbols = new HashSet<>();
    private SymbolTree workingMemoryTree = new SymbolTree("state");
    private Map<String, String> currentVariableDictionary;
    private String nestedVariableName;
    private Map<String, Map<String, String>> globalVariableDictionary = new HashMap<>();

    public SymbolVisitor(SoarParser.SoarContext ctx)
    {
        ctx.soar_production().forEach(sp -> sp.accept(this));
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

    @Override
    public SymbolTree visitSoar(SoarParser.SoarContext ctx)
    {
        ctx.soar_production().forEach(p -> p.accept(this));
        return workingMemoryTree;
    }

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

    @Override
    public SymbolTree visitCondition_side(SoarParser.Condition_sideContext ctx)
    {
        ctx.state_imp_cond().accept(this);
        ctx.cond().forEach(c -> c.accept(this));
        return null;
    }

    @Override
    public SymbolTree visitState_imp_cond(SoarParser.State_imp_condContext ctx)
    {
        currentVariableDictionary.put(ctx.id_test().getText(), workingMemoryTree.name);

        ctx.attr_value_tests().forEach(avt -> workingMemoryTree.addChild(avt.accept(this)));
        return null;
    }

    @Override
    public SymbolTree visitCond(SoarParser.CondContext ctx)
    {
        ctx.positive_cond().accept(this);
        return null;
    }

    @Override
    public SymbolTree visitPositive_cond(SoarParser.Positive_condContext ctx)
    {
        ctx.conds_for_one_id().accept(this);
        ctx.cond().forEach(c -> c.accept(this));
        return null;
    }

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

    @Override
    public SymbolTree visitId_test(SoarParser.Id_testContext ctx)
    {
        return ctx.test().accept(this);
    }

    @Override
    public SymbolTree visitAttr_value_tests(SoarParser.Attr_value_testsContext ctx)
    {
        SymbolTree subtree = getTreeFromList(ctx.attr_test());
        nestedVariableName = null;
        ctx.value_test().forEach(vt -> vt.accept(this));

        if (nestedVariableName != null && !currentVariableDictionary.containsKey(nestedVariableName))
        {
            currentVariableDictionary.put(nestedVariableName, getFirstLeaf(subtree));
        }

        if (ctx.value_test().size() > 0 &&
                (  ctx.value_test(0).getText().equals("true")
                || ctx.value_test(0).getText().equals("false")))
        {
            booleanSymbols.add(subtree.name);
        }
        return subtree;
    }

    private String getFirstLeaf(SymbolTree subtree)
    {
        SymbolTree t = subtree;
        while (t.getChildren().size() > 0)
        {
            t = t.getChildren().get(0);
        }
        return t.name;
    }

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

    @Override
    public SymbolTree visitAttr_test(SoarParser.Attr_testContext ctx)
    {
        ctx.test().accept(this);
        return null;
    }

    @Override
    public SymbolTree visitValue_test(SoarParser.Value_testContext ctx)
    {
        ctx.test().accept(this);
        return null;
    }

    @Override
    public SymbolTree visitTest(SoarParser.TestContext ctx)
    {
       return ctx.simple_test().accept(this);
    }

    @Override
    public SymbolTree visitSimple_test(SoarParser.Simple_testContext ctx)
    {
        return ctx.relational_test().accept(this);
    }

    @Override
    public SymbolTree visitRelational_test(SoarParser.Relational_testContext ctx)
    {
        return ctx.single_test().accept(this);
    }

    @Override
    public SymbolTree visitSingle_test(SoarParser.Single_testContext ctx)
    {
        return ctx.children.get(0).accept(this);
    }

    @Override
    public SymbolTree visitVariable(SoarParser.VariableContext ctx)
    {
        nestedVariableName = ctx.getText();

        try
        {
            String variableName = currentVariableDictionary.get(nestedVariableName);
            if (variableName != null)
            {
                return workingMemoryTree.getSubtree(variableName);
            }
        }
        catch (NoSuchElementException e)
        {
            e.printStackTrace();
        }
        return null;
    }

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
            result = UPPAALCreator.LITERAL_STRING_PREFIX + ctx.Print_string().getText().split("|")[1];
            stringSymbols.add(result);
        }

        return new SymbolTree(result);
    }

    @Override
    public SymbolTree visitAction_side(SoarParser.Action_sideContext ctx)
    {
        ctx.action().forEach(a -> a.accept(this));
        return null;
    }

    @Override
    public SymbolTree visitAction(SoarParser.ActionContext ctx)
    {
        if (ctx.attr_value_make() != null && ctx.variable() != null)
        {
            SymbolTree attachPoint = ctx.variable().accept(this);
            ctx.attr_value_make().forEach(avm -> attachPoint.addChild(avm.accept(this)));
            System.out.println();
        }
        return null;
    }

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
                currentVariableDictionary.put(nestedVariableName, subtree.name);
            }
            else
            {
                ctx.value_make().accept(this).getChildren()
                        .forEach(subtree::addChild);
            }
        }

        return subtree;
    }

    @Override
    public SymbolTree visitVariable_or_sym_constant(SoarParser.Variable_or_sym_constantContext ctx)
    {
        return new SymbolTree(ctx.getText());
    }

    @Override
    public SymbolTree visitValue_make(SoarParser.Value_makeContext ctx)
    {
        return ctx.value().accept(this);
    }

    @Override
    public SymbolTree defaultResult()
    {
        return null;
    }
}
