package edu.fit.hiai.lvca.translator.soar;

import edu.fit.hiai.lvca.antlr4.SoarBaseVisitor;
import edu.fit.hiai.lvca.antlr4.SoarParser;
import edu.fit.hiai.lvca.antlr4.SoarVisitor;
import org.antlr.v4.runtime.RuleContext;
import org.antlr.v4.runtime.tree.ErrorNode;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.RuleNode;
import org.antlr.v4.runtime.tree.TerminalNode;
import org.dom4j.Document;
import org.dom4j.DocumentHelper;
import org.dom4j.Element;
import org.dom4j.tree.DefaultDocumentType;
import org.dom4j.tree.DefaultElement;

import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Collectors;

/**
 * Created by mstafford on 8/10/16.
 *
 * Generate a UPPAAL project with corresponding templates for each Soar production.
 */
public class UPPAALCreator extends SoarBaseVisitor<Element>
{

    static final String LITERAL_STRING_PREFIX = "literal_string__";

    private class UPPAALElementWithXY extends DefaultElement
    {

        UPPAALElementWithXY(String s)
        {
            super(s);
            this.addAttribute("x", "5");
            this.addAttribute("y", "5");
        }

    }

    private final Set<String> _booleanGlobals;
    private final Map<String, Map<String, String>> _variableDictionary;
    private final Document _doc = DocumentHelper.createDocument();
    private final Set<String> _templateNames = new HashSet<>();
    private Integer _locationCounter = 0;
    private final Set<String> _globals;
    private SoarParser.Soar_productionContext _goalProductionContext;

    public UPPAALCreator(Set<String> stringAttributeNames, SoarParser.SoarContext soar, Map<String, Map<String, String>> variablesPerProductionContext, Set<String> boolAttributeNames)
    {
        _globals = stringAttributeNames;
        _booleanGlobals = boolAttributeNames;
        _doc.setXMLEncoding("utf-8");
        _doc.setDocType(new DefaultDocumentType("nta", "-//Uppaal Team//DTD Flat System 1.1//EN", "http://www.it.uu.se/research/group/darts/uppaal/flat-1_2.dtd"));
        _variableDictionary = variablesPerProductionContext;
        _doc.setRootElement(soar.accept(this));
    }

    public String getXML()
    {
        return _doc.asXML();
    }

    private Element getDeclarationElement()
    {
        Element decl = new DefaultElement("declaration");

        _globals.remove("nil"); // added later so that nil always equals 0

        String vars = "";

        final AtomicInteger i = new AtomicInteger(1);

        vars += _globals
                .stream()
                .filter(var -> var.startsWith("state"))
                .map(this::simplifiedString)
                .map(var -> "int " + var + "; \n")
                .collect(Collectors.joining());

        vars += _booleanGlobals
                .stream()
                .map(this::simplifiedString)
                .map(var -> "bool "+ var + "; \n")
                .collect(Collectors.joining());

        vars += "const int nil = 0;\n";

        vars += _globals
                .stream()
                .filter(var -> !var.startsWith("state"))
                .map(this::simplifiedString)
                .map(var -> "const int " + var + " = " + i.getAndIncrement() + "; \n")
                .collect(Collectors.joining());


        decl.addText("\n" + vars);
        decl.addText("broadcast chan Run_Rule;\n");

        return decl;
    }

    private Element getScheduler()
    {
        Element template = new DefaultElement("template");
        template.add(new DefaultElement("name").addText("scheduler"));

        String checkID = getCounter();
        String runID = getCounter();
        String startID = getCounter();

        template.add(getLocationWithNameElement(checkID, "Check"));

        Element runLocation = getLocationWithNameElement(runID, "Run");
        runLocation.add(new DefaultElement("committed"));
        template.add(runLocation);

        template.add(getLocationWithNameElement(startID, "Start"));
        template.add(new DefaultElement("init").addAttribute("ref", "id" + startID));
        template.add(getTransitionWithText(checkID, runID, "synchronisation", "Run_Rule!"));
        template.add(getTransitionWithText(runID, checkID, "guard", "!(" + _goalProductionContext.condition_side().accept(this).getText() + ")"));
        template.add(getTransitionWithText(startID, runID, "synchronisation", "Run_Rule!"));

        return template;
    }

    private String getCounter()
    {
        String i = _locationCounter.toString();
        _locationCounter++;
        return i;
    }

    private Element getLocationWithNameElement(String num, String nameText)
    {
        Element runLocation = new UPPAALElementWithXY("location").addAttribute("id", "id" + num);

        Element runName = new UPPAALElementWithXY("name").addText(nameText);

        runLocation.add(runName);

        return runLocation;
    }

    private Element getTransitionWithText(String sourceID, String targetID, String kind, String text)
    {
        Element startToRun = new DefaultElement("transition");

        Element source = new DefaultElement("source").addAttribute("ref", "id" + sourceID);

        Element target = new DefaultElement("target").addAttribute("ref", "id" + targetID);

        Element label = new UPPAALElementWithXY("label").addAttribute("kind", kind).addText(text);

        startToRun.add(source);
        startToRun.add(target);
        startToRun.add(label);

        return startToRun;
    }

    private Element getStartToRunTransitionElement(String runStateID, String startStateID, SoarParser.Soar_productionContext ctx)
    {
        Element startToRun = new DefaultElement("transition");
        Element source = new DefaultElement("source").addAttribute("ref", "id" + startStateID);
        Element target = new DefaultElement("target").addAttribute("ref", "id" + runStateID);

        startToRun.add(source);
        startToRun.add(target);

        startToRun.add(ctx.condition_side().accept(this));

        // add run rule sync label
        Element syncLabel = new UPPAALElementWithXY("label").addAttribute("kind", "synchronisation").addText("Run_Rule?");
        startToRun.add(syncLabel);

        startToRun.add(ctx.action_side().accept(this));

        return startToRun;
    }

    private Element getSystemElement()
    {
        final Element system = new DefaultElement("system").addText("\n");
        List<String[]> compoundNames = _templateNames.stream().map(name -> new String[]{name + "_0", name}).collect(Collectors.toList());
        String goalTemplateName = simplifiedString(_goalProductionContext.sym_constant().getText());

        system.addText(compoundNames.stream().map(name -> name[0] + " = " + name[1] + "(); \n").collect(Collectors.joining()));
        system.addText("schd = scheduler();\n");
        system.addText("goal = " + goalTemplateName + "(); \n");

        String instantiation = "system " + compoundNames.stream().map(cName -> cName[0]).collect(Collectors.joining(", ")) + ", goal, schd;";

        system.addText(instantiation);
        return system;
    }

    private Element getNameElement(String text)
    {
        return new UPPAALElementWithXY("name").addText(simplifiedString(text));
    }

    @Override
    public Element visitSoar(SoarParser.SoarContext ctx)
    {
        ctx.soar_production().forEach(sp -> sp.accept(this));

        final Element nta = new DefaultElement("nta");

        nta.add(getDeclarationElement());

        // Add template object for each production
        ctx.soar_production().stream().map(sp -> sp.accept(this)).filter(sp -> sp != null).forEach(nta::add);

        // Add scheduler to call 'Run Rule'
        nta.add(getScheduler());

        // Add system tag to instantiate all rules
        nta.add(getSystemElement());

        return nta;
    }

    @Override
    public Element visitSoar_production(SoarParser.Soar_productionContext ctx)
    {
        if (ctx.getText().contains("(halt)"))
        {
            _goalProductionContext = ctx;
        }

        String runStateID = getCounter();
        String startStateID = getCounter();

        Element productionElement = new DefaultElement("template");
        Element templateElement = getNameElement(ctx.sym_constant().getText());
        _templateNames.add(templateElement.getText());
        productionElement.add(templateElement);
        productionElement.add(new DefaultElement("declaration"));

        productionElement.add(getLocationWithNameElement(runStateID, "Run"));

        Element startState = getLocationWithNameElement(startStateID, "Start");
        startState.add(new DefaultElement("committed"));
        productionElement.add(startState);

        Element init = new DefaultElement("init");
        init.addAttribute("ref", "id" + startStateID);
        productionElement.add(init);

        productionElement.add(getTransitionWithText(runStateID, startStateID, "synchronisation", "Run_Rule?"));
        productionElement.add(getStartToRunTransitionElement(runStateID, startStateID, ctx));

        return productionElement;
    }

    @Override
    public Element visitFlags(SoarParser.FlagsContext ctx)
    {
        return null;
    }

    @Override
    public Element visitCondition_side(SoarParser.Condition_sideContext ctx)
    {
        // get guards from conditions

        List<String> guards = new LinkedList<>();
        guards.add(ctx.state_imp_cond().accept(this).getText());
        guards.addAll(ctx.cond().stream().map(c -> c.accept(this).getText()).collect(Collectors.toList()));

        return new UPPAALElementWithXY("label")
                .addAttribute("kind", "guard")
                .addText(guards
                        .stream()
                        .filter(g -> !g.equals(""))
                        .collect(Collectors.joining(" && ")));
    }

    /**
     * Gets dependencies and wraps result of inner visit
     *
     * @param condCtx
     * @return
     */
    @Override
    public Element visitState_imp_cond(SoarParser.State_imp_condContext condCtx)
    {
        String productionName = ((SoarParser.Soar_productionContext) condCtx.parent.parent).sym_constant().getText();
        String idTest = condCtx.id_test().getText();
        Map<String, String> localVariableDictionary = _variableDictionary.get(productionName);

        return new DefaultElement("").addText(innerVisitConditionVisit(condCtx.attr_value_tests(), localVariableDictionary, idTest));
    }

    private String innerVisitConditionVisit(List<SoarParser.Attr_value_testsContext> attrValueTestsCtxs, Map<String, String> localVariableDictionary, String idTest)
    {
        List<String> stateVariableComparisons = new LinkedList<>();

        // Variable in left hand side
        if (localVariableDictionary.containsKey(idTest))
        {
            String variablePath = localVariableDictionary.get(idTest);

            // Build the comparisons
            for (SoarParser.Attr_value_testsContext attributeCtx : attrValueTestsCtxs)
            {
                String attrPath = attributeCtx.attr_test().stream().map(RuleContext::getText).collect(Collectors.joining("_"));

                String leftTerm = variablePath + "_" + attrPath;

                if (attributeCtx.getText().startsWith("-^"))
                {
                    stateVariableComparisons.add(leftTerm + " == nil");
                }
                else
                {
                    int numberOfValues = attributeCtx.value_test().size();

                    if (numberOfValues == 1)
                    {
                        Element relationAndRightTerm = attributeCtx.value_test(0).accept(this);

                        String relation = relationAndRightTerm.attributeValue("rel");
                        String rightTerm;

                        if (relation.equals("="))
                        {
                            relation = "==";
                        }

                        if (relationAndRightTerm.attribute("var") != null)
                        {
                            rightTerm = localVariableDictionary.get(relationAndRightTerm.attributeValue("var"));
                        }
                        else
                        {
                            rightTerm = relationAndRightTerm.attributeValue("const");
                        }

                        if (rightTerm == null)
                        {
                            break;
                        }
                        else if (rightTerm.equals("true") && relation.equals("=="))
                        {
                            stateVariableComparisons.add(simplifiedString(leftTerm));
                        }
                        else if (rightTerm.equals("false") && relation.equals("=="))
                        {
                            stateVariableComparisons.add("!"+simplifiedString(leftTerm));
                        }
                        else if (!rightTerm.equals(leftTerm))
                        {
                            stateVariableComparisons.add(simplifiedString(leftTerm) + " " + relation + " " + simplifiedString(rightTerm));
                        }
                    }
                    else
                    {

                        // use "path_to_var[index] = constant" pattern
                    }
                }
            }
        }

        return stateVariableComparisons
                .stream()
                .filter(c -> c != null && !c.equals(""))
                .collect(Collectors.joining(" && "));
    }

    @Override
    public Element visitCond(SoarParser.CondContext ctx)
    {
        return ctx.positive_cond().accept(this);
    }

    @Override
    public Element visitPositive_cond(SoarParser.Positive_condContext ctx)
    {
        return ctx.conds_for_one_id().accept(this);
    }

    @Override
    public Element visitConds_for_one_id(SoarParser.Conds_for_one_idContext ctx)
    {
        String productionName = ((SoarParser.Soar_productionContext) ctx.parent.parent.parent.parent).sym_constant().getText();
        String idTest = ctx.id_test().getText();
        Map<String, String> localVariableDictionary = _variableDictionary.get(productionName);

        return new DefaultElement("").addText(innerVisitConditionVisit(ctx.attr_value_tests(), localVariableDictionary, idTest));
    }

    @Override
    public Element visitId_test(SoarParser.Id_testContext ctx)
    {
        return null;
    }

    @Override
    public Element visitAttr_value_tests(SoarParser.Attr_value_testsContext ctx)
    {
        return null;
    }

    @Override
    public Element visitAttr_test(SoarParser.Attr_testContext ctx)
    {
        return null;
    }

    @Override
    public Element visitValue_test(SoarParser.Value_testContext ctx)
    {
        return ctx.children.get(0).accept(this);
    }

    @Override
    public Element visitTest(SoarParser.TestContext ctx)
    {
        return ctx.children.get(0).accept(this);
    }

    @Override
    public Element visitConjunctive_test(SoarParser.Conjunctive_testContext ctx)
    {
        return null;
    }

    @Override
    public Element visitSimple_test(SoarParser.Simple_testContext ctx)
    {
        return ctx.children.get(0).accept(this);
    }

    @Override
    public Element visitMulti_value_test(SoarParser.Multi_value_testContext ctx)
    {
        return null;
    }

    @Override
    public Element visitDisjunction_test(SoarParser.Disjunction_testContext ctx)
    {
        return null;
    }

    @Override
    public Element visitRelational_test(SoarParser.Relational_testContext ctx)
    {
        String relation = "==";

        if (ctx.relation() != null)
        {
            relation = ctx.relation().getText();

            if (relation.equals("<>"))
            {
                relation = "!=";
            }
        }
        return ctx.single_test().accept(this).addAttribute("rel", relation);
    }

    @Override
    public Element visitRelation(SoarParser.RelationContext ctx)
    {
        return null;
    }

    @Override
    public Element visitSingle_test(SoarParser.Single_testContext ctx)
    {
        return ctx.children.get(0).accept(this);
    }

    @Override
    public Element visitVariable(SoarParser.VariableContext ctx)
    {
        return new DefaultElement("").addAttribute("var", ctx.getText());
    }

    @Override
    public Element visitConstant(SoarParser.ConstantContext ctx)
    {
        String result = simplifiedString(ctx.getText());

        if (ctx.Print_string() != null)
        {
            result = LITERAL_STRING_PREFIX + ctx.Print_string().getText().split("|")[1];
        }

        return new DefaultElement("").addAttribute("const", result);
    }

    @Override
    public Element visitAction_side(SoarParser.Action_sideContext ctx)
    {
        // get assignments from actions
        return new UPPAALElementWithXY("label")
                .addAttribute("kind", "assignment")
                .addText(ctx.action()
                        .stream()
                        .map(c -> c.accept(this).getText())
                        .filter(t -> t != null && !t.equals(""))
                        .collect(Collectors.joining(", ")));
    }

    @Override
    public Element visitAction(SoarParser.ActionContext ctx)
    {
        String productionName = ((SoarParser.Soar_productionContext) ctx.parent.parent).sym_constant().getText();
        Map<String, String> localDictionary = _variableDictionary.get(productionName);
        String prefix = localDictionary.get(ctx.variable().getText());

        return new DefaultElement("").addText(innerVisitAction(prefix, ctx.attr_value_make()));
    }

    private String innerVisitAction(String prefix, List<SoarParser.Attr_value_makeContext> ctxs)
    {
        Map<String, String[]> stateAssignments = new HashMap<>();

        for (SoarParser.Attr_value_makeContext attrCtx : ctxs)
        {
            String suffix = attrCtx.variable_or_sym_constant()
                    .stream()
                    .map(RuleContext::getText)
                    .collect(Collectors.joining("_"));

            String leftSide = prefix + "_" + suffix;

            Element rightSideElement = attrCtx.value_make().accept(this);
            String[] rightSide = determineAssignment(leftSide, rightSideElement, stateAssignments);

            if (rightSide != null)
            {
                stateAssignments.put(leftSide, rightSide);
            }
        }
        return stateAssignments.entrySet().stream()
                .map(e -> simplifiedString(e.getKey()) + " = " + e.getValue()[0])
                .collect(Collectors.joining(", "));
    }

    private String[] determineAssignment(String leftSide, Element rightSideElement, Map<String, String[]> stateAssignments)
    {
        if (rightSideElement == null)
        {
            return null;
        }

        String rightSide;
        String prefs;

        if (rightSideElement.attributeValue("const") != null)
        {
            rightSide = rightSideElement.attributeValue("const");
        }
        else if (rightSideElement.attributeValue("expr") != null)
        {
            rightSide = rightSideElement.attributeValue("expr");
        }
        else
        {
            return null;
        }

        if (rightSideElement.attributeValue("pref") != null)
        {
            prefs = rightSideElement.attributeValue("pref");
        }
        else
        {
            prefs = "+";
        }

        if (stateAssignments.containsKey(leftSide))
        {
            String currentPrefs = stateAssignments.get(leftSide)[1];

            String bestPref = getBestPreference(prefs, currentPrefs);

            if (bestPref.equals(prefs))
            {
                return new String[]{rightSide, prefs};
            }
            else
            {
                return null;
            }
        }
        else
        {
            return new String[]{rightSide, prefs};
        }
    }

    private String getBestPreference(String pref1, String pref2)
    {
        if (pref1.contains("~") && !pref2.contains("~"))
        {
            return pref2;
        }
        else if (pref2.contains("~") && !pref1.contains("~"))
        {
            return pref1;
        }
        else
        {
            String orderedPreferences = "!>+=<";
            for (int i = 0; i < orderedPreferences.length(); i++)
            {
                String nextPref = orderedPreferences.substring(i,i);

                if (pref1.contains(nextPref) && !pref2.contains(nextPref))
                {
                    return pref1;
                }
            }
        }
        return pref1;
    }

    @Override
    public Element visitPrint(SoarParser.PrintContext ctx)
    {
        return null;
    }

    @Override
    public Element visitFunc_call(SoarParser.Func_callContext ctx)
    {
        String productionName = ((SoarParser.Soar_productionContext) ctx.parent.parent.parent.parent.parent.parent).sym_constant().getText();
        Map<String, String> localDictionary = _variableDictionary.get(productionName);

        SoarParser.ValueContext leftContext = ctx.value(0);
        SoarParser.ValueContext rightContext = ctx.value(1);

        String leftSide = leftContext.variable() == null ? leftContext.constant().getText() : localDictionary.get(leftContext.getText());

        String result;

        if (ctx.func_name().getText().equals("-") && rightContext == null)
        {
            result = "0 - " + simplifiedString(leftSide);
        }
        else
        {
            String rightSide = rightContext.variable() == null ? rightContext.constant().getText() : localDictionary.get(rightContext.getText());
            String funcName = ctx.func_name().getText();

            if ("+-/*".contains(ctx.func_name().getText()))
            {
                result = simplifiedString(leftSide + " " + funcName + " " + rightSide);
            }
            else
            {
                result = "";
            }
        }

        return new DefaultElement("").addAttribute("expr", result);
    }

    @Override
    public Element visitFunc_name(SoarParser.Func_nameContext ctx)
    {
        return null;
    }

    @Override
    public Element visitValue(SoarParser.ValueContext ctx)
    {
        return ctx.children.get(0).accept(this);
    }

    @Override
    public Element visitAttr_value_make(SoarParser.Attr_value_makeContext ctx)
    {
        String leftSide = ctx.variable_or_sym_constant()
                .stream()
                .map(RuleContext::getText)
                .collect(Collectors.joining("_"));

        Element rightSide = ctx.value_make().accept(this);

        if (rightSide == null)
        {
            return new DefaultElement("");
        }
        else
        {
            return new DefaultElement("").addText(leftSide + " = " + rightSide.getText());
        }
    }

    @Override
    public Element visitVariable_or_sym_constant(SoarParser.Variable_or_sym_constantContext ctx)
    {
        return null;
    }

    @Override
    public Element visitValue_make(SoarParser.Value_makeContext ctx)
    {
        Element resultantElement = ctx.value(0).accept(this);

        long preferences = ctx.pref_specifier().size();

        if (preferences > 0)
        {
            String concatenatedPreferences = ctx.pref_specifier()
                    .stream()
                    .map(RuleContext::getText)
                    .collect(Collectors.joining());

            resultantElement.addAttribute("pref", concatenatedPreferences);
        }

        return resultantElement;
    }

    @Override
    public Element visitPref_specifier(SoarParser.Pref_specifierContext ctx)
    {
        return null;
    }

    @Override
    public Element visitUnary_pref(SoarParser.Unary_prefContext ctx)
    {
        return null;
    }

    @Override
    public Element visitUnary_or_binary_pref(SoarParser.Unary_or_binary_prefContext ctx)
    {
        return null;
    }

    @Override
    public Element visit(ParseTree parseTree)
    {
        return null;
    }

    @Override
    public Element visitChildren(RuleNode ruleNode)
    {
        return null;
    }

    @Override
    public Element visitTerminal(TerminalNode terminalNode)
    {
        return null;
    }

    @Override
    public Element visitErrorNode(ErrorNode errorNode)
    {
        return null;
    }

    private String simplifiedString(String str)
    {
        return str.replace("-", "_").replace("*", "_");
    }
}
