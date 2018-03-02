package edu.fit.hiai.lvca.translator.soar;

import com.uppaal.model.core2.*;
import edu.fit.hiai.lvca.antlr4.SoarBaseVisitor;
import edu.fit.hiai.lvca.antlr4.SoarParser;
import org.antlr.v4.runtime.RuleContext;
import org.antlr.v4.runtime.tree.ErrorNode;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.RuleNode;
import org.antlr.v4.runtime.tree.TerminalNode;

import java.io.IOException;
import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Collectors;

public class UPPAALSemanticVisitor extends SoarBaseVisitor<Node> {

    static final String LITERAL_STRING_PREFIX = "literal_string__";
    private final Set<String> _globals;
    private final Set<String> _booleanGlobals;
    private final Map<String, Map<String, String>> _variableDictionary;
    private SoarParser.Soar_productionContext _goalProductionContext;
    private Integer _locationCounter = 0;
    Document ourDocument = new Document(new PrototypeDocument());
    private Template lastTemplate = null;
    private final Set<String> _templateNames = new HashSet<>();

    public UPPAALSemanticVisitor(Set<String> stringAttributeNames, Map<String, Map<String, String>> variablesPerProductionContext, Set<String> boolAttributeNames)
    {
        _globals = stringAttributeNames;
        _booleanGlobals = boolAttributeNames;
        _variableDictionary = variablesPerProductionContext;
    }

    private String getCounter() {
        String i = _locationCounter.toString();
        _locationCounter++;
        return i;
    }

    private String simplifiedString(String str) {
        return str.replace("-", "_").replace("*", "_");
    }

    private void getDeclarationElement()
    {
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

        vars += "broadcast chan Run_Rule;\n";


        ourDocument.setProperty("declaration", vars);
    }

    private void getSystemElement()
    {
        List<String[]> compoundNames = _templateNames.stream().map(name -> new String[]{name + "_0", name}).collect(Collectors.toList());
        String goalTemplateName = simplifiedString(_goalProductionContext.sym_constant().getText());
        String system = "";
        system += compoundNames.stream().map(name -> name[0] + " = " + name[1] + "(); \n").collect(Collectors.joining());
        system += "schd = scheduler();\n";
        system += "goal = " + goalTemplateName + "(); \n";
        system += "system " + compoundNames.stream().map(cName -> cName[0]).collect(Collectors.joining(", ")) + ", goal, schd;";

        ourDocument.setProperty("system", system);
    }

    @Override
    public Node visitSoar(SoarParser.SoarContext ctx) {

        getDeclarationElement();

        ctx.soar_production().forEach(sp -> sp.accept(this));

        getScheduler();

        getSystemElement();


        try {
            ourDocument.save("sampledoc.xml");
        } catch (IOException er) {
            er.printStackTrace(System.err);
        }

        return null;
    }

    @Override
    public Node visitSoar_production(SoarParser.Soar_productionContext ctx) {
        if (ctx.getText().contains("(halt)")) {
            _goalProductionContext = ctx;
        }

        String runStateID = getCounter();
        String startStateID = getCounter();

        Template currentTemplate = makeTemplate(simplifiedString(ctx.sym_constant().getText()));
        _templateNames.add(getText(currentTemplate, "name"));

        Location runLocation = makeLocation(currentTemplate, "Run", runStateID, false, false);

        Location startLocation = makeLocation(currentTemplate, "Start", startStateID, true, true);

        makeEdge(currentTemplate, runLocation, startLocation, "Run_Rule?", null, null);

        String guard = (String) ctx.condition_side().accept(this).getProperty("name").getValue();
        String assignment = (String) ctx.action_side().accept(this).getProperty("name").getValue();
        makeEdge(currentTemplate, startLocation, runLocation, "Run_Rule?", guard, assignment);

        return null;
    }

    @Override
    public Node visitFlags(SoarParser.FlagsContext ctx) {
        return null;
    }

    @Override
    public Node visitCondition_side(SoarParser.Condition_sideContext ctx) {
        List<String> guards = new LinkedList<>();
        guards.add((String) ctx.state_imp_cond().accept(this).getProperty("name").getValue());
        guards.addAll(ctx.cond().stream().map(c -> getText(c.accept(this), "name")).collect(Collectors.toList()));
        return textAsNode("name", guards
                .stream()
                .filter(g -> g != null && !g.equals(""))
                .collect(Collectors.joining(" && ")));
    }

    private Node textAsNode(String property, String text)
    {
        Node node = generateNode();
        node.setProperty(property, text);
        return node;
    }

    private String getText(Node accept, String property)
    {
        return (String) accept.getProperty(property).getValue();
    }

    private Node generateNode()
    {
        return ourDocument.createTemplate();
    }

    @Override
    public Node visitState_imp_cond(SoarParser.State_imp_condContext ctx) {

        String productionName = ((SoarParser.Soar_productionContext) ctx.parent.parent).sym_constant().getText();
        String idTest = ctx.id_test().getText();
        Map<String, String> localVariableDictionary = _variableDictionary.get(productionName);
        return textAsNode("name", innerConditionVisit(ctx.attr_value_tests(), localVariableDictionary, idTest));
    }

    private String innerConditionVisit(List<SoarParser.Attr_value_testsContext> attrValueTestsCtxs, Map<String, String> localVariableDictionary, String idTest)
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
                        Node relationAndRightTerm = attributeCtx.value_test(0).accept(this);

                        String relation = getText(relationAndRightTerm, "rel");
                        String rightTerm;

                        if (relation.equals("="))
                        {
                            relation = "==";
                        }

                        if (relationAndRightTerm.getProperty("var") != null)
                        {
                            rightTerm = localVariableDictionary.get(getText(relationAndRightTerm,"var"));
                        }
                        else
                        {
                            rightTerm = getText(relationAndRightTerm, "const");
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
    public Node visitCond(SoarParser.CondContext ctx) {
        return ctx.positive_cond().accept(this);
    }

    @Override
    public Node visitPositive_cond(SoarParser.Positive_condContext ctx) {
        return ctx.conds_for_one_id().accept(this);
    }

    @Override
    public Node visitConds_for_one_id(SoarParser.Conds_for_one_idContext ctx) {
        String productionName = ((SoarParser.Soar_productionContext) ctx.parent.parent.parent.parent).sym_constant().getText();
        String idTest = ctx.id_test().getText();
        Map<String, String> localVariableDictionary = _variableDictionary.get(productionName);

        return textAsNode("name", innerConditionVisit(ctx.attr_value_tests(), localVariableDictionary, idTest));
    }

    @Override
    public Node visitId_test(SoarParser.Id_testContext ctx) {
        return null;
    }

    @Override
    public Node visitAttr_value_tests(SoarParser.Attr_value_testsContext ctx) {
        return null;
    }

    @Override
    public Node visitAttr_test(SoarParser.Attr_testContext ctx) {
        return null;
    }

    @Override
    public Node visitValue_test(SoarParser.Value_testContext ctx) {
        return ctx.children.get(0).accept(this);
    }

    @Override
    public Node visitTest(SoarParser.TestContext ctx) {
        return ctx.children.get(0).accept(this);
    }

    @Override
    public Node visitConjunctive_test(SoarParser.Conjunctive_testContext ctx) {
        return null;
    }

    @Override
    public Node visitSimple_test(SoarParser.Simple_testContext ctx) {
        return ctx.children.get(0).accept(this);
    }

    @Override
    public Node visitMulti_value_test(SoarParser.Multi_value_testContext ctx) {
        return null;
    }

    @Override
    public Node visitDisjunction_test(SoarParser.Disjunction_testContext ctx) {
        return null;
    }

    @Override
    public Node visitRelational_test(SoarParser.Relational_testContext ctx) {
        String relation = "==";

        if (ctx.relation() != null)
        {
            relation = ctx.relation().getText();

            if (relation.equals("<>"))
            {
                relation = "!=";
            }
        }
        Node returnNode = ctx.single_test().accept(this);
        returnNode.setProperty("rel", relation);
        return returnNode;
    }

    @Override
    public Node visitRelation(SoarParser.RelationContext ctx) {
        return null;
    }

    @Override
    public Node visitSingle_test(SoarParser.Single_testContext ctx) {
        return ctx.children.get(0).accept(this);
    }

    @Override
    public Node visitVariable(SoarParser.VariableContext ctx) {
        return textAsNode("var", ctx.getText());
    }

    @Override
    public Node visitConstant(SoarParser.ConstantContext ctx) {
        String result = simplifiedString(ctx.getText());

        if (ctx.Print_string() != null)
        {
            result = LITERAL_STRING_PREFIX + ctx.Print_string().getText().split("|")[1];
        }
        return textAsNode("const", result);
    }

    @Override
    public Node visitAction_side(SoarParser.Action_sideContext ctx) {
    return textAsNode("name", ctx.action()
                        .stream()
                        .map(action -> getText(action.accept(this), "name"))
                        .filter(t -> t != null && !t.equals(""))
                        .collect(Collectors.joining(", ")));
    }

    @Override
    public Node visitAction(SoarParser.ActionContext ctx) {
        String productionName = ((SoarParser.Soar_productionContext) ctx.parent.parent).sym_constant().getText();
        Map<String, String> localDictionary = _variableDictionary.get(productionName);
        String prefix = localDictionary.get(ctx.variable().getText());

        return textAsNode("name", innerVisitAction(prefix, ctx.attr_value_make()));
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

            Node rightSideElement = attrCtx.value_make().accept(this);
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

    private String[] determineAssignment(String leftSide, Node rightSideElement, Map<String, String[]> stateAssignments)
    {
        if (rightSideElement == null)
        {
            return null;
        }

        String rightSide;
        String prefs;

        if (rightSideElement.getProperty("const") != null)
        {
            rightSide = getText(rightSideElement, "const");
        }
        else if (rightSideElement.getProperty("expr") != null)
        {
            rightSide = getText(rightSideElement, "expr");
        }
        else
        {
            return null;
        }

        if (rightSideElement.getProperty("pref") != null)
        {
            prefs = getText(rightSideElement, "pref");
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
    public Node visitPrint(SoarParser.PrintContext ctx) {
        return null;
    }

    @Override
    public Node visitFunc_call(SoarParser.Func_callContext ctx) {
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

        return textAsNode("expr", result);
    }

    @Override
    public Node visitFunc_name(SoarParser.Func_nameContext ctx) {
        return null;
    }

    @Override
    public Node visitValue(SoarParser.ValueContext ctx) {
        return ctx.children.get(0).accept(this);
    }

    @Override
    public Node visitAttr_value_make(SoarParser.Attr_value_makeContext ctx) {
        String leftSide = ctx.variable_or_sym_constant()
                .stream()
                .map(RuleContext::getText)
                .collect(Collectors.joining("_"));

        Node rightSide = ctx.value_make().accept(this);

        if (rightSide == null) {
            return generateNode();
        } else {
            return textAsNode("name", leftSide + " = " + getText(rightSide, "name"));
        }
    }

    @Override
    public Node visitVariable_or_sym_constant(SoarParser.Variable_or_sym_constantContext ctx) {
        return null;
    }

    @Override
    public Node visitValue_make(SoarParser.Value_makeContext ctx) {
        Node resultantElement = ctx.value().accept(this);

        long preferences = ctx.pref_specifier().size();

        if (preferences > 0)
        {
            String concatenatedPreferences = ctx.pref_specifier()
                    .stream()
                    .map(RuleContext::getText)
                    .collect(Collectors.joining());

            resultantElement.setProperty("pref", concatenatedPreferences);
        }

        return resultantElement;
    }

    @Override
    public Node visitPref_specifier(SoarParser.Pref_specifierContext ctx) {
        return null;
    }

    @Override
    public Node visitUnary_pref(SoarParser.Unary_prefContext ctx) {
        return null;
    }

    @Override
    public Node visitUnary_or_binary_pref(SoarParser.Unary_or_binary_prefContext ctx) {
        return null;
    }

    @Override
    public Node visitSym_constant(SoarParser.Sym_constantContext ctx) {
        return null;
    }

    @Override
    public Node visit(ParseTree parseTree) {
        return null;
    }

    @Override
    public Node visitChildren(RuleNode ruleNode) {
        return null;
    }

    @Override
    public Node visitTerminal(TerminalNode terminalNode) {
        return null;
    }

    @Override
    public Node visitErrorNode(ErrorNode errorNode) {
        return null;
    }

    private Template makeTemplate(String name) {
        Template t = ourDocument.createTemplate();
        ourDocument.insert(t, lastTemplate);
        lastTemplate = t;
        t.setProperty("name", name);
        return t;
    }

    private Location makeLocation(Template t, String name, String ID, boolean committed, boolean init) {
        Location l = t.createLocation();
        t.insert(l, t.getLast());
        l.setProperty("name", name);
        l.setProperty("id", "id" + ID);
        if (committed) {
            l.setProperty("committed", true);
        }
        if (init) {
            l.setProperty("init", true);
        }
        return l;
    }

    private Edge makeEdge(Template t, Location source, Location target, String synchronisation, String guard, String assignment) {
        Edge e = t.createEdge();
        t.insert(e, t.getLast());
        e.setSource(source);
        e.setTarget(target);
        if (synchronisation != null) {
            e.setProperty("synchronisation", synchronisation);
        }
        if (guard != null) {
            e.setProperty("guard", guard);
        }
        if (assignment != null) {
            e.setProperty("assignment", assignment);
        }
        return e;
    }

    private Element getScheduler()
    {
        String checkId = getCounter();
        String runId = getCounter();
        String startId = getCounter();

        Template schedulerTemplate = makeTemplate("scheduler");

        Location checkLocation = makeLocation(schedulerTemplate, "Check", checkId, true, false);

        Location runLocation = makeLocation(schedulerTemplate, "Run", runId, true, false);

        Location startLocation = makeLocation(schedulerTemplate, "Start", startId, false, true);

        makeEdge(schedulerTemplate, checkLocation, runLocation, "Run_Rule!", null, null);

        makeEdge(schedulerTemplate, runLocation, checkLocation, null, "!(" + getText(_goalProductionContext.condition_side().accept(this), "name") + ")", null);

        makeEdge(schedulerTemplate, startLocation, runLocation, "Run_Rule!", null, null);
        return null;
    }
}
