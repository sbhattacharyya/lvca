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
    private final ArrayList<SymbolTree> _operators;
    private final Map<String, Map<String, String>> _variableDictionary;
    private SoarParser.Soar_productionContext _goalProductionContext;
    private Integer _locationCounter = 0;
    Document ourDocument = new Document(new PrototypeDocument());
    private Template lastTemplate = null;
    private final Set<String> _templateNames = new HashSet<>();

    public UPPAALSemanticVisitor(Set<String> stringAttributeNames, Map<String, Map<String, String>> variablesPerProductionContext, Set<String> boolAttributeNames, ArrayList<SymbolTree> operators)
    {
        _globals = stringAttributeNames;
        _booleanGlobals = boolAttributeNames;
        _variableDictionary = variablesPerProductionContext;
        _operators = operators;
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

        vars += "\n" +
                "int id = 1;\n" +
                "const int N = " + _operators.size() + ";\n" +
                "\n" +
                "typedef struct {\n" +
                "\tbool isRequired;\n" +
                "\tbool isAcceptable;\n" +
                "\tbool isBest;\n" +
                "\tbool isWorst;\n" +
                "\tbool isProhibited;\n" +
                "\tbool isRejected;\n" +
                "\tbool isUnaryIndifferent;\n" +
                "\tbool hasNumericIndifferent;\n" +
                "\tint numericIndifferent;\n" +
                "\tint id;\n" +
                "} BaseOperator;\n" +
                "typedef struct {\n" +
                "\tBaseOperator operator;\n" +
                "\tint better[N];\n" +
                "\tint binaryIndifferent[N];\n" +
                "} Operator;\n" +
                "\n" +
                "Operator operators[N];\n" +
                "int required[N];\n" +
                "int acceptable[N];\n" +
                "int best[N];\n" +
                "chan requireTest;\n" +
                "BaseOperator defaultOperator = {false, false, false, false, false, false, false, false, 0, 0};\n" +
                "int defaultOperatorArray[N];\n" +
                "int numLeft = 0;\n" +
                "int finalOp;\n" +
                "\n" +
                "int getNumLeft(int &ref[N]) {\n" +
                "\tint i = 0;\n" +
                "\tint count = 0;\n" +
                "\twhile (i < N && ref[i] != 0) {\n" +
                "\t\t\tcount++;\n" +
                "\t\t\ti++;\n" +
                "\t}\n" +
                "\treturn count;\n" +
                "}\n" +
                "\n" +
                "void initialize(Operator &op[N]) {\n" +
                "\tint i = 0;\n" +
                "\tfor (i = 0; i < N; i++) {\n" +
                "\t\tdefaultOperatorArray[i] = 0;\n" +
                "\t}\n" +
                "\tfor (i = 0; i < N; i++) {\n" +
                "\t\tBaseOperator def = {false, false, false, false, false, false, false, false, 0, id};\n" +
                "\t\top[i].operator = def;\n" +
                "\t\top[i].better = defaultOperatorArray;\n" +
                "\t\top[i].binaryIndifferent = defaultOperatorArray;\n" +
                "\t\tid++;\n" +
                "\t}\n" +
                "}\n" +
                "\n" +
                "void fillOthers() {\n" +
                "\tint i = 0;\n" +
                "\tint requiredIndex = 0;\n" +
                "\tint acceptableIndex = 0;\n" +
                "\tint bestIndex = 0;\n" +
                "\tfor (i = 0; i < N; i++) {\n" +
                "\t\tif (operators[i].operator.isRequired) {\n" +
                "\t\t\trequired[requiredIndex] = operators[i].operator.id;\n" +
                "\t\t\trequiredIndex++;\n" +
                "\t\t}\n" +
                "\t\tif (operators[i].operator.isAcceptable) {\n" +
                "\t\t\tacceptable[acceptableIndex] = operators[i].operator.id;\n" +
                "\t\t\tacceptableIndex++;\n" +
                "\t\t} \n" +
                "\t\tif (operators[i].operator.isBest) {\n" +
                "\t\t\tbest[bestIndex] = operators[i].operator.id;\n" +
                "\t\t\tbestIndex++;\n" +
                "\t\t}\n" +
                "\t}\n" +
                "}";


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
        system += "preferenceResolution = preferenceResolutionTemplate(); \n";
        system += "system " + compoundNames.stream().map(cName -> cName[0]).collect(Collectors.joining(", ")) + ", goal, schd, preferenceResolution;";

        ourDocument.setProperty("system", system);
    }

    @Override
    public Node visitSoar(SoarParser.SoarContext ctx) {

        ctx.soar_production().forEach(sp -> sp.accept(this));

        getDeclarationElement();

        getScheduler();

        getOperatorPreferences();

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

        Location runLocation = makeLocationWithCoordinates(currentTemplate, "Run", runStateID, false, false, 232, -80, 248, -80);

        Location startLocation = makeLocationWithCoordinates(currentTemplate, "Start", startStateID, true, true, -152, -80, -208, -80);

        makeEdgeWithNails(currentTemplate, runLocation, startLocation, null, null, "Run_Rule?", new Integer[]{16, -192}, null, null, null, null, new Integer[]{40, -168});

        String guard = (String) ctx.condition_side().accept(this).getProperty("name").getValue();
        String assignment = (String) ctx.action_side().accept(this).getProperty("name").getValue();
        makeEdge(currentTemplate, startLocation, runLocation, null, null, "Run_Rule?", new Integer[]{8, -104}, guard, new Integer[]{-152, -48}, assignment, new Integer[]{-152, -64});

        return null;
    }

    @Override
    public Node visitFlags(SoarParser.FlagsContext ctx) {
        return null;
    }

    @Override
    public Node visitCondition_side(SoarParser.Condition_sideContext ctx) {
        List<String> guards = new LinkedList<>();
        guards.add(getText(ctx.state_imp_cond().accept(this), "name"));
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

            Node rightSideElement = attrCtx.value_make(0).accept(this);
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
            return null;
        }
        else
        {
            return new String[]{rightSide, prefs};
        }
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

        Node rightSide = ctx.value_make(0).accept(this);

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
//todo FIX VISIT_VALUE_MAKE in UPPAAALSemanticVisitor
//    @Override
//    public Node visitValue_make(SoarParser.Value_makeContext ctx)
//    {
//        Node resultantElement = null;
//        for (SoarParser.ValueContext valueContext : ctx.value())
//        {
//            resultantElement = valueContext.accept(this);
//        }
//
//        long preferences = ctx.pref_specifier().size();
//
//        if (preferences > 0) {
//            String concatenatedPreferences = ctx.pref_specifier()
//                    .stream()
//                    .map(RuleContext::getText)
//                    .collect(Collectors.joining());
//            resultantElement.setProperty("pref", concatenatedPreferences);
//        }
//        return resultantElement;
//    }

//    @Override
//    public Node visitPref_specifier(SoarParser.Pref_specifierContext ctx) {
//        return null;
//    }

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
        if (name != null) {
            l.setProperty("name", name);
        }
        l.setProperty("id", "id" + ID);
        if (committed) {
            l.setProperty("committed", true);
        }
        if (init) {
            l.setProperty("init", true);
        }
        return l;
    }

    private Location makeLocationWithCoordinates(Template t, String name, String ID, boolean committed, boolean init, int x, int y, Integer nameX, Integer nameY) {
        Location ret = makeLocation(t, name, ID, committed, init);
        ret.setProperty("x", x);
        ret.setProperty("y", y);
        if (nameX != null) {
            Property nameProperty = ret.getProperty("name");
            nameProperty.setProperty("x", nameX);
            nameProperty.setProperty("y", nameY);
        }
        return ret;
    }

    private Edge makeEdge(Template t, Location source, Location target, String select, Integer[] selectXY, String synchronisation, Integer[] synchronisationXY, String guard, Integer[] guardXY, String assignment, Integer[] assignmentXY) {
        Edge e = t.createEdge();
        t.insert(e, t.getLast());
        e.setSource(source);
        e.setTarget(target);
        if (select != null) {
            Property s = e.setProperty("select", select);
            if (selectXY != null && selectXY.length >= 2) {
                s.setProperty("x", selectXY[0]);
                s.setProperty("y", selectXY[1]);
            }
        }
        if (synchronisation != null) {
            Property s = e.setProperty("synchronisation", synchronisation);
            if (synchronisationXY != null && synchronisationXY.length >= 2) {
                s.setProperty("x", synchronisationXY[0]);
                s.setProperty("y", synchronisationXY[1]);
            }
        }
        if (guard != null) {
            Property g = e.setProperty("guard", guard);
            if (guardXY != null && guardXY.length >= 2) {
                g.setProperty("x", guardXY[0]);
                g.setProperty("y", guardXY[1]);
            }
        }
        if (assignment != null) {
            Property a = e.setProperty("assignment", assignment);
            if (assignmentXY != null && assignmentXY.length >= 2) {
                a.setProperty("x", assignmentXY[0]);
                a.setProperty("y", assignmentXY[1]);
            }
        }
        return e;
    }

    private Edge makeEdgeWithNails(Template t, Location source, Location target, String select, Integer[] selectXY, String synchronisation, Integer[] synchronisationXY, String guard, Integer[] guardXY, String assignment, Integer[] assignmentXY, Integer[] nailsXY) {
        Edge ret = makeEdge(t, source, target, select, selectXY, synchronisation, synchronisationXY, guard, guardXY, assignment, assignmentXY);
        Nail n = ret.createNail();
        n.setProperty("x", nailsXY[0]);
        n.setProperty("y", nailsXY[1]);
        Node last = ret.insert(n, null);
        for (int i = 2; i < nailsXY.length; i += 2) {
            n = ret.createNail();
            n.setProperty("x", nailsXY[i]);
            n.setProperty("y", nailsXY[i+1]);
            last = ret.insert(n, last);
        }
        return ret;
    }

    private Element getScheduler()
    {
        String checkId = getCounter();
        String runId = getCounter();
        String startId = getCounter();

        Template schedulerTemplate = makeTemplate("scheduler");

        Location checkLocation = makeLocationWithCoordinates(schedulerTemplate, "Check", checkId, true, false, 248, -72, 264, -72);

        Location runLocation = makeLocationWithCoordinates(schedulerTemplate, "Run", runId, true, false, -144, -72, -128, -72);

        Location startLocation = makeLocationWithCoordinates(schedulerTemplate, "Start", startId, false, true, -368, -72, -424, -72);

        makeEdgeWithNails(schedulerTemplate, checkLocation, runLocation, null, null, "Run_Rule!", new Integer[]{24, -152}, null, null, null, null, new Integer[]{56, -128});

        makeEdgeWithNails(schedulerTemplate, runLocation, checkLocation, null, null, null, null, "!(" + getText(_goalProductionContext.condition_side().accept(this), "name") + ")", new Integer[]{-136, -48}, null, null, new Integer[]{128, -72});

        makeEdge(schedulerTemplate, startLocation, runLocation, null, null, "Run_Rule!", new Integer[]{-288, -96}, null, null, null, null);
        return null;
    }

    private Element getOperatorPreferences() {
        Template operatorPreferencesTemplate = makeTemplate("preferenceResolutionTemplate");
        operatorPreferencesTemplate.setProperty("declaration",
                "bool requiredAndProhibited;\n" +
                "int currentOp;\n" +
                "bool isRequiredAndProhibited() {\n" +
                "\tint i = 0;\n" +
                "\twhile (i < N && required[i] != 0) {\n" +
                "\t\tif (operators[required[i]-1].operator.isProhibited == 1) {\n" +
                "\t\t\treturn true;\n" +
                "\t\t}\n" +
                "\t\ti++;\n" +
                "\t}\n" +
                "\treturn false;\n" +
                "}\n" +
                "\n" +
                "void remove(int index, int &ref[N]) {\n" +
                "\tint i = index;\n" +
                "\twhile (i < N-1 && ref[i] != 0) {\n" +
                "\t\tref[i] = ref[i+1];\n" +
                "\t\ti++;\n" +
                "\t}\n" +
                "\tref[i] = 0;\n" +
                "} \n" +
                "\n" +
                "void removeProhibitedFromAcceptable() {\n" +
                "\tint i = 0;\n" +
                "\twhile (i < N && acceptable[i] != 0) {\n" +
                "\t\tif (operators[acceptable[i]-1].operator.isProhibited == 1) {\n" +
                "\t\t\tremove(i, acceptable);\n" +
                "\t\t} else {\n" +
                "\t\t\ti++;\n" +
                "\t\t}\n" +
                "\t}\n" +
                "}\n" +
                "\n" +
                "int contains(int testId) {\n" +
                "\tint i = 0;\n" +
                "\twhile (i < N && acceptable[i] != 0) {\n" +
                "\t\tif (acceptable[i] == testId) {\n" +
                "\t\t\treturn i;\n" +
                "\t\t}\n" +
                "\t\ti++;\n" +
                "\t}\n" +
                "\treturn -1;\n" +
                "}\n" +
                "\n" +
                "void removeWorseAndRejectedFromAcceptable() {\n" +
                "\tint i = 0;\n" +
                "\tint j = 0;\n" +
                "\tint k = 0;\n" +
                "\tbool temp[N];\n" +
                "\tint containID = -1;\n" +
                "\tfor (k = 0; k < N; k++) {\n" +
                "\t\ttemp[k] = false;\n" +
                "\t}\n" +
                "\ti = 0;\n" +
                "\twhile (i < N && acceptable[i] != 0) {\n" +
                "\t\tj = 0;\n" +
                "\t\twhile (j < N && operators[acceptable[i]-1].better[j] != 0) {\n" +
                "\t\t\tcontainID = contains(operators[acceptable[i]-1].better[j]);\n" +
                "\t\t\tif (!temp[operators[acceptable[i]-1].better[j] - 1] && containID != -1) {\n" +
                "\t\t\t\ttemp[operators[acceptable[i]-1].better[j] - 1] = true;\n" +
                "\t\t\t}\n" +
                "\t\t\tj++;\n" +
                "\t\t}\n" +
                "\t\tif (operators[acceptable[i]-1].operator.isRejected == 1 && !temp[acceptable[i] - 1]) {\n" +
                "\t\t\ttemp[acceptable[i] - 1] = true;\n" +
                "\t\t}\n" +
                "\t\ti++;\n" +
                "\t}\n" +
                "\ti = N-1;\n" +
                "\twhile (i >= 0) {\n" +
                "\t\tif (temp[i]) {\n" +
                "\t\t\tremove(i, acceptable);\n" +
                "\t\t}\n" +
                "\t\ti--;\t\n" +
                "\t}\n" +
                "}\n" +
                "\n" +
                "void removeBest() {\n" +
                "\tint i = 0;\n" +
                "\twhile (i < N && acceptable[i] != 0) {\n" +
                "\t\tif (operators[acceptable[i]-1].operator.isBest) {\n" +
                "\t\t\tremove(i, acceptable);\n" +
                "\t\t} else {\n" +
                "\t\t\ti++;\n" +
                "\t\t}\n" +
                "\t}\n" +
                "}\n" +
                "\n" +
                "void removeWorst() {\n" +
                "\tint i = 0;\n" +
                "\twhile (i < N && acceptable[i] != 0) {\n" +
                "\t\tif (operators[acceptable[i]-1].operator.isWorst) {\n" +
                "\t\t\tremove(i, acceptable);\n" +
                "\t\t} else {\n" +
                "\t\t\ti++;\n" +
                "\t\t}\n" +
                "\t}\n" +
                "}\n" +
                "\n" +
                "bool areAllIndifferent() {\n" +
                "\tint i = 0;\n" +
                "\tint j = 0;\n" +
                "\tbool temp[N];\n" +
                "\tfor(i = 0; i < N; i++) {\n" +
                "\t\ttemp[i] = false;\n" +
                "\t}\n" +
                "\ti = 0;\n" +
                "\twhile (i < N && acceptable[i] != 0) {\n" +
                "\t\tif (operators[acceptable[i]-1].operator.isUnaryIndifferent == 0 && operators[acceptable[i]-1].operator.hasNumericIndifferent == 0) {\n" +
                "\t\t\ttemp[acceptable[i]-1] = true;\n" +
                "\t\t}\n" +
                "\t\ti++;\n" +
                "\t}\n" +
                "\ti = 0;\n" +
                "\twhile (i < N) {\n" +
                "\t\tif (temp[i]) {\n" +
                "\t\t\tj = 0;\n" +
                "\t\t\tif (operators[i].binaryIndifferent[0] == 0) {\n" +
                "\t\t\t\treturn false;\n" +
                "\t\t\t}\n" +
                "\t\t\twhile(j < N && operators[i].binaryIndifferent[j] != 0) {\n" +
                "\t\t\t\tif(contains(operators[i].binaryIndifferent[j]) == -1) {\n" +
                "\t\t\t\t\treturn false;\n" +
                "\t\t\t\t}\n" +
                "\t\t\t\tj++;\n" +
                "\t\t\t}\n" +
                "\t\t}\n" +
                "\t\ti++;\n" +
                "\t}\n" +
                "\treturn true;\n" +
                "}\n" +
                "\n" +
                "int modulus(int num) {\n" +
                "\tif (num == 0) {\n" +
                "\t\treturn 0;\n" +
                "\t} else {\n" +
                "\t\tint d = num / numLeft;\n" +
                "\t\tint m = numLeft*d;\n" +
                "\t\tint r = num-m;\n" +
                "\t\treturn r;\n" +
                "\t}\n" +
                "}"
        );
        Location noName = makeLocationWithCoordinates(operatorPreferencesTemplate, null, getCounter(), true, false, -3488, -864, null, null);
        Location noName1 = makeLocationWithCoordinates(operatorPreferencesTemplate, null, getCounter(), true, false, -3488, -920, null, null);
        Location noName2 = makeLocationWithCoordinates(operatorPreferencesTemplate, null, getCounter(), true, false, -3488, -1120, null, null);
        Location tie = makeLocationWithCoordinates(operatorPreferencesTemplate,  "Tie", getCounter(), true, false, -2966, -706, -2976, -736);
        Location indifferentTest = makeLocationWithCoordinates(operatorPreferencesTemplate, "IndifferentTest", getCounter(), true, false, -3488, -624, -3616, -632);
        Location worstFilter = makeLocationWithCoordinates(operatorPreferencesTemplate, "WorstFilter", getCounter(), true, false, -3488, -816, -3592, -824);
        Location conflict = makeLocationWithCoordinates(operatorPreferencesTemplate, "Conflict", getCounter(), true, false, -2976, -1064, -2986, -1094);
        Location bestFilter = makeLocationWithCoordinates(operatorPreferencesTemplate, "BestFilter", getCounter(), true, false, -3488, -992, -3576, -1000);
        Location betterWorseFilter = makeLocationWithCoordinates(operatorPreferencesTemplate, "BetterWorseFilter", getCounter(), true, false, -3488, -1064, -3632, -1072);
        Location noChange = makeLocationWithCoordinates(operatorPreferencesTemplate, "NoChange", getCounter(), true, false, -2872, -1096, -2864, -1120);
        Location rejectFilter = makeLocationWithCoordinates(operatorPreferencesTemplate, "RejectFilter", getCounter(), true, false, -3488, -1192, -3592, -1200);
        Location prohibitFilter = makeLocationWithCoordinates(operatorPreferencesTemplate, "ProhibitFilter", getCounter(), true, false, -3488, -1264, -3600, -1272);
        Location acceptableCollect = makeLocationWithCoordinates(operatorPreferencesTemplate, "AcceptableCollect", getCounter(), true, false, -3488, -1336, -3640, -1344);
        Location done = makeLocationWithCoordinates(operatorPreferencesTemplate, "done", getCounter(), true, false, -2616, -520, -2598, -594);
        Location noName3 = makeLocationWithCoordinates(operatorPreferencesTemplate, null, getCounter(), true, false, -2976, -1424, null, null);
        Location constraintFailure = makeLocationWithCoordinates(operatorPreferencesTemplate, "ConstraintFailure", getCounter(), true, false, -2976, -1520, -2986, -1550);
        Location requireTest = makeLocationWithCoordinates(operatorPreferencesTemplate, "RequireTest", getCounter(), true, false, -3488, -1424, -3592, -1432);
        Location start = makeLocationWithCoordinates(operatorPreferencesTemplate, "Start", getCounter(), true, true, -3488, -1536, -3498, -1566);

        makeEdgeWithNails(operatorPreferencesTemplate, indifferentTest, done, "x : int[0, N-1]", new Integer[]{-3208, -648}, null, null, "areAllIndifferent()", new Integer[]{-3224, -616}, "finalOp = acceptable[modulus(x)]", new Integer[]{-3280, -600}, new Integer[]{-2616, -624});
        makeEdge(operatorPreferencesTemplate, noName, worstFilter, null, null, null, null, null, null, "numLeft = getNumLeft(acceptable)", new Integer[]{-3760, -848});
        makeEdge(operatorPreferencesTemplate, bestFilter, noName1, null, null, null, null, null ,null, "numLeft = getNumLeft(best)", new Integer[]{-3480, -960});
        makeEdge(operatorPreferencesTemplate, noName2, betterWorseFilter, null, null, null, null, null, null, "numLeft = getNumLeft(acceptable)", new Integer[]{-3480, -1104});
        makeEdge(operatorPreferencesTemplate, rejectFilter, noName2, null, null, null, null, "numLeft > 1", new Integer[]{-3480, -1176}, "removeWorseAndRejectedFromAcceptable()", new Integer[]{-3480, -1160});
        makeEdge(operatorPreferencesTemplate, betterWorseFilter, conflict, null, null, null, null, "numLeft == 0", new Integer[]{-3296, -1056}, null, null);
        makeEdgeWithNails(operatorPreferencesTemplate, indifferentTest, tie, null, null, null, null, "!areAllIndifferent()", new Integer[]{-3174, -730}, null, null, new Integer[]{-3296, -624, -3254, -706});
        makeEdge(operatorPreferencesTemplate, worstFilter, indifferentTest, null, null, null, null, "numLeft > 1", new Integer[]{-3480, -776}, "removeWorst()", new Integer[]{-3480, -760});
        makeEdgeWithNails(operatorPreferencesTemplate, noName1, noName, null, null, null, null, "numLeft > 0", new Integer[]{-3456, -920}, "removeBest()", new Integer[]{-3456, -880}, new Integer[]{-3456, -888});
        makeEdgeWithNails(operatorPreferencesTemplate, noName1, noName, null, null, null, null, "numLeft == 0", new Integer[]{-3624, -896}, null, null, new Integer[]{-3520, -888});
        makeEdgeWithNails(operatorPreferencesTemplate, worstFilter, done, null, null, null, null, "numLeft == 1", new Integer[]{-3112, -840}, "finalOp = acceptable[0]", new Integer[]{-3112, -808}, new Integer[]{-2616, -816});
        makeEdgeWithNails(operatorPreferencesTemplate, worstFilter, noChange, null, null, null, null, "numLeft == 0", new Integer[]{-3224, -936}, null, null, new Integer[]{-3312, -816, -3264, -912, -2976, -912, -2872, -912});
        makeEdge(operatorPreferencesTemplate, betterWorseFilter, bestFilter, null, null, null, null, "numLeft > 0", new Integer[]{-3480, -1040}, null, null);
        makeEdgeWithNails(operatorPreferencesTemplate, rejectFilter, noChange, null, null, null, null, "numLeft == 0", new Integer[]{-3080, -1216}, null, null, new Integer[]{-3304, -1192, -2872, -1192});
        makeEdgeWithNails(operatorPreferencesTemplate, rejectFilter, done, null, null, null, null, "numLeft == 1", new Integer[]{-2856, -1296}, "finalOp = acceptable[0]", new Integer[]{-2880, -1264}, new Integer[]{-3328, -1192, -3264, -1272, -2616, -1272});
        makeEdge(operatorPreferencesTemplate, prohibitFilter, rejectFilter, null, null, null, null, null, null, "numLeft = getNumLeft(acceptable)", new Integer[]{-3744, -1240});
        makeEdge(operatorPreferencesTemplate, acceptableCollect, prohibitFilter, null, null, null, null, null, null, "removeProhibitedFromAcceptable()", new Integer[]{-3472, -1312});
        makeEdgeWithNails(operatorPreferencesTemplate, requireTest, acceptableCollect, null, null, null, null, "numLeft == 0", new Integer[]{-3480, -1384}, null, null, new Integer[]{-3488, -1352});
        makeEdge(operatorPreferencesTemplate, noName3, constraintFailure, null, null, null, null, "operators[currentOp-1].operator.isProhibited", new Integer[]{-2968, -1488}, null, null);
        makeEdgeWithNails(operatorPreferencesTemplate, noName3, done, null, null, null, null, "!operators[currentOp-1].operator.isProhibited", new Integer[]{-2808, -1456}, "finalOp = currentOp", new Integer[]{-2792, -1416}, new Integer[]{-2616, -1424});
        makeEdge(operatorPreferencesTemplate, requireTest, noName3, null, null, null, null, "numLeft == 1", new Integer[]{-3256, -1448}, "currentOp = required[0]", new Integer[]{-3272, -1416});
        makeEdgeWithNails(operatorPreferencesTemplate, requireTest, constraintFailure, null, null, null, null, "numLeft > 1", new Integer[]{-3144, -1552}, null, null, new Integer[]{-3320, -1424, -3264, -1520});
        makeEdge(operatorPreferencesTemplate, start, requireTest, null, null, "requireTest?", new Integer[]{-3624, -1520}, null, null, "numLeft = getNumLeft(required)", new Integer[]{-3728, -1496});

        return null;
    }
}
