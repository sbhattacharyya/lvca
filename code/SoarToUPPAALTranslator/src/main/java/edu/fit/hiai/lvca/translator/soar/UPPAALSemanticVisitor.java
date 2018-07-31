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
import java.util.stream.Collectors;

public class UPPAALSemanticVisitor extends SoarBaseVisitor<Node> {

    static final int SIZE_OF_TEXT = 17;
    static final String LITERAL_STRING_PREFIX = "literal_string__";
    private final Set<String> _globals;
    private HashMap<String, Integer> globalToIndex;
    private final Set<String> _booleanGlobals;
    private final int NUM_OPERATORS;
    private final Map<String, Map<String, String>> _variableDictionary;
    private Integer _locationCounter = 0;
    Document ourDocument = new Document(new PrototypeDocument());
    private Template _lastTemplate = null;
    private final Set<String> _templateNames = new HashSet<>();
    private boolean _unaryOrBinaryFlag = false;
    private int _templateIndex = 1;
    private Map<String, String> _productionVariables;
    private List<Integer> _takenValues;
    private Map<String, ProductionVariables> _actualVariablesPerProduction;
    private LinkedList<String> _uppaalOperatorCollection;
    private LinkedList<UppaalAttributeValueTriad> _AVCollection;
    private Map<String, Map<String, String>> _variablesToPathWithID;
    private Map<String, String> conditionSideVariablesToTemps;
    private LinkedList<String> conditionProductionIdentifiers;
    private LinkedList<String> conditionProductionAttributes;
    private LinkedList<String> conditionProductionValues;
    private LinkedList<String> conditionProductionTemp;
    private LinkedList<String> actionProductionIdentifiers;
    private LinkedList<String> actionProductionAttributes;
    private LinkedList<String> actionProductionValues;
    private LinkedList<String> actionProductionFunctions;
    private Map<String, String> attributesToTemps;
    private LinkedList<String> attributeTemps;
    private int _latestNum;
    private int _maxQuerySize;
    private int _latestIndex;
    private Map<String, Boolean> _productionToOSupported;
    private Map<String, LinkedList<String>> _variableToAttributes;
    private Map<String, Map<String, String[]>> _attributeVariableToDisjunctionTestPerProduction;
    private Map<String, Map<String, String>> _attributeVariableToArrayNamePerProduction;
    private Map<String, String[]> _disjunctionArrayNameToArray;
    private Map<String, Boolean> _flags;
    private int _maxConditionSize = -1;

    public UPPAALSemanticVisitor(Set<String> stringAttributeNames, Map<String, Map<String, String>> variablesPerProductionContext, Set<String> boolAttributeNames, int numOperators, Map<String, ProductionVariables> actualVariablesPerProduction, HashSet<Integer> takenValues, LinkedList<String> uppaalOperatorCollection, LinkedList<UppaalAttributeValueTriad> AVCollection, Map<String, Map<String, String>> variablesToPathWithID, int maxQuerySize, Map<String, Boolean> productionToOSupported, Map<String, LinkedList<String>> variableToAttributes, Map<String, Map<String, String[]>> attributeVariableToDisjunctionTestPerProduction, Map<String, Map<String, String>> attributeVariableToArrayNamePerProduction) {
        _globals = stringAttributeNames;
        _booleanGlobals = boolAttributeNames;
        _variableDictionary = variablesPerProductionContext;
        _actualVariablesPerProduction = actualVariablesPerProduction;
        NUM_OPERATORS = numOperators;
        _takenValues = takenValues.stream().sorted().collect(Collectors.toList());
        fillGlobalToIndex();
        _uppaalOperatorCollection = uppaalOperatorCollection;
        _AVCollection = AVCollection;
        _variablesToPathWithID = variablesToPathWithID;
        _maxQuerySize = maxQuerySize + 1;
        _latestNum = 1 + _globals.size() + _uppaalOperatorCollection.size();
        _productionToOSupported = productionToOSupported;
        _variableToAttributes = variableToAttributes;
        _attributeVariableToDisjunctionTestPerProduction = attributeVariableToDisjunctionTestPerProduction;
        _attributeVariableToArrayNamePerProduction = cleanAttributeVariableToArrayName();
    }

    private String getArrayName(String[] checkArray, int[] index) {
        String arrayName = null;
        for (Map.Entry<String, String[]> arrayNameEntry : _disjunctionArrayNameToArray.entrySet()) {
            if (Arrays.equals(arrayNameEntry.getValue(), checkArray)) {
                arrayName = arrayNameEntry.getKey();
                break;
            }
        }
        if (arrayName == null) {
            arrayName = "noneBut_" + index[0];
            _disjunctionArrayNameToArray.put(arrayName, checkArray);
            index[0]++;
        }
        return arrayName;
    }

    /**
     * This is super space inefficent right now.  It's checking if the arrays are equal by looping through all the elements in both arrays
     * This can be made much more efficent by storing the arrays as encoded single values which can then be compared
     * #todo make this more efficent
     * @return
     */
    private Map<String, Map<String, String>> cleanAttributeVariableToArrayName() {
        int[] index = {1};
        _disjunctionArrayNameToArray = new HashMap<>();
        Map<String, Map<String, String>> productionToAttributeToArrayName = new HashMap<>();
        for (Map.Entry<String, Map<String, String[]>> productionToVariable : _attributeVariableToDisjunctionTestPerProduction.entrySet()) {
            Map<String, String> currentVariableToArrayName = new HashMap<>();
            productionToAttributeToArrayName.put(productionToVariable.getKey(), currentVariableToArrayName);
            for (Map.Entry<String, String[]> variableToArray : productionToVariable.getValue().entrySet()) {
                currentVariableToArrayName.put(variableToArray.getKey(), getArrayName(variableToArray.getValue(), index));
            }
        }
        return productionToAttributeToArrayName;
    }

    private int getNextIndex(int i) {
        i++;
        if (_takenValues != null) {
            while (_takenValues.size() > 0 && i == _takenValues.get(0)) {
                i++;
                _takenValues.remove(0);
            }
        }
        return i;
    }

    private void fillGlobalToIndex() {
        globalToIndex = new HashMap<>();
        int i = getNextIndex(0);
        for (String variable : _globals) {
            if (!variable.equals("nil")) {
                globalToIndex.put(variable, i);
                i = getNextIndex(i);
            }
        }
    }

    private String getCounter() {
        String i = _locationCounter.toString();
        _locationCounter++;
        return i;
    }

    private void addConstantToGlobals(StringBuilder globalVariables, String variable, Integer variableIndex) {
        globalVariables.append("const ");
        globalVariables.append("int ");
        globalVariables.append(variable);
        if (variableIndex != null) {
            globalVariables.append(" = ");
            globalVariables.append(variableIndex);
        }
        globalVariables.append(";\n");
    }

    private void getDeclarationElement() {
        _globals.remove("nil"); // added later so that nil always equals 0

        StringBuilder vars = new StringBuilder();

        vars.append(_booleanGlobals
                .stream()
                .map(SoarTranslator::simplifiedString)
                .map(var -> "bool " + var + "; \n")
                .collect(Collectors.joining()));

        vars.append("const int nil = 0;\n" +
                "const int nilAnything = -1;\n");

        StringBuilder globalVariables = new StringBuilder();
        int index = 1;
        for (String variable : _globals) {
            int nextGlobalIndex = globalToIndex.get(variable);
            addConstantToGlobals(globalVariables, SoarTranslator.simplifiedString(variable), nextGlobalIndex);
            index = Math.max(nextGlobalIndex, index);
        }
        index++;
        LinkedList<String> actualOperatorCollection = new LinkedList<>();
        for (String variable : _uppaalOperatorCollection) {
            addConstantToGlobals(globalVariables, SoarTranslator.simplifiedString(variable), index++);
            if (variable.startsWith("state_operator")) {
                actualOperatorCollection.add(variable);
            }
        }
        addConstantToGlobals(globalVariables, "finalOp", index++);
        addConstantToGlobals(globalVariables, "_state", -1);

        for (String variable : _variableToAttributes.keySet()) {
            String variableText;
            if (variable.equals("state_-1")) {
                variableText = "state";
            } else {
                variableText = variable;
            }
            addConstantToGlobals(globalVariables, SoarTranslator.simplifiedString(variableText) + "_num_attributes", _variableToAttributes.get(variable).size());
        }
        //index is set to latest negative number.  Currently, -12
        index = -12;
        int max = -1;
        StringBuilder noneButSwitch = _disjunctionArrayNameToArray.values().size() > 0 ? new StringBuilder("int getNumButNextElement(int numBut, int index) {\n") : null;
        boolean hasIf = false;
        for (Map.Entry<String, String[]> disjunctionMap : _disjunctionArrayNameToArray.entrySet()) {
            max = Math.max(max, disjunctionMap.getValue().length);
            addConstantToGlobals(globalVariables, disjunctionMap.getKey(), index--);
            globalVariables.append("int ").append(disjunctionMap.getKey()).append("_array[").append(disjunctionMap.getValue().length).append("] = {");
            for (int i = 0; i< disjunctionMap.getValue().length; i++) {
                if (i != 0) {
                    globalVariables.append(", ");
                }
                globalVariables.append(SoarTranslator.simplifiedString(disjunctionMap.getValue()[i]));
            }
            globalVariables.append("};\n");
            addConstantToGlobals(globalVariables, disjunctionMap.getKey() + "_array_size", disjunctionMap.getValue().length);
            noneButSwitch.append("\t");
            if (hasIf) {
                noneButSwitch.append("} else ");
            }
            noneButSwitch.append("if (numBut == ").append(disjunctionMap.getKey()).append(") {\n");
            noneButSwitch.append("\t\tif (index >= ").append(disjunctionMap.getKey() + "_array_size").append(") {\n");
            noneButSwitch.append("\t\t\treturn -1;\n");
            noneButSwitch.append("\t\t} else {\n");
            noneButSwitch.append("\t\t\treturn ").append(disjunctionMap.getKey() + "_array[index]").append(";\n");
            noneButSwitch.append("\t\t}\n");
            hasIf = true;
        }
        if (noneButSwitch != null) {
            if (noneButSwitch.length() > 0) {
                noneButSwitch.append("\t} else {\n\t\treturn -2;\n").append("\t}\n");
            } else {
                noneButSwitch.append("\treturn -2;\n");
            }
            noneButSwitch.append("}\n");
        }

        vars.append(globalVariables.toString());

        vars.append("broadcast chan Run_Rule;\n" +
                "broadcast chan Halt;\n" +
                "broadcast chan Reset_Apply;\n" +
                "bool halt = false;\n" +
                "chan Continue_Run;\n" +
                "chan Require_Test;\n" +
                "bool isRetracting;\n" +
                "bool addOperator;\n" +
                "bool removeOperator;\n" +
                "bool productionFired;\n" +
                "const int EMPTY = -2;\n" +
                "const int numTemplates = " + _templateNames.size() + ";\n" +
                "int stackCondition[numTemplates];\n" +
                "int stackAction[numTemplates];\n" +
                "int stackRetract[numTemplates];\n" +
                "int stackConditionIndex = -1;\n" +
                "int stackActionIndex = -1;\n" +
                "int stackRetractIndex = -1;\n" +
                "int selectedFinalOperatorIndex;\n" +
                "const int remove = -3;\n" +
                "const int addFunction = -4;\n" +
                "const int subtractFunction = -5;\n" +
                "const int multiplyFunction = -6;\n" +
                "const int divideFunction = -7;\n" +
                "const int extraRestriction = -8;\n" +
                "const int isNotEqualTo = -9;\n" +
                "const int isGreaterThan = -10;\n" +
                "const int isLessThan = -11;\n" +       //if you add any more negative nums then update the noneBut starting index above
                "const int numAVs = 8;\n" +
                "int numAVCounter = 0;\n" +
                "int lookAheadArray[" + _maxConditionSize + "];\n" +
                "int lookAheadIndex;\n" +
                "int lookAheadDefault[" + _maxConditionSize + "];\n" +
                "int globalIndex = 0;\n" +
                "int valueFunction;\n" +
                "int attributeFunction;\n" +
                "int globalIdentifier;\n" +
                "int globalAttribute;\n" +
                "int globalValue;\n" +
                "int globalDoesContain;\n" +
                "int currentNumAttributes;\n");
        int totalAttributeSize = 0;
        for (LinkedList<String> nextNumAttributes : _variableToAttributes.values()) {
            totalAttributeSize += nextNumAttributes.size();
        }
        vars.append("const int TOTAL_NUM_ATTRIBUTES = " +
                totalAttributeSize + ";\n" +
                "int nestedCheckArray[TOTAL_NUM_ATTRIBUTES];\n" +
                "int nestedCheckIndex = 0;\n");


        vars.append("\n" +
                "int id = 1;\n" +
                "const int N = " + NUM_OPERATORS + ";\n" +
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
                "\tint[0, N] betterIndex;\n" +
                "\tint better[N];\n" +
                "\tint[0, N] binaryIndifferentIndex;\n" +
                "\tint binaryIndifferent[N];\n" +
                "} Operator;\n" +
                "\n" +
                "int retractOperators[N];\n" +
                "int retractOperatorsIndex = 0;\n" +
                "Operator operators[N];\n" +
                "int required[N];\n" +
                "int acceptable[N];\n" +
                "int best[N];\n" +
                "BaseOperator defaultOperator = {false, false, false, false, false, false, false, false, 0, 0};\n" +
                "int defaultOperatorArray[N];\n" +
                "int numLeft = 0;\n" +
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
                "\t\tstackCondition[i] = 0;\n" +
                "\t\tstackAction[i] = 0;\n" +
                "\t\tstackRetract[i] = 0;\n" +
                "\t\tretractOperators[i] = 0;\n" +
                "\t}\n" +
                "\tfor (i = 0; i < " + _maxConditionSize + "; i++) {\n" +
                "\t\tlookAheadDefault[i] = 0;\n" +
                "\t}\n" +
                "}\n" +
                "\n" +
                "void addToStackCondition(int flag) {\n" +
                "\tstackConditionIndex++;\n" +
                "\tstackCondition[stackConditionIndex] = flag;\n" +
                "}\n" +
                "\n" +
                "void addToStackAction(int flag) {\n" +
                "\tstackActionIndex++;\n" +
                "\tstackAction[stackActionIndex] = flag;\n" +
                "}\n" +
                "\n" +
                "void addToStackRetract(int flag) {\n" +
                "\tstackRetractIndex++;\n" +
                "\tstackRetract[stackRetractIndex] = flag;\n" +
                "}\n" +
                "\n" +
                "int removeStackCondition() {\n" +
                "\tint temp = stackCondition[stackConditionIndex];\n" +
                "\tstackCondition[stackConditionIndex] = 0;\n" +
                "\tstackConditionIndex--;\n" +
                "\treturn temp;\n" +
                "}\n" +
                "\n" +
                "int removeStackAction() {\n" +
                "\tint temp = stackAction[stackActionIndex];\n" +
                "\tstackAction[stackActionIndex] = 0;\n" +
                "\tstackActionIndex--;\n" +
                "\treturn temp;\n" +
                "}\n" +
                "\n" +
                "int removeStackRetract() {\n" +
                "\tint temp = stackRetract[stackRetractIndex];\n" +
                "\tstackRetract[stackRetractIndex] = 0;\n" +
                "\tstackRetractIndex--;\n" +
                "\treturn temp;\n" +
                "}\n" +
                "\n" +
                "void clearStacks() {\n" +
                "\tstackConditionIndex = -1;\n" +
                "\tstackActionIndex = -1;\n" +
                "\tstackRetractIndex = -1;\n" +
                "}\n" +
                "\n" +
                "void clearFill(int &ref[N]) {\n" +
                "\tint i = 0;\n" +
                "\twhile(i < N && ref[i] != 0) {\n" +
                "\t\tref[i] = 0;\n" +
                "\t}\n" +
                "}\n" +
                "\n" +
                "bool retractOperatorsContains(int checkValue) {\n" +
                "\tbool contains = false;\n" +
                "\tint i;\n" +
                "\tfor(i = 0; i < retractOperatorsIndex; i++) {\n" +
                "\t\tif (retractOperators[i] == checkValue) {\n" +
                "\t\t\tcontains = true;\n" +
                "\t\t\ti = retractOperatorsIndex;\n" +
                "\t\t}\n" +
                "\t}\n" +
                "\treturn contains;\n" +
                "}\n" +
                "\n" +
                "void clearOperator(int operatorIndex) {\n" +
                "\tBaseOperator def = defaultOperator;\n" +
                "\tdef.id = operators[operatorIndex].operator.id;\n" +
                "\toperators[operatorIndex].operator = def;\n" +
                "\twhile (operators[operatorIndex].betterIndex > 0) {\n" +
                "\t\toperators[operatorIndex].betterIndex--;\n" +
                "\t\toperators[operatorIndex].better[operators[operatorIndex].betterIndex] = 0;\n" +
                "\t}\n" +
                "\twhile (operators[operatorIndex].binaryIndifferentIndex > 0) {\n" +
                "\t\toperators[operatorIndex].binaryIndifferentIndex--;\n" +
                "\t\toperators[operatorIndex].binaryIndifferent[operators[operatorIndex].binaryIndifferentIndex] = 0;\n" +
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
                "}" +
                "\n" +
                "void addBetterTo(int index1, int index2) {\n" +
                "\tint nextIndex = operators[index1].betterIndex;\n" +
                "\toperators[index1].betterIndex++;\n" +
                "\toperators[index1].better[nextIndex] = index2;\n" +
                "}\n" +
                "\n" +
                "void addBinaryIndifferentTo(int index1, int index2) {\n" +
                "\tint nextIndex = operators[index1].binaryIndifferentIndex;\n" +
                "\toperators[index1].binaryIndifferentIndex++;\n" +
                "\toperators[index1].binaryIndifferent[nextIndex] = index2;\n" +
                "}\n" +
                "\n" +
                "void addToNestedCheckArray(int value) {\n" +
                "\tnestedCheckArray[nestedCheckIndex] = value;\n" +
                "\tnestedCheckIndex++;\n" +
                "}\n" +
                "\n" +
                "void removeNestedCheckArray() {\n" +
                "\tnestedCheckArray[globalIndex] = 0;\n" +
                "}\n" +
                "\n");

        vars.append("int getNumAttributes(int variable) {\n");

        StringBuilder newSwitch = new StringBuilder();
        newSwitch.append("\tif (variable == finalOp){\n\t\treturn 1;\n\t}");
        for (String variable : _uppaalOperatorCollection) {
            String correctedName = SoarTranslator.simplifiedString(variable);
            newSwitch.append(" else if (variable == " + correctedName + ") {\n").append("\t\treturn " + correctedName + "_num_attributes;\n").append("\t}");
        }
        newSwitch.append(" else {\n").append("\t\treturn -1;\n").append("\t}\n");
        vars.append(newSwitch).append("}\n").append("\n");

        getOperatorToIDAndBack(actualOperatorCollection, "getOperatorFromID(int id)", "id", true, vars);

        getOperatorToIDAndBack(actualOperatorCollection, "getIDFromOperator(int operator)", "operator", false, vars);

        if (noneButSwitch != null) {
            vars.append(noneButSwitch);
        }

        ourDocument.setProperty("declaration", vars.toString());
    }

    private void getOperatorToIDAndBack(LinkedList<String> actualOperatorCollection, String functionName, String ifPart, boolean operatorFromID, StringBuilder currentDeclaration) {
        currentDeclaration.append("int ").append(functionName).append(" {\n");

        StringBuilder newSwitch = new StringBuilder();
        for (String nextOperator : actualOperatorCollection) {
            newSwitch.append("\t");
            if (newSwitch.length() > 1) {
                newSwitch.append("} else ");
            }
            int operatorIndex = Integer.parseInt(nextOperator.substring(nextOperator.lastIndexOf('_') + 1)) - 1;
            newSwitch.append("if (").append(ifPart).append(" == ");
            if (operatorFromID) {
                newSwitch.append(operatorIndex);
            } else {
                newSwitch.append(nextOperator);
            }
            newSwitch.append(") {\n\t\treturn ");
            if (operatorFromID) {
                newSwitch.append(nextOperator);
            } else {
                newSwitch.append(operatorIndex);
            }
            newSwitch.append(";\n");
        }
        if (newSwitch.length() > 0) {
            newSwitch.append("\t} else {\n\t\treturn -1;\n").append("\t}\n");
        } else {
            newSwitch.append("\treturn -1;\n");
        }
        newSwitch.append("}\n").append("\n");
        currentDeclaration.append(newSwitch);
    }

    private void getSystemElement(Element attributeValuePairs) {
        List<String[]> compoundNames = _templateNames.stream().map(name -> new String[]{name + "_0", name}).collect(Collectors.toList());
        StringBuilder system = new StringBuilder();
        system.append(compoundNames.stream().map(name -> name[0] + " = " + name[1] + "(); \n").collect(Collectors.joining()));
        system.append(attributeValuePairs.getProperty("instantiations").getValue());
        system.append("AVUtility = Attribute_Value_Utility();\n");
        system.append("preferenceResolution = preferenceResolutionTemplate(); \n");
        system.append("scheduler = Scheduler(); \n");
        system.append("system " + compoundNames.stream().map(cName -> cName[0]).collect(Collectors.joining(", ")) + ", AVUtility, preferenceResolution, scheduler,");
        system.append(attributeValuePairs.getProperty("system").getValue());
        if (system.charAt(system.length() - 2) == ',') {
            system.delete(system.length() - 2, system.length());
        }
        system.append(";");

        ourDocument.setProperty("system", system.toString());
    }

    @Override
    public Node visitSoar(SoarParser.SoarContext ctx) {

        ctx.soar_production().forEach(sp -> sp.accept(this));

        getDeclarationElement();

        Element attributeValuePairs = getScheduler();

        getOperatorPreferences();

        getSystemElement(attributeValuePairs);


        try {
            ourDocument.save("sampledoc.xml");
        } catch (IOException er) {
            er.printStackTrace(System.err);
        }

        return null;
    }

    private int getNameLocation(String name, int lastLocationCoordsX) {
        if (name == null) {
            return 0;
        }
        return lastLocationCoordsX - 10 - 10*(name.length() - 1);
    }

    private String[] getGuards(String startGuard) {
        String[] guards = new String[2];
        if (startGuard.equals("globalDoesContain")) {
            guards[0] = startGuard + " == 1";
            guards[1] = startGuard + " == -1";
        } else {
            guards[0] = "!" + startGuard;
            guards[1] = null;
        }
        return guards;
    }

    private Location addHorizontalLocation(Template currentTemplate, Location lastLocation, int[] lastLocationCoords, String name, String synchronization, String stackGuard, String assignment, boolean mirrored, Location startLocation) {
        int xTextLocation = lastLocationCoords[0] + (mirrored ? -370 : 0) + 20;
        int xTempCoords = lastLocationCoords[0] + (mirrored ? -370 : 370);
        Location lastLocationTemp = makeLocationWithCoordinates(currentTemplate, name, getCounter(), true, false, xTempCoords, 0, getNameLocation(name, xTempCoords), lastLocationCoords[1] - 32 + (mirrored ? -1 * SIZE_OF_TEXT : 0));

        makeEdge(currentTemplate, lastLocation, lastLocationTemp, null, null, synchronization, new Integer[]{xTextLocation, lastLocationCoords[1] - (getNumLines(stackGuard, " &&") + 1)*SIZE_OF_TEXT}, stackGuard, new Integer[]{xTextLocation, lastLocationCoords[1] - getNumLines(stackGuard, " &&")*SIZE_OF_TEXT}, assignment, new Integer[]{xTextLocation, lastLocationCoords[1] + 8});
        lastLocationCoords[0] = xTempCoords;
        if (startLocation != null) {
            kickBackToProvidedLocation(currentTemplate, lastLocationTemp, lastLocationCoords, startLocation, "globalDoesContain == -1", null, null, false, null);
        }
        return lastLocationTemp;
    }

    private void kickBackToProvidedLocation(Template currentTemplate, Location fromLocation, int[] fromLocationCoords, Location toLocation, String guard, Integer kickBackIndex, Location kickBackReference, boolean isRetraction, Map<Integer, StringBuilder> indexToKickBackCommands) {
        Integer[] textLocation = new Integer[2];
        Integer[] nails;
        String assignment;
        if (isRetraction) {
            textLocation[0] = fromLocationCoords[0] - (370/2) - 7;
            textLocation[1] = fromLocationCoords[1] - SIZE_OF_TEXT;
            if (fromLocation.getY() == toLocation.getY()) {
                nails = null;
            } else {
                nails = new Integer[]{toLocation.getX(), fromLocation.getY()};
            }
//            nails = new Integer[]{fromLocationCoords[0] - (370/2) - 10, fromLocationCoords[1], fromLocationCoords[0] - (370/2) - 10, -110, fromLocationCoords[0] + 370, -110};
            assignment = null;
        } else {
            if (kickBackReference != null) {
                toLocation = kickBackReference;
                textLocation[0] = fromLocationCoords[0] - 370 * 2 + 40;
                textLocation[1] = fromLocationCoords[1] + 180;
                nails = new Integer[]{fromLocationCoords[0] - 370, fromLocationCoords[1] + 200, fromLocationCoords[0] - 370 * 2, fromLocationCoords[1] + 200};
            } else {
                textLocation[0] = fromLocationCoords[0] - 370 - 370 + 20;
                textLocation[1] = fromLocationCoords[1] + 180;
                nails = new Integer[]{fromLocationCoords[0] - 370, fromLocationCoords[1] + 200, toLocation.getX(), fromLocationCoords[1] + 200};
            }
            assignment = "";
            if (kickBackReference == null) {
                assignment = assignment + "lookAheadArray = lookAheadDefault,\nremoveStackCondition()";
            } else {
                assignment = assignment + indexToKickBackCommands.get(kickBackIndex - 1).toString();
            }
        }
        makeEdgeWithNails(currentTemplate, fromLocation, toLocation, null, null, null, null, guard, textLocation, assignment, new Integer[]{textLocation[0], textLocation[1] + 2*SIZE_OF_TEXT}, nails);
    }

    private Location addSingleVerticalLocation(Template currentTemplate, Location lastLocation, int[] lastLocationCoords, String guard, String assignment) {
        Integer[] textLocation = new Integer[]{lastLocationCoords[0] + 25, lastLocationCoords[1] + SIZE_OF_TEXT};
        int yTempCoords = lastLocationCoords[1] + 200;
        Location lastLocationTemp = makeLocationWithCoordinates(currentTemplate, null, getCounter(), true, false, lastLocationCoords[0], yTempCoords, null, null);
        makeEdge(currentTemplate, lastLocation, lastLocationTemp, null, null, null, null, guard, textLocation, assignment, new Integer[]{textLocation[0], textLocation[1] + (SIZE_OF_TEXT*getNumLines(guard, " &&"))});
        lastLocation = lastLocationTemp;
        lastLocationCoords[1] = yTempCoords;
        return lastLocation;
    }

    private Location addVerticalLocation(Template currentTemplate, Location lastLocation, int[] lastLocationCoords, String guard, StringBuilder[] conditionsOrAssignments, Location kickBackLocation, int[] kickBackIndexes, Location[] kickBackReferences, boolean isRetraction, Map<Integer, StringBuilder> indexToKickBackCommands) {
        String[] guardAndInverseGuard = getGuards(guard);
        for(int i = 1; i < conditionsOrAssignments.length; i++) {
            lastLocation = addSingleVerticalLocation(currentTemplate, lastLocation, lastLocationCoords, guardAndInverseGuard[0], conditionsOrAssignments[i].toString());
            if (guardAndInverseGuard[1] != null) {
                if (isRetraction) {
                    kickBackToProvidedLocation(currentTemplate, lastLocation, lastLocationCoords, kickBackLocation, guardAndInverseGuard[1], null, null, isRetraction, null);
                } else {
                    kickBackToProvidedLocation(currentTemplate, lastLocation, lastLocationCoords, kickBackLocation, guardAndInverseGuard[1], kickBackIndexes[i], kickBackIndexes[i] == -1 ? null : kickBackReferences[kickBackIndexes[i]], isRetraction, indexToKickBackCommands);
                    kickBackReferences[i+1] = lastLocation;
                }
            }
        }
        if (guardAndInverseGuard[1] != null && !isRetraction && (conditionSideVariablesToTemps.size() > 0 || attributesToTemps.size() > 0)) {
            lastLocation = addSingleVerticalLocation(currentTemplate, lastLocation, lastLocationCoords, guardAndInverseGuard[0], "valueFunction = 0,\nattributeFunction = 0,\nglobalIdentifier = 0,\nglobalAttribute = 0,\nglobalValue = 0,\nglobalDoesContain = 0,\ncheckProductionsContain()");
            kickBackToProvidedLocation(currentTemplate, lastLocation, lastLocationCoords, kickBackLocation, guardAndInverseGuard[1], kickBackIndexes[kickBackIndexes.length - 1], kickBackIndexes[kickBackIndexes.length - 1] == -1 ? null : kickBackReferences[kickBackIndexes[kickBackIndexes.length - 1]], isRetraction, indexToKickBackCommands);
        }

        return lastLocation;
    }

    private Location goToNextStage(Template currentTemplate, Location lastLocation, int[] lastLocationCoords, String name, String guard, String assignment, boolean mirrored) {
        int xTempCoords = lastLocationCoords[0] + (mirrored ? -370 : 370);
        Location lastLocationTemp = makeLocationWithCoordinates(currentTemplate, name, getCounter(), true, false, xTempCoords, 0, getNameLocation(name, xTempCoords), -32 + (mirrored ? -1 * SIZE_OF_TEXT : 0));
        Integer[] nails = new Integer[]{lastLocationCoords[0] + (mirrored ? (-370/3) : (370/3)), lastLocationCoords[1] + 200, xTempCoords, lastLocationCoords[1] + 200};
        Integer[] textLocation = new Integer[]{(mirrored ? nails[2] : nails[0]) + 25, lastLocationCoords[1] + 200 - SIZE_OF_TEXT};
        makeEdgeWithNails(currentTemplate, lastLocation, lastLocationTemp, null, null, null, null, guard, textLocation, assignment, new Integer[]{textLocation[0], textLocation[1] + (getNumLines(guard, " &&")*SIZE_OF_TEXT)}, nails);
        lastLocationCoords[0] = xTempCoords;
        lastLocationCoords[1] = 0;
        return lastLocationTemp;
    }

    private void goBackToProvidedLocation(Template currentTemplate, Location lastLocation, Location startLocation, int[] lastLocationCoords, String guard, String assignment, boolean mirrored) {
        Integer[] nails;
        if (mirrored) {
            nails = new Integer[]{lastLocationCoords[0] - (370/2) - 10, lastLocationCoords[1], lastLocationCoords[0] - (370/2) - 10, -110, startLocation.getX(), -110};
        } else {
            nails = new Integer[]{lastLocationCoords[0], lastLocationCoords[1] - 110, startLocation.getX(), -110};
        }
        String synchronization;
        if (assignment == null) {
            synchronization = null;
        } else {
            switch (assignment) {
                case ("Halt!"):
                    synchronization = "Halt!";
                    assignment = "halt = true";
                    break;
                case ("halt"):
                    synchronization = "Halt?";
                    assignment = null;
                    break;
                default:
                    synchronization = null;
            }
        }
        int assignmentSpace = lastLocationCoords[1] - 110 - SIZE_OF_TEXT * (assignment != null && assignment.contains("halt") ? 0 : getNumLines(assignment, ","));
        int textLocationX = lastLocationCoords[0] + (mirrored ? -(370/2) - 7 : -370);
        Integer[] guardLocation = new Integer[]{textLocationX,  assignmentSpace - SIZE_OF_TEXT * getNumLines(guard, " &&")};
        Integer[] assignmentLocation = new Integer[]{textLocationX, assignmentSpace};

        makeEdgeWithNails(currentTemplate, lastLocation, startLocation, null, null, synchronization, new Integer[]{textLocationX, guardLocation[1] - SIZE_OF_TEXT}, guard, guardLocation, assignment, assignmentLocation, nails);
    }

    private void goBackToStartFromAssignment(Template currentTemplate, Location lastLocation, Location startLocation, int[] lastLocationCoords, String operatorAssignments, boolean needsRetraction, String guard) {
        StringBuilder assignment = new StringBuilder("addOperator = false,\nremoveStackAction()");
        if (!needsRetraction) {
            assignment.append(",\ncurrentNumFiringPerCycle++");
        }
        if (operatorAssignments.length() > 0) {
            assignment.append(",\n").append(operatorAssignments);
        }
        assignment.append(",\nfillNextProduction()");
        Integer[] textLocation = new Integer[]{lastLocationCoords[0] + 25, lastLocationCoords[1] - (SIZE_OF_TEXT*getNumLines(guard, " &&"))};
        Integer[] nails = new Integer[]{lastLocationCoords[0] + 370, lastLocationCoords[1], lastLocationCoords[0] + 370, -110, startLocation.getX(), -110};
        makeEdgeWithNails(currentTemplate, lastLocation, startLocation, null, null, null, null, guard, textLocation, assignment.toString(), new Integer[]{textLocation[0], textLocation[1] + (getNumLines(guard, " &&")*SIZE_OF_TEXT)}, nails);
    }

    private void setLastLocationCoords(int[] lastLocationCoords) {
        lastLocationCoords[0] = -152;
        lastLocationCoords[1] = 0;
    }

    private Integer getNumLines(String text, String lookFor) {
        if (text == null) {
            return 0;
        }
        String tempText = text;
        int countLookFor = 0;
        int indexNextLookFor;
        do {
            countLookFor++;
            indexNextLookFor = tempText.indexOf(lookFor);
            tempText = tempText.substring(indexNextLookFor + 1);
        } while (indexNextLookFor != -1);
        return countLookFor;
    }

    private String getProductionDeclaration(String productionName, Set<String> operatorIndexes, Map<String, Integer> conditionTempToIndex, Map<String, Integer> attributeTempToIndex) {
        StringBuilder currentTemplateDeclaration = new StringBuilder();
        int currentLatestNum = _latestNum;
        for (String dummyVariable : conditionSideVariablesToTemps.values()) {
            currentTemplateDeclaration.append("int ").append(dummyVariable).append(" = ").append(currentLatestNum++).append(";\n");
        }
        for (String dummyVariable : attributesToTemps.values()) {
            currentTemplateDeclaration.append("int ").append(dummyVariable).append(" = ").append(currentLatestNum++).append(";\n");
        }
        currentTemplateDeclaration.append("const int NUMBER_OF_PRODUCTIONS = 1;\n");
        currentTemplateDeclaration.append("\n");

        int conditionTemps = conditionSideVariablesToTemps.size();
        int attributeTemps = attributesToTemps.size();


        if (conditionTemps != 0 || attributeTemps != 0) {
            currentTemplateDeclaration.append("typedef struct {\n");
            if (conditionTemps != 0) {
                currentTemplateDeclaration.append("\tint savedTempAndFunction[" + conditionTemps + "];\n");
            }
            if (attributeTemps != 0) {
                currentTemplateDeclaration.append("\tint savedAttributeTemp[" + attributeTemps + "];\n");
            }
            currentTemplateDeclaration.append("} Production;\n").append("\n");

            currentTemplateDeclaration.append(
                    "Production productions[NUMBER_OF_PRODUCTIONS];\n" +
                            "int productionIndex = 0;\n" +
                            "int productionIndexTemp;\n" +
                            "\n");
            currentTemplateDeclaration.append("\n");

            currentTemplateDeclaration.append("void fillNextProduction() {\n");
            int index = 0;
            for (String nextTemp : conditionSideVariablesToTemps.values()) {
                conditionTempToIndex.put(nextTemp, index);
                currentTemplateDeclaration.append("\tproductions[productionIndex].savedTempAndFunction[" + index++ + "] = " + nextTemp + ";\n");
            }
            index = 0;
            for (String nextTemp : attributesToTemps.values()) {
                attributeTempToIndex.put(nextTemp, index);
                currentTemplateDeclaration.append("\tproductions[productionIndex].savedAttributeTemp[" + index++ + "] = " + nextTemp + ";\n");
            }
            currentTemplateDeclaration.append("\tproductionIndex++;\n");
            currentTemplateDeclaration.append("}\n").append("\n");

            currentTemplateDeclaration.append("void checkProductionsContain() {\n");
            currentTemplateDeclaration.append("\tbool containsProduction = false;\n");
            currentTemplateDeclaration.append("\tint i;\n");
            currentTemplateDeclaration.append("\tfor (i = 0; i < productionIndex; i++) {\n");
            currentTemplateDeclaration.append("\t\tif (");
            boolean first = true;
            for (Map.Entry<String, Integer> conditionTempToIndexEntry : conditionTempToIndex.entrySet()) {
                if (!first) {
                    currentTemplateDeclaration.append(" &&\n\t\t\t");
                }
                currentTemplateDeclaration.append("productions[i].savedTempAndFunction[" + conditionTempToIndexEntry.getValue() + "] == " + conditionTempToIndexEntry.getKey());
                first = false;
            }
            for (Map.Entry<String, Integer> attributeTempToIndexEntry : attributeTempToIndex.entrySet()) {
                if (!first) {
                    currentTemplateDeclaration.append(" &&\n\t\t\t");
                }
                currentTemplateDeclaration.append("productions[i].savedAttributeTemp[" + attributeTempToIndexEntry.getValue() + "] == " + attributeTempToIndexEntry.getKey());
                first = false;
            }
            currentTemplateDeclaration.append(") {\n");
            currentTemplateDeclaration.append("\t\t\t\tcontainsProduction = true;\n");
            currentTemplateDeclaration.append("\t\t\t\ti = NUMBER_OF_PRODUCTIONS;\n");
            currentTemplateDeclaration.append("\t\t}\n");
            currentTemplateDeclaration.append("\t}\n");
            currentTemplateDeclaration.append("\tif (containsProduction) {\n");
            currentTemplateDeclaration.append("\t\tglobalDoesContain = -1;\n");
            currentTemplateDeclaration.append("\t} else {\n");
            currentTemplateDeclaration.append("\t\tglobalDoesContain = 1;\n");
            currentTemplateDeclaration.append("\t}\n");
            currentTemplateDeclaration.append("}\n").append("\n");

        } else {
            currentTemplateDeclaration.append("int productionIndex = 0;\n");
            currentTemplateDeclaration.append("int productionIndexTemp;\n");
            currentTemplateDeclaration.append("void fillNextProduction() {\n");
            currentTemplateDeclaration.append("\tproductionIndex++;\n");
            currentTemplateDeclaration.append("}\n").append("\n");
        }


        if (!_productionToOSupported.get(productionName)) {
            if (operatorIndexes != null) {
                currentTemplateDeclaration.append("\nvoid checkAndClearFinalOperator() {\n");
                currentTemplateDeclaration.append("\t if(");
                StringBuilder addOperatorsToRetract = new StringBuilder();
                StringBuilder clearOperators = new StringBuilder();
                for (String nextOperatorIndex : operatorIndexes) {
                    if (currentTemplateDeclaration.charAt(currentTemplateDeclaration.length() - 1) != '(') {
                        currentTemplateDeclaration.append(" || ");
                    }
                    int correctedIndex = Integer.parseInt(nextOperatorIndex) + 1;
                    currentTemplateDeclaration.append("selectedFinalOperatorIndex == " + correctedIndex);
                    addOperatorsToRetract.append("\tretractOperators[retractOperatorsIndex++] = ").append(correctedIndex).append(";\n");
                    clearOperators.append("\tclearOperator(").append(correctedIndex-1).append(");\n");
                }
                currentTemplateDeclaration.append(") {\n").append("\t\taddToNestedCheckArray(finalOp);\n").append("\t}\n");
                currentTemplateDeclaration.append(addOperatorsToRetract);
                currentTemplateDeclaration.append(clearOperators);
                currentTemplateDeclaration.append("}\n");

            }
        } else {
            currentTemplateDeclaration.append("int currentNumFiringPerCycle = 0;\n");
            currentTemplateDeclaration.append("void checkProductionHasOperator() {\n");
            currentTemplateDeclaration.append("\tif (retractOperatorsIndex > 0) {\n");
            currentTemplateDeclaration.append("\t\tint i;\n");
            currentTemplateDeclaration.append("\t\tint j;\n");
            currentTemplateDeclaration.append("\t\tint removeProductionIndexes[NUMBER_OF_PRODUCTIONS];\n");
            currentTemplateDeclaration.append("\t\tint removeIndex = 0;\n");
            currentTemplateDeclaration.append("\t\tfor (i = 0; i < productionIndex; i++) {\n");
            currentTemplateDeclaration.append("\t\t\tif (");
            boolean first = true;
            for (Map.Entry<String, String> variableToPath : _variableDictionary.get(productionName).entrySet()) {
                if (variableToPath.getValue().equals("state_operator")) {
                    if (!first) {
                        currentTemplateDeclaration.append(" ||\n");
                    }
                    currentTemplateDeclaration.append("retractOperatorsContains(1 + getIDFromOperator(productions[i].savedTempAndFunction[").append(conditionTempToIndex.get(SoarTranslator.simplifiedString("dummy_state_operator_" + variableToPath.getKey()))).append("]))");
                    first = false;
                }
            }
            currentTemplateDeclaration.append(") {\n");
            currentTemplateDeclaration.append("\t\t\t\tremoveProductionIndexes[removeIndex++] = i;\n");
            currentTemplateDeclaration.append("\t\t\t}\n");
            currentTemplateDeclaration.append("\t\t}\n");
            currentTemplateDeclaration.append("\t\tfor (i = 0; i < removeIndex; i++) {\n");
            currentTemplateDeclaration.append("\t\t\tfor (j = removeProductionIndexes[i]; j < productionIndex - 1; j++) {\n");
            currentTemplateDeclaration.append("\t\t\t\tproductions[j] = productions[j+1];\n");
            currentTemplateDeclaration.append("\t\t\t}\n");
            currentTemplateDeclaration.append("\t\t\tproductionIndex--;\n");
            currentTemplateDeclaration.append("\t\t}\n");
            currentTemplateDeclaration.append("\t}\n");
            currentTemplateDeclaration.append("}\n").append("\n");
        }

        return currentTemplateDeclaration.toString();
    }


    private void addFlags(SoarParser.FlagsContext ctx) {
//        ('o-support' | 'i-support' | 'chunk' | 'default' | 'template' )
        _flags.put("o-support", false);
        _flags.put("i-support", false);
        _flags.put("chunk", false);
        _flags.put("default", false);
        _flags.put("template", false);
        if (ctx != null) {
            for (ParseTree child : ctx.children) {
                if (child.getText().equals(":")) {
                    continue;
                } else {
                    _flags.put(child.getText(), true);
                }
            }
        }
    }

    private void addNextElement(String variable, String nextElement, StringBuilder conditionOrAssignment, boolean commaNext) {
        if (conditionOrAssignment != null) {
            conditionOrAssignment.append(variable).append(" = ");
            if (!nextElement.equals("0")) {
                conditionOrAssignment.append(nextElement);
            } else {
                conditionOrAssignment.append("0");
            }
            if (commaNext) {
                conditionOrAssignment.append(",\n");
            }
        }
    }

    private StringBuilder[][] getConditionOrAssignment(LinkedList<String> productionIdentifiers, LinkedList<String> productionAttributes, LinkedList<String> productionValues, LinkedList<String> productionValueTemps, LinkedList<String> productionAttributeTemps, Map<String, Integer> conditionTempToIndex, Map<String, Integer> attributeTempToIndex, boolean isAssignment, Map<Integer, StringBuilder> indexToKickBackCommands) {
        int size = productionIdentifiers.size();
        for (String nextPossibleFunction : productionValueTemps) {
            if (nextPossibleFunction.equals("addFunction") || nextPossibleFunction.equals("subtractFunction")) {
                size--;
            }
        }
        StringBuilder nextKickBackCommands = null;
        StringBuilder[] conditionsOrAssignments = new StringBuilder[size];
        StringBuilder[] inverseConditionOrAssignments = new StringBuilder[size];
        StringBuilder tempFromLast = new StringBuilder();
        String commaNext = ",\n";
        boolean skipNext = false;
        int builderIndex = 0;
        for (int i = 0; i < productionIdentifiers.size(); i++) {
            if (skipNext) {
                i++;
                skipNext = false;
            }
            conditionsOrAssignments[builderIndex] = new StringBuilder();
            inverseConditionOrAssignments[builderIndex] = new StringBuilder();
            if (indexToKickBackCommands != null) {
                nextKickBackCommands = new StringBuilder();
                indexToKickBackCommands.put(i, nextKickBackCommands);
            }
            String nextIdentifier = productionIdentifiers.get(i);
            String nextAttribute = productionAttributes.get(i);
            String nextValue = productionValues.get(i);
            String nextAttributeTemp = null;
            if (productionAttributeTemps != null) {
                nextAttributeTemp = productionAttributeTemps.get(i);
            }
            if (tempFromLast.length() > 0) {
                conditionsOrAssignments[builderIndex].append(tempFromLast).append(commaNext);
            }
            tempFromLast = new StringBuilder();
            String nextValueTemp = productionValueTemps.get(i);
            if (nextValueTemp.startsWith("dummy")) {
                tempFromLast.append(nextValueTemp).append(" = ");
                if (nextIdentifier.equals("finalOp")) {
                    tempFromLast.append("getOperatorFromID(globalValue - 1)");
                } else {
                    tempFromLast.append("globalValue");
                }
                if (isAssignment) {
                    addNextElement("valueFunction", "remove", inverseConditionOrAssignments[builderIndex], true);
                } else {
                    addNextElement("valueFunction", "0", inverseConditionOrAssignments[builderIndex], true);
                }
                String savedArray = "savedTempAndFunction";
                Integer index = conditionTempToIndex.get(nextValueTemp);
                if (index == null) {
                    savedArray = "savedAttributeTemp";
                    index = attributeTempToIndex.get(nextValueTemp);
                }
                addNextElement("globalValue", "\nproductions[productionIndexTemp]." + savedArray + "[" + index + "]", inverseConditionOrAssignments[builderIndex], true);
                addNextElement("valueFunction", "0", conditionsOrAssignments[builderIndex], true);
                addNextElement("valueFunction", "0", nextKickBackCommands, true);
            } else {
                if (isAssignment) {
                    addNextElement("valueFunction", "remove", inverseConditionOrAssignments[builderIndex], true);
                } else {
                    addNextElement("valueFunction", nextValueTemp, inverseConditionOrAssignments[builderIndex], true);
                }
                addNextElement("valueFunction", nextValueTemp, conditionsOrAssignments[builderIndex], true);
                addNextElement("valueFunction", nextValueTemp, nextKickBackCommands, true);
                if (nextValueTemp.equals("addFunction") || nextValueTemp.equals("subtractFunction")) {
                    skipNext = true;
                    nextAttributeTemp = productionValues.get(i + 1);
                }
                addNextElement("globalValue", nextValue, inverseConditionOrAssignments[builderIndex], true);
            }
            if (nextAttributeTemp != null) {
                addNextElement("attributeFunction", nextAttributeTemp, conditionsOrAssignments[builderIndex], true);
                addNextElement("attributeFunction", nextAttributeTemp, inverseConditionOrAssignments[builderIndex], true);
                addNextElement("attributeFunction", nextAttributeTemp, nextKickBackCommands, true);
            } else {
                addNextElement("attributeFunction", "0", conditionsOrAssignments[builderIndex], true);
                addNextElement("attributeFunction", "0", inverseConditionOrAssignments[builderIndex], true);
                addNextElement("attributeFunction", "0", nextKickBackCommands, true);
            }
            addNextElement("globalIdentifier", nextIdentifier, conditionsOrAssignments[builderIndex], true);
            addNextElement("globalIdentifier", nextIdentifier, inverseConditionOrAssignments[builderIndex], true);
            addNextElement("globalIdentifier", nextIdentifier, nextKickBackCommands, true);
            if (nextAttribute.startsWith("noneBut")) {
                if (tempFromLast.length() > 0) {
                    tempFromLast.append(",\n");
                }
                tempFromLast.append(nextAttributeTemp).append(" = attributeFunction");
            }
            addNextElement("globalAttribute", nextAttribute, conditionsOrAssignments[builderIndex], true);
            addNextElement("globalAttribute", nextAttribute, inverseConditionOrAssignments[builderIndex], false);
            addNextElement("globalAttribute", nextAttribute, nextKickBackCommands, true);
            addNextElement("globalValue", nextValue, conditionsOrAssignments[builderIndex], false);
            addNextElement("globalValue", nextValue, nextKickBackCommands, false);
            if (!isAssignment) {
                conditionsOrAssignments[builderIndex].append(",\nlookAheadIndex = ").append(i);
                conditionsOrAssignments[builderIndex].append(",\nglobalDoesContain = 0");
                if (nextKickBackCommands != null) {
                    nextKickBackCommands.append(",\nlookAheadIndex = ").append(i);
                    nextKickBackCommands.append(",\nglobalDoesContain = 0");
                }
                inverseConditionOrAssignments[builderIndex].append(",\nglobalDoesContain = 0");
            }
            builderIndex++;
        }
        if (tempFromLast.length() > 0) {
            conditionsOrAssignments = Arrays.copyOf(conditionsOrAssignments, conditionsOrAssignments.length + 1);
            conditionsOrAssignments[conditionsOrAssignments.length - 1] = new StringBuilder(tempFromLast);
        }


        return new StringBuilder[][]{conditionsOrAssignments, inverseConditionOrAssignments};
    }

    private int[] getKickBackIndexes() {
        int[] kickBackIndexes = new int[conditionProductionValues.size()];
        int lastNilAnything = -1;
        int index = 0;
        for (String nextValue : conditionProductionValues) {
            kickBackIndexes[index] = lastNilAnything;
            if (nextValue.equals("nilAnything") || conditionProductionAttributes.get(index).startsWith("noneBut")) {
                lastNilAnything = index + 1;
            }
            index++;
        }
        return kickBackIndexes;
    }

    @Override
    public Node visitSoar_production(SoarParser.Soar_productionContext ctx) {
        _productionVariables = new HashMap<>();
        conditionSideVariablesToTemps = new HashMap<>();
        conditionProductionIdentifiers = new LinkedList<>();
        conditionProductionAttributes = new LinkedList<>();
        conditionProductionValues = new LinkedList<>();
        conditionProductionTemp = new LinkedList<>();
        actionProductionIdentifiers = new LinkedList<>();
        actionProductionAttributes = new LinkedList<>();
        actionProductionValues = new LinkedList<>();
        actionProductionFunctions = new LinkedList<>();
        attributesToTemps = new HashMap<>();
        attributeTemps = new LinkedList<>();
        _latestIndex = 0;
        _flags = new HashMap<>();
        addFlags(ctx.flags());

        String startStateID = getCounter();

        Template currentTemplate = makeTemplate(SoarTranslator.simplifiedString(ctx.sym_constant().getText()));
        _templateNames.add(getText(currentTemplate, "name"));

        Location startLocation = makeLocationWithCoordinates(currentTemplate, "Start", startStateID, true, true, -152, 0, -200, -32);

        ctx.condition_side().accept(this);

        Node actionSide = ctx.action_side().accept(this);
        String operatorAssignments = getText(actionSide, "operatorAssignments");
        Set<String> operatorIndexes;
        if (operatorAssignments.length() > 0) {
            operatorIndexes = new HashSet<>();
            int lookIndex = 0;
            int possibleIndex;
            do {
                possibleIndex = operatorAssignments.indexOf("operators", lookIndex);
                if (possibleIndex != -1) {
                    lookIndex = possibleIndex + "operators[".length();
                    int endIndex = operatorAssignments.indexOf("]", lookIndex);
                    String nextIndex = operatorAssignments.substring(lookIndex, endIndex);
//                    try {
//                        Integer.parseInt(nextIndex);
//                    } catch(NumberFormatException e) {
//                        int newLookIndex = operatorAssignments.indexOf("(", lookIndex) + 1;
//                        int newEndIndex = operatorAssignments.indexOf(")", newLookIndex);
//                        nextIndex = operatorAssignments.substring(newLookIndex, newEndIndex);
//                    }
                    lookIndex = endIndex;
                    operatorIndexes.add(nextIndex);
                }
            } while (possibleIndex != -1);
        } else {
            operatorIndexes = null;
        }

        Map<String, Integer> conditionTempToIndex = new HashMap<>();
        Map<String, Integer> attributeTempToIndex = new HashMap<>();

        boolean halt = getText(actionSide, "hasHalt").equals("yes");
        boolean needsRetraction = !_productionToOSupported.get(ctx.sym_constant().getText());

        currentTemplate.setProperty("declaration", getProductionDeclaration(ctx.sym_constant().getText(), operatorIndexes, conditionTempToIndex, attributeTempToIndex));

        int[] lastLocationCoords = new int[2];
        setLastLocationCoords(lastLocationCoords);
        Location lastLocation;

        Map<Integer, StringBuilder> indexToKickBackCommands = new HashMap<>();
        StringBuilder[][] conditions = getConditionOrAssignment(conditionProductionIdentifiers, conditionProductionAttributes, conditionProductionValues, conditionProductionTemp, attributeTemps, conditionTempToIndex, attributeTempToIndex, false, indexToKickBackCommands);
        StringBuilder[][] assignments = getConditionOrAssignment(actionProductionIdentifiers, actionProductionAttributes, actionProductionValues, actionProductionFunctions, null, conditionTempToIndex, attributeTempToIndex, true, null);
        for (StringBuilder[] nextBuilder : assignments) {
            for (StringBuilder nextAssignment : nextBuilder) {
                nextAssignment.append(",\naddOperator = true");
            }
        }
        if (operatorIndexes != null && assignments[1].length > 0) {
            assignments[1][assignments[1].length - 1].append(",\ncheckAndClearFinalOperator()");
        }

        String guard;
        String assignment;
        if (!halt) {
            if (needsRetraction) {
                assignment = "addToStackRetract(" + _templateIndex + "),\nproductionIndexTemp = 0";
                lastLocation = addHorizontalLocation(currentTemplate, startLocation, lastLocationCoords, "Retract_Conditions", "Run_Rule?", "isRetracting", assignment, true, null);
                Location runRetractLocation = lastLocation;

                guard = "stackRetract[stackRetractIndex] == " + _templateIndex + " &&\nproductionIndexTemp == productionIndex";
                assignment = "productionIndexTemp = 0,\nremoveStackRetract()";
                goBackToProvidedLocation(currentTemplate, lastLocation, startLocation, lastLocationCoords, guard, assignment, true);

                guard = "productionIndexTemp != productionIndex &&\nstackRetract[stackRetractIndex] == " + _templateIndex;
                assignment = conditions[1][0].toString();
                lastLocation = addHorizontalLocation(currentTemplate, lastLocation, lastLocationCoords, null, null, guard, assignment, true, null);
                int extraShift = ((getNumLines(assignment, ",") + 1)*SIZE_OF_TEXT);


                Location runRetractAssignments = makeLocationWithCoordinates(currentTemplate, "Retract_Assignments", getCounter(), true, false, lastLocationCoords[0] - 370, 0, getNameLocation("Retract_Assignments", lastLocationCoords[0] - 370), lastLocationCoords[1] - 32 + (-1 * SIZE_OF_TEXT));

                makeEdge(currentTemplate, lastLocation, runRetractAssignments, null, null, null, null, "globalDoesContain == -1", new Integer[]{lastLocationCoords[0] - (370/2) - 7, lastLocationCoords[1] - SIZE_OF_TEXT}, null, null);

                lastLocationCoords[1] += extraShift;

                lastLocation = addVerticalLocation(currentTemplate, lastLocation, lastLocationCoords, "globalDoesContain", conditions[1], runRetractAssignments,null, null, true, null);

                assignment = "productionIndexTemp++";
                lastLocationCoords[0] -= 150;
                goBackToProvidedLocation(currentTemplate, lastLocation, runRetractLocation, lastLocationCoords, "globalDoesContain == 1", assignment, true);

                lastLocation = runRetractAssignments;
                lastLocationCoords[0] = runRetractAssignments.getX();
                lastLocationCoords[1] = runRetractAssignments.getY();

                assignment = assignments[1][0].toString();
                lastLocation = addHorizontalLocation(currentTemplate, lastLocation, lastLocationCoords, null, null, guard, assignment, true, null);
                extraShift = ((getNumLines(assignment, ",") + 1)*SIZE_OF_TEXT);

                lastLocationCoords[1] += extraShift;
                lastLocation = addVerticalLocation(currentTemplate, lastLocation, lastLocationCoords, "addOperator", assignments[1], runRetractLocation,null, null, true, null);

                lastLocation = addSingleVerticalLocation(currentTemplate, lastLocation, lastLocationCoords, "!addOperator", "removeOperator = true,\nglobalIndex = 0,\ncurrentNumAttributes =\ngetNumAttributes(nestedCheckArray[0])");

                assignment = "productionIndex--";
                goBackToProvidedLocation(currentTemplate, lastLocation, runRetractLocation, lastLocationCoords, "!removeOperator &&\ncurrentNumAttributes == 0", assignment, true);
            } else {
                int xTextLocation = lastLocationCoords[0] - 370;
                makeEdgeWithNails(currentTemplate, startLocation, startLocation, null, null, "Run_Rule?", new Integer[]{xTextLocation, lastLocationCoords[1] - SIZE_OF_TEXT*3}, "!productionFired &&\nisRetracting", new Integer[]{xTextLocation, lastLocationCoords[1] - SIZE_OF_TEXT*2}, "currentNumFiringPerCycle = 0", new Integer[]{xTextLocation, lastLocationCoords[1] + 10}, new Integer[]{xTextLocation, lastLocationCoords[1]});
                guard = null;
                assignment = "checkProductionHasOperator()";
                int[] constants = {417, 100, 68};
                Integer[] nails = new Integer[]{startLocation.getX(), startLocation.getY() + constants[1], startLocation.getX() - constants[2], startLocation.getY() + constants[1], startLocation.getX() - constants[2], startLocation.getY()};
                makeEdgeWithNails(currentTemplate, startLocation, startLocation, null, null, "Reset_Apply?", new Integer[]{xTextLocation, startLocation.getY() + constants[1] - 10 - SIZE_OF_TEXT}, null, new Integer[]{xTextLocation, startLocation.getY() + constants[1] - 10}, assignment, new Integer[]{xTextLocation, startLocation.getY() + constants[1] - 10 + getNumLines(guard, " &&")*SIZE_OF_TEXT}, nails);

            }
        }

        setLastLocationCoords(lastLocationCoords);

        lastLocation = addHorizontalLocation(currentTemplate, startLocation, lastLocationCoords, "Run_Guard", "Run_Rule?", "!isRetracting &&\n" + (needsRetraction ? "productionIndex" : "currentNumFiringPerCycle") + " != NUMBER_OF_PRODUCTIONS", "addToStackCondition(" + _templateIndex + ")", false, null);

        int[] kickBackIndexes = getKickBackIndexes();
        Location[] kickBackReferences = new Location[kickBackIndexes.length + 1];
        kickBackReferences[0] = lastLocation;

        goBackToProvidedLocation(currentTemplate, lastLocation, startLocation, lastLocationCoords, null, "halt", false);

        lastLocation = addHorizontalLocation(currentTemplate, lastLocation, lastLocationCoords, null, null, "stackCondition[stackConditionIndex] == " + _templateIndex + " &&\n!addOperator", conditions[0][0].toString() + ",\nglobalIndex = 0", false, startLocation);

        kickBackReferences[1] = lastLocation;
        lastLocation = addVerticalLocation(currentTemplate, lastLocation, lastLocationCoords, "globalDoesContain", conditions[0], startLocation, kickBackIndexes, kickBackReferences, false, indexToKickBackCommands);

        lastLocation = goToNextStage(currentTemplate, lastLocation, lastLocationCoords, "Run_Assignment", "globalDoesContain == 1", "removeStackCondition(),\naddToStackAction(" + _templateIndex + "),\nproductionFired = true,\nlookAheadArray = lookAheadDefault", false);

        goBackToProvidedLocation(currentTemplate, lastLocation, startLocation, lastLocationCoords, null, "halt", false);

        if (assignments[0].length == 0) {
            guard = "stackConditionIndex == -1 &&\nstackAction[stackActionIndex] == " + _templateIndex;
        } else {
            lastLocation = addHorizontalLocation(currentTemplate, lastLocation, lastLocationCoords, null, null, "stackConditionIndex == -1 &&\nstackAction[stackActionIndex] == " + _templateIndex, assignments[0][0].toString(),false, null);
            if (assignments[0].length != 1) {
                lastLocation = addVerticalLocation(currentTemplate, lastLocation, lastLocationCoords, "addOperator", assignments[0], null, null, null, false, null);
            }
            guard = "!addOperator";
        }
        goBackToStartFromAssignment(currentTemplate, lastLocation, startLocation, lastLocationCoords, operatorAssignments, needsRetraction, guard);

        _templateIndex++;
        _maxConditionSize = Math.max(_maxConditionSize, conditionProductionIdentifiers.size());
        return null;
    }

    @Override
    public Node visitCondition_side(SoarParser.Condition_sideContext ctx) {
        ctx.state_imp_cond().accept(this);
        ctx.cond().forEach(cond -> cond.accept(this));
        return null;
    }

    private Node textAsNode(String property, String text) {
        Node node = generateNode();
        node.setProperty(property, text);
        return node;
    }

    private String getText(Node accept, String property) {
        return (String) accept.getProperty(property).getValue();
    }

    private Node generateNode() {
        return ourDocument.createTemplate();
    }

    @Override
    public Node visitState_imp_cond(SoarParser.State_imp_condContext ctx) {

        String productionName = ((SoarParser.Soar_productionContext) ctx.parent.parent).sym_constant().getText();
        String idTest = ctx.id_test().getText();
        Map<String, String> localVariableDictionary = _variableDictionary.get(productionName);
        ProductionVariables localActualVariables = _actualVariablesPerProduction.get(productionName);
        Map<String, String> attributeVariableToArrayName = _attributeVariableToArrayNamePerProduction.get(productionName);

        innerConditionVisit(ctx.attr_value_tests(), localVariableDictionary, idTest, localActualVariables, attributeVariableToArrayName);

        return null;
    }

    private String getVaribleFromConjunctive(SoarParser.Conjunctive_testContext ctx) {
        String variable = null;
        for (SoarParser.Simple_testContext simple_testContext : ctx.simple_test()) {
            if (simple_testContext.relational_test() != null && simple_testContext.relational_test().relation() == null) {
                variable = simple_testContext.relational_test().single_test().variable().getText();
                break;
            }
        }
        return variable;
    }

    private void innerConditionVisit(List<SoarParser.Attr_value_testsContext> attrValueTestsCtxs, Map<String, String> localVariableDictionary, String idTest, ProductionVariables localActualVariables, Map<String, String> attributeVariableToArrayName) {
        // Variable in left hand side
        if (localVariableDictionary.containsKey(idTest)) {
            // Build the comparisons
            for (SoarParser.Attr_value_testsContext attributeCtx : attrValueTestsCtxs) {

                String lastVariable;
                if (localVariableDictionary.get(idTest).equals("state")) {
                    lastVariable = "_state";
                } else {
                    lastVariable = conditionSideVariablesToTemps.get(idTest);
                }

                for (int i = 0; i < attributeCtx.attr_test().size() - 1; i++) {
                    String attributeText = attributeCtx.attr_test(i).getText();
                    conditionProductionIdentifiers.add(attributeText.equals("operator") ? "finalOp" : lastVariable);
                    conditionProductionAttributes.add(attributeText);
                    conditionProductionValues.add("nilAnything");
                    String withoutTempVariable = lastVariable + "_" + attributeText;
                    String dummyVariable = "dummy" + (withoutTempVariable.charAt(0) != '_' ? "_" : "") + withoutTempVariable;
                    conditionProductionTemp.add(dummyVariable);
                    String newTempVariable = withoutTempVariable + "_temp";
                    _productionVariables.put(dummyVariable, newTempVariable);
                    conditionSideVariablesToTemps.put(dummyVariable, dummyVariable);
                    lastVariable = dummyVariable;
                    attributeTemps.add("0");
                }

                String attrPath = attributeCtx.attr_test(attributeCtx.attr_test().size() - 1).getText();
                String dummyValue = conditionSideVariablesToTemps.get(attrPath);
                if (dummyValue != null) {
                    attrPath = dummyValue;
                } else if (attributeCtx.attr_test(attributeCtx.attr_test().size() - 1).test().conjunctive_test() != null) {
                    attrPath = getVaribleFromConjunctive(attributeCtx.attr_test(attributeCtx.attr_test().size() - 1).test().conjunctive_test());
                    if (attributesToTemps.get(attrPath) == null) {
                        String dummy = "dummy_state_" + SoarTranslator.simplifiedString(attrPath);
                        attributesToTemps.put(attrPath, dummy);
                    }
                    attributeTemps.add(0, attributesToTemps.get(attrPath));
                    conditionProductionIdentifiers.add(0, "0");
                    conditionProductionAttributes.add(0, attributeVariableToArrayName.get(attrPath));
                    conditionProductionValues.add(0, "-1");
                    conditionProductionTemp.add(0, "0");
                    _latestIndex++;

                    attrPath = attributesToTemps.get(attrPath);
                } else if (attributesToTemps.get(attrPath) != null) {
                    attrPath = attributesToTemps.get(attrPath);
                } else {
                    attrPath = SoarTranslator.simplifiedString(attrPath);
                }

                conditionProductionIdentifiers.add(_flags.get("chunk") || !attrPath.equals("operator") ? lastVariable : "finalOp");
                conditionProductionAttributes.add(attrPath);
                if (attributeTemps.size() < conditionProductionIdentifiers.size()) {
                    attributeTemps.add("0");
                }

                String value;

                if (attributeCtx.getText().startsWith("-^")) {
                    conditionProductionValues.add("EMPTY");
                    conditionProductionTemp.add("0");
                } else {
                    int numberOfValues = attributeCtx.value_test().size();

                    if (numberOfValues == 1) {
                        Node relationAndRightTerm = attributeCtx.value_test(0).accept(this);

                        if (attributeCtx.value_test(0).test().conjunctive_test() != null || attributeCtx.value_test(0).test().simple_test().disjunction_test() == null) {

                            String[] relations = null;
                            String[] variablesForRelations = null;
                            String rightTerm;

                            if (relationAndRightTerm.getProperty("setOfRel") != null) {
                                relations = getText(relationAndRightTerm, "setOfRel").split(",");
                                variablesForRelations = new String[relations.length];
                                for (int i = 0; i < relations.length; i++) {
                                    variablesForRelations[i] = getText(relationAndRightTerm, relations[i]);
                                }
                            }

                            if (relationAndRightTerm.getProperty("var") != null) {
                                rightTerm = getText(relationAndRightTerm, "var");
                                if (conditionSideVariablesToTemps.get(rightTerm) == null) {
                                    value = "nilAnything";
                                    String withoutTempVariable = SoarTranslator.simplifiedString(localVariableDictionary.get(rightTerm) + "_" + rightTerm);
                                    String dummyVariable = "dummy_" + withoutTempVariable;
                                    conditionSideVariablesToTemps.put(rightTerm, dummyVariable);
                                    conditionProductionTemp.add(dummyVariable);
                                    if (localActualVariables.variablesContains(rightTerm)) {
                                        String newTempVariable = withoutTempVariable + "_temp";
                                        _productionVariables.put(rightTerm, newTempVariable);
                                    }
                                } else {
                                    value = conditionSideVariablesToTemps.get(rightTerm);
                                }
                            } else {
                                rightTerm = getText(relationAndRightTerm, "const");
                                value = SoarTranslator.simplifiedString(rightTerm);
                            }

                           if (value.length() > 0) {
                                if (value.equals("nilAnything")) {
                                    conditionProductionValues.add(_latestIndex, value);
                                    conditionProductionIdentifiers.add(_latestIndex, conditionProductionIdentifiers.removeLast());
                                    conditionProductionAttributes.add(_latestIndex, conditionProductionAttributes.removeLast());
                                    conditionProductionTemp.add(_latestIndex, conditionProductionTemp.removeLast());
                                    attributeTemps.add(_latestIndex, attributeTemps.removeLast());
                                    _latestIndex++;
                                } else {
                                    conditionProductionValues.add(value);
                                    conditionProductionTemp.add("0");
                                }
                                if (relations != null) {
                                    String identifier = conditionProductionTemp.get(_latestIndex - 1);
                                    for(int i = 0; i < relations.length; i++) {
                                        conditionProductionIdentifiers.add(_latestIndex, identifier);
                                        conditionProductionAttributes.add(_latestIndex, "extraRestriction");
                                        conditionProductionValues.add(_latestIndex, variablesForRelations[i]);
                                        conditionProductionTemp.add(_latestIndex, relations[i]);
                                        attributeTemps.add(_latestIndex, "0");
                                        _latestIndex++;
                                    }
                                }
                            }
                        } else if (relationAndRightTerm.getProperty("disjunction") != null) {
                            //FIXFIXFIX
                        }
                    } else {
                        // use "path_to_var[index] = constant" pattern
                    }
                }
            }
        }
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
        ProductionVariables localActualVariables = _actualVariablesPerProduction.get(productionName);
        Map<String, String> attributeVariableToArrayName = _attributeVariableToArrayNamePerProduction.get(productionName);

        innerConditionVisit(ctx.attr_value_tests(), localVariableDictionary, idTest, localActualVariables, attributeVariableToArrayName);

        return null;
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
        Node returnNode = textAsNode("setOfRel", "");
        for (SoarParser.Simple_testContext simple_testContext : ctx.simple_test()) {
            Node simpleNode = simple_testContext.accept(this);
            if (simpleNode != null) {
                if (simpleNode.getProperty("rel") == null) {
                    returnNode.setProperty("var", getText(simpleNode, "var"));
                } else {
                    String variableOrConstant;
                    if (simpleNode.getProperty("var") != null) {
                        variableOrConstant = getText(simpleNode, "var");
                    } else {
                        variableOrConstant = getText(simpleNode, "const");
                    }
                    if (returnNode.getProperty(getText(simpleNode, "rel")) == null) {
                        returnNode.setProperty(getText(simpleNode, "rel"), variableOrConstant);
                        returnNode.setProperty("setOfRel", getText(returnNode, "setOfRel") + (getText(returnNode, "setOfRel").length() > 0 ? "," : "") + getText(simpleNode, "rel"));
                    } else {
                        returnNode.setProperty(getText(returnNode, getText(simpleNode, "rel")) + "," + variableOrConstant, getText(simpleNode, "rel"));
                    }
                }
            }
        }
        return returnNode;
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
        Node relationNode = ctx.single_test().accept(this);

        if (ctx.relation() != null) {
            relationNode.setProperty("rel", getText(ctx.relation().accept(this), "rel"));
        }
        return relationNode;
    }

    @Override
    public Node visitRelation(SoarParser.RelationContext ctx) {

        String relationText = UtilityForVisitors.relationToText(ctx.getText());
        Node returnTree = generateNode();
        if (relationText != null) {
            returnTree.setProperty("rel", relationText);
        }
        return returnTree;
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
        String result = SoarTranslator.simplifiedString(ctx.getText());

        if (ctx.Print_string() != null) {
            result = LITERAL_STRING_PREFIX + ctx.Print_string().getText().split("|")[1];
        }
        return textAsNode("const", result);
    }

    @Override
    public Node visitAction_side(SoarParser.Action_sideContext ctx) {
        StringBuilder operatorAssignments = new StringBuilder();
        StringBuilder lookForOperatorAssignments = new StringBuilder();
        boolean hasLastAssignment = false;
        for (SoarParser.ActionContext actionContext : ctx.action()) {
            Node actionNode = actionContext.accept(this);
            if (!getText(actionNode, "operatorAssignments").equals("")) {
                if (hasLastAssignment) {
                    operatorAssignments.append(",\n");
                }
                operatorAssignments.append(getText(actionNode, "operatorAssignments"));
                hasLastAssignment = true;
            }
        }

        Node returnNode = textAsNode("operatorAssignments", operatorAssignments.toString());
        returnNode.setProperty("lookForOperatorAssignments", lookForOperatorAssignments.toString());

        String hasHalt = "no";
        if (ctx.func_call().size() != 0) {
            for (SoarParser.Func_callContext func_callContext : ctx.func_call()) {
                if (func_callContext.func_name().getText().equals("halt")) {
                    hasHalt = "yes";
                    break;
                }
            }
        }
        returnNode.setProperty("hasHalt", hasHalt);

        return returnNode;
    }

    @Override
    public Node visitAction(SoarParser.ActionContext ctx) {
        String productionName = ((SoarParser.Soar_productionContext) ctx.parent.parent).sym_constant().getText();
        Map<String, String> localVariablePathsWithID = _variablesToPathWithID.get(productionName);
        String variableName = ctx.variable().getText();

        String operatorCollection = innerVisitAction(ctx.attr_value_make(), variableName, localVariablePathsWithID);
        Node returnNode = textAsNode("operatorAssignments", operatorCollection);
        return returnNode;
    }

    private String innerVisitAction(List<SoarParser.Attr_value_makeContext> ctxs, String variableName, Map<String, String> localVariablePathsWithID) {
        LinkedList<String> operatorCollection = new LinkedList<>();
        String variable = conditionSideVariablesToTemps.get(variableName);
        if (variable == null) {
            String pathWithId = localVariablePathsWithID.get(variableName);
            int index = Integer.parseInt(pathWithId.substring(pathWithId.lastIndexOf("_") + 1));
            if (index == -1) {
                variable = "_" + pathWithId.substring(0, pathWithId.lastIndexOf("_"));
            } else {
                variable = pathWithId;
            }
            variable = SoarTranslator.simplifiedString(variable);
        }

        for (SoarParser.Attr_value_makeContext attrCtx : ctxs) {
            String attribute = attrCtx.variable_or_sym_constant(attrCtx.variable_or_sym_constant().size() - 1).getText();
            if (attributesToTemps.get(attribute) != null) {
                attribute = attributesToTemps.get(attribute);
            } else {
                attribute = SoarTranslator.simplifiedString(attribute);
            }

            for (SoarParser.Value_makeContext value_makeContext : attrCtx.value_make()) {
                actionProductionIdentifiers.add(variable);
                actionProductionAttributes.add(attribute);
                attributeTemps.add("0");

                Node rightSideElement = value_makeContext.accept(this);
                String rightSide = determineAssignment(rightSideElement, localVariablePathsWithID);
                if (rightSideElement.getProperty("expr") != null) {
                    actionProductionIdentifiers.add("0");
                    actionProductionAttributes.add("0");
                    actionProductionValues.add(getText(rightSideElement, "secondValue"));
                    actionProductionFunctions.add("0");
                    attributeTemps.add("0");
                }

                if (rightSide != null) {
                    operatorCollection.add(rightSide);
                }
            }
        }

        return operatorCollection.stream().collect(Collectors.joining(",\n"));
    }

    private String getOperatorIndex(String index) {
        try {
            Integer.parseInt(index);
            return index;
        } catch(NumberFormatException e) {
            return "getIDFromOperator(" + index + ")";
        }
    }

    private String operatorBaseString(String index, String parameter) {
        StringBuilder returnString = new StringBuilder();
        returnString.append("operators[");
        returnString.append(getOperatorIndex(index));
        returnString.append("].operator.");

        returnString.append(parameter);
        return returnString.toString();
    }

    private void shiftLists() {
        actionProductionIdentifiers.addFirst(actionProductionIdentifiers.removeLast());
        actionProductionAttributes.addFirst(actionProductionAttributes.removeLast());
        actionProductionValues.addFirst(actionProductionValues.removeLast());
        actionProductionFunctions.addFirst(actionProductionFunctions.removeLast());
    }

    private String getVariable(String text, Map<String, String> localVariablePathsWithID) {
        String variable = _productionVariables.get(text);
        if (variable == null) {
            variable = localVariablePathsWithID.get(text);
        }
        return variable;
    }

    private String determineAssignment(Node rightSideElement, Map<String, String> localVariablePathsWithID) {
        String rightSide = null;
        if (rightSideElement != null) {
            if (rightSideElement.getProperty("expr") != null) {
                actionProductionValues.add(getText(rightSideElement, "firstValue"));
                actionProductionFunctions.add(getText(rightSideElement, "expr"));
            } else if (rightSideElement.getProperty("pref") != null) {
                if (getText(rightSideElement, "pref").equals("remove")) {
                    String rightSideVarOrConst = getText(rightSideElement, "constVarExpr");
                    String variableOrConst;
                    if (rightSideVarOrConst.equals("const")) {
                        variableOrConst = getText(rightSideElement, "const");
                    } else {
                        rightSideVarOrConst = getText(rightSideElement, "var");
                        variableOrConst = conditionSideVariablesToTemps.get(rightSideVarOrConst);
                        if (variableOrConst == null) {
                            variableOrConst = getVariable(rightSideVarOrConst, localVariablePathsWithID);
                        }
                    }
                    actionProductionValues.add(variableOrConst);
                    actionProductionFunctions.add("remove");
                    shiftLists();
                } else {
                    String operatorIndex = getIndexFromID(getText(rightSideElement, "var"), localVariablePathsWithID);

                    try {
                        Integer.parseInt(operatorIndex);
                        actionProductionValues.add(getVariable(getText(rightSideElement, "var"), localVariablePathsWithID));
                    } catch (NumberFormatException e) {
                        actionProductionIdentifiers.removeLast();
                        actionProductionAttributes.removeLast();
                        attributeTemps.removeLast();
                    }

                    if (getText(rightSideElement, "pref").equals("unary")) {
                        String unaryPrefCollection = getText(rightSideElement, "unaryPrefCollection");
                        String delims = "[,]";
                        String[] tokens = unaryPrefCollection.split(delims);
                        StringBuilder buildRightSide = new StringBuilder();

                        for (int i = 0; i < tokens.length; i++) {
                            if (i != 0) {
                                buildRightSide.append(",\n");
                            }
                            String operatorBaseString = operatorBaseString(operatorIndex, tokens[i]);
                            buildRightSide.append(operatorBaseString);
                            buildRightSide.append(" = true");
                        }
                        rightSide = buildRightSide.toString();
                    } else if (getText(rightSideElement, "pref").equals("binary")) {
                        String binaryPref = getText(rightSideElement, "binaryPref");
                        String thatValueID = getIndexFromID(getText(rightSideElement, "secondValue"), localVariablePathsWithID);
                        operatorIndex = getOperatorIndex(operatorIndex);
                        thatValueID = getOperatorIndex(thatValueID);
                        if (binaryPref.equals("isBetterTo")) {
                            rightSide = functionCallWithTwoIDs("addBetterTo", operatorIndex, thatValueID);
                        } else if (binaryPref.equals("isUnaryOrBinaryIndifferentTo")) {
                            rightSide = functionCallWithTwoIDs("addBinaryIndifferentTo", operatorIndex, thatValueID);
                        }
                    }
                }
            } else if (rightSideElement.getProperty("const") != null) {
                actionProductionValues.add(getText(rightSideElement, "const"));
            } else if (rightSideElement.getProperty("var") != null) {
                String rightSideVar = getText(rightSideElement, "var");
                String variable = conditionSideVariablesToTemps.get(rightSideVar);
                if (variable == null) {
                    variable = SoarTranslator.simplifiedString(getVariable(rightSideVar, localVariablePathsWithID));
                }
                actionProductionValues.add(variable);
            }
        }
        if (actionProductionFunctions.size() < actionProductionValues.size()) {
            actionProductionFunctions.add("0");
        }
        return rightSide;
    }

    private String functionCallWithTwoIDs(String function, String index1, String index2) {
        return function + "(" + index1 + ", " + index2 + ")";
    }


    @Override
    public Node visitPrint(SoarParser.PrintContext ctx) {
        return null;
    }

    private String getVariableOrTemp(SoarParser.ValueContext ctx) {
        StringBuilder variableOrTemp = new StringBuilder();
        if (ctx.variable() == null) {
            variableOrTemp.append(SoarTranslator.simplifiedString(ctx.constant().getText()));
        } else if (conditionSideVariablesToTemps.get(ctx.variable().getText()) != null) {
            variableOrTemp.append(conditionSideVariablesToTemps.get(ctx.variable().getText()));
        }
        return variableOrTemp.toString();
    }

    @Override
    public Node visitFunc_call(SoarParser.Func_callContext ctx) {
        SoarParser.ValueContext leftContext = ctx.value(0);
        SoarParser.ValueContext rightContext = ctx.value(1);

        String leftSide = getVariableOrTemp(leftContext);

        String funcName = ctx.func_name().getText();
        String result;
        switch(funcName) {
            case("+"): result = "addFunction";
                       break;
            case("-"): result = "subtractFunction";
                break;
            case("*"): result = "multiplyFunction";
                break;
            case("/"): result = "divideFunction";
                break;
            default: result = "";
                     break;
        }

        Node returnNode = textAsNode("expr", result);
        returnNode.setProperty("firstValue", leftSide);
        returnNode.setProperty("secondValue", getVariableOrTemp(rightContext));

        return returnNode;
    }

    @Override
    public Node visitFunc_name(SoarParser.Func_nameContext ctx) {
        return null;
    }

    @Override
    public Node visitValue(SoarParser.ValueContext ctx) {
        Node returnNode = ctx.children.get(0).accept(this);
        String property;
        if (ctx.constant() != null) {
            property = "const";
        } else if (ctx.variable() != null) {
            property = "var";
        } else {
            property = "expr";
        }
        returnNode.setProperty("constVarExpr", property);
        return returnNode;

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

    @Override
    public Node visitValue_make(SoarParser.Value_makeContext ctx) {
        Node value = ctx.value().accept(this);

        if (((SoarParser.Attr_value_makeContext) ctx.parent).variable_or_sym_constant().get(0).getText().equals("operator")) {
            if (ctx.value_pref_binary_value() != null) {
                Node valuePrefBinaryValue = ctx.value_pref_binary_value().accept(this);

                value.setProperty("binaryPref", getText(valuePrefBinaryValue, "preference"));
                value.setProperty("secondValue", getText(valuePrefBinaryValue, "secondValue"));
                value.setProperty("pref", "binary");
            } else if (ctx.value_pref_clause().size() != 0) {
                value.setProperty("unaryPrefCollection", getPreferenceCollection(ctx));
                value.setProperty("pref", "unary");
            } else {
                value.setProperty("unaryPrefCollection", "isAcceptable,");
                value.setProperty("pref", "unary");
            }
        } else if (ctx.value_pref_clause().size() != 0) {
            value.setProperty("removeWme", getPreferenceCollection(ctx));
            value.setProperty("pref", "remove");
        }
        return value;
    }

    private String getPreferenceCollection(SoarParser.Value_makeContext ctx) {
        StringBuilder preferences = new StringBuilder();
        for (SoarParser.Value_pref_clauseContext value_pref_clauseContext : ctx.value_pref_clause()) {
            if (preferences.length() > 0) {
                preferences.append(",");
            }
            preferences.append(getText(value_pref_clauseContext.accept(this), "unaryPref"));
        }
        return preferences.toString();
    }

    private String getIndexFromID(String variableName, Map<String, String> localVariablePathsWithID) {
        String pathWithID = localVariablePathsWithID.get(variableName);
        String index;
        if (pathWithID == null) {
            index = conditionSideVariablesToTemps.get(variableName);
        } else {
            int indexOfLast_ = pathWithID.lastIndexOf("_");
            index = (Integer.parseInt(pathWithID.substring(indexOfLast_ + 1)) - 1) + "";
        }
        return index;
    }

    @Override
    public Node visitValue_pref_binary_value(SoarParser.Value_pref_binary_valueContext ctx) {
        Node valuePrefNode = null;

        if (ctx.unary_or_binary_pref() != null) {
            Node unaryOrBinaryPref = ctx.unary_or_binary_pref().accept(this);

            Node secondValue = ctx.value().accept(this);
            String secondValueProperty;

            if (getText(unaryOrBinaryPref, "unaryBinaryPref").equals("isWorseTo")) {
                unaryOrBinaryPref.setProperty("unaryBinaryPref", "isBetterTo");
                secondValueProperty = getText(secondValue, "var");
            } else {
                if (ctx.value().constant() != null) {
                    secondValueProperty = getText(secondValue, "const");
                } else {
                    secondValueProperty = getText(secondValue, "var");
                }
            }

            valuePrefNode = textAsNode("preference", getText(unaryOrBinaryPref, "unaryBinaryPref"));
            valuePrefNode.setProperty("secondValue", secondValueProperty);
        }
        return valuePrefNode;
    }

    @Override
    public Node visitUnary_pref(SoarParser.Unary_prefContext ctx) {
        Node prefNode = null;
        String isWhat = UtilityForVisitors.unaryToString(ctx.getText().charAt(0));
        if (isWhat != null) {
            prefNode = textAsNode("unaryPref", isWhat);
        }
        return prefNode;
    }

    @Override
    public Node visitUnary_or_binary_pref(SoarParser.Unary_or_binary_prefContext ctx) {
        Node prefNode = null;
        String isWhat = UtilityForVisitors.unaryOrBinaryToString(ctx.getText().charAt(0), _unaryOrBinaryFlag);
        if (isWhat != null) {
            prefNode = textAsNode("unaryBinaryPref", isWhat);
        }
        return prefNode;
    }

    public Node visitValue_pref_clause(SoarParser.Value_pref_clauseContext ctx) {
        String preference = null;
        if (ctx.unary_or_binary_pref() != null) {
            _unaryOrBinaryFlag = true;
            preference = getText(ctx.unary_or_binary_pref().accept(this), "unaryBinaryPref");
            _unaryOrBinaryFlag = false;
        } else if (ctx.unary_pref() != null) {
            preference = getText(ctx.unary_pref().accept(this), "unaryPref");
        }

        return textAsNode("unaryPref", preference);
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
        ourDocument.insert(t, _lastTemplate);
        _lastTemplate = t;
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
        if (nailsXY != null) {
            Nail n = ret.createNail();
            n.setProperty("x", nailsXY[0]);
            n.setProperty("y", nailsXY[1]);
            Node last = ret.insert(n, null);
            for (int i = 2; i < nailsXY.length; i += 2) {
                if (nailsXY[i] != null && nailsXY[i + 1] != null) {
                    n = ret.createNail();
                    n.setProperty("x", nailsXY[i]);
                    n.setProperty("y", nailsXY[i + 1]);
                    last = ret.insert(n, last);
                }
            }
        }
        return ret;
    }

    private Element getScheduler() {
        getRunScheduler();
        getAVUtility();
        return getAttributeValueTemplate();
    }

    private Element getRunScheduler() {
        String startId = getCounter();

        Template runScheduler = makeTemplate("Scheduler");

        runScheduler.setProperty("declaration", "bool checkApplyRetract;\n");

        int[] lastLocationCoords = {-152, 0};

        Location lastLocation = makeLocationWithCoordinates(runScheduler, "Start", startId, true, true, lastLocationCoords[0], lastLocationCoords[1], lastLocationCoords[0] - 48, lastLocationCoords[1] - 32);

        String nextAssignment = "addOperator = true,\nvalueFunction = 0,\nglobalIdentifier = _state,\nglobalAttribute = superstate,\nglobalValue = nil,\nglobalDoesContain = 1";
        lastLocation = addHorizontalLocation(runScheduler, lastLocation, lastLocationCoords, "Set_Superstate_Nil", null, null, nextAssignment, false, null);

        Location proposalLocation = addHorizontalLocation(runScheduler, lastLocation, lastLocationCoords, "Proposal", null, "!addOperator", "initialize(operators)", false, null);
        lastLocation = proposalLocation;

        lastLocation = addHorizontalLocation(runScheduler, lastLocation, lastLocationCoords, "Run_Retract", "Run_Rule!", "!halt", "productionFired = false", false, null);
        goBackToProvidedLocation(runScheduler, lastLocation, proposalLocation, lastLocationCoords, null, "halt", false);
        lastLocation = addHorizontalLocation(runScheduler, lastLocation, lastLocationCoords, null, null, "stackConditionIndex == -1 &&\nstackActionIndex == -1 &&\n!addOperator", "isRetracting = true", false, null);
        lastLocation = addHorizontalLocation(runScheduler, lastLocation, lastLocationCoords, "Ready_Decision", "Run_Rule!", null, "checkApplyRetract = true", false, null);

        int xTextLocation = lastLocationCoords[0] + 10;
        makeEdgeWithNails(runScheduler, lastLocation, lastLocation, null, null, "Reset_Apply!", new Integer[]{xTextLocation, lastLocationCoords[1] + SIZE_OF_TEXT*4}, "stackRetractIndex == -1 &&\ncheckApplyRetract", new Integer[]{xTextLocation, lastLocationCoords[1] + SIZE_OF_TEXT * 5}, "checkApplyRetract = false", new Integer[]{xTextLocation, lastLocationCoords[1] + SIZE_OF_TEXT*7}, new Integer[]{lastLocationCoords[0], lastLocationCoords[1] + SIZE_OF_TEXT * 7});

        goBackToProvidedLocation(runScheduler, lastLocation, proposalLocation, lastLocationCoords, "!checkApplyRetract &&\nproductionFired &&\nstackRetractIndex == -1", "isRetracting = false,\nretractOperatorsIndex = 0", false);
        lastLocation = addHorizontalLocation(runScheduler, lastLocation, lastLocationCoords, "Decision", "Reset_Apply!", "!checkApplyRetract &&\n!productionFired &&\nstackRetractIndex == -1", "isRetracting = false,\nfillOthers(),\nretractOperatorsIndex = 0", false, null);
        lastLocation = addHorizontalLocation(runScheduler, lastLocation, lastLocationCoords, "Ready_Application", "Require_Test!", null, null, false, null);
        Location applicationLocation = addHorizontalLocation(runScheduler, lastLocation, lastLocationCoords, "Application", "Continue_Run?", null, null, false, null);
        lastLocation = applicationLocation;
        lastLocation = addHorizontalLocation(runScheduler, lastLocation, lastLocationCoords, "Back_To_Proposal", "Run_Rule!", null, "productionFired = false", false, null);
        goBackToProvidedLocation(runScheduler, lastLocation, proposalLocation, lastLocationCoords, null, "halt", false);
        lastLocation = addHorizontalLocation(runScheduler, lastLocation, lastLocationCoords, null, null, "stackConditionIndex == -1 &&\nstackActionIndex == -1 &&\n!addOperator", "isRetracting = true,\nretractOperatorsIndex = 0", false, null);
        lastLocation = addHorizontalLocation(runScheduler, lastLocation, lastLocationCoords, "Run_Retract_Again", "Run_Rule!", null, "checkApplyRetract = true", false, null);
        goBackToProvidedLocation(runScheduler, lastLocation, applicationLocation, lastLocationCoords, "!checkApplyRetract &&\nproductionFired &&\nstackRetractIndex == -1", "isRetracting = false,\nretractOperatorsIndex = 0", true);
        String guard = "!checkApplyRetract &&\n!productionFired &&\nstackRetractIndex == -1";
        nextAssignment = "clearFill(required),\nclearFill(acceptable),\nclearFill(best),\nisRetracting = false,\nremoveOperator = true,\nglobalIdentifier = finalOp,\nglobalAttribute = operator,\nretractOperatorsIndex = 0";
        goBackToProvidedLocation(runScheduler, lastLocation, proposalLocation, lastLocationCoords, guard, nextAssignment, false);

        xTextLocation = lastLocationCoords[0] + 10;
        makeEdgeWithNails(runScheduler, lastLocation, lastLocation, null, null, "Reset_Apply!", new Integer[]{xTextLocation, lastLocationCoords[1] + SIZE_OF_TEXT*4}, "stackRetractIndex == -1 &&\ncheckApplyRetract", new Integer[]{xTextLocation, lastLocationCoords[1] + SIZE_OF_TEXT * 5}, "checkApplyRetract = false", new Integer[]{xTextLocation, lastLocationCoords[1] + SIZE_OF_TEXT*7}, new Integer[]{lastLocationCoords[0], lastLocationCoords[1] + SIZE_OF_TEXT * 7});
        return runScheduler;
    }

    private void addExtraAV(String AVName, int numValues, String identifier, String attribute, StringBuilder system, StringBuilder instantiationsCollection) {
        system.append(AVName);
        instantiationsCollection.append(AVName);
        instantiationsCollection.append(" = ");
        instantiationsCollection.append("Attribute_Value(");
        instantiationsCollection.append(numValues + ", " + identifier + ", " + attribute);
        instantiationsCollection.append(");\n");
    }

    private String[] makeAttributeValueTemplates() {
        StringBuilder instantiationsCollection = new StringBuilder();
        StringBuilder systemProcesses = new StringBuilder(" ");
        for (UppaalAttributeValueTriad UAT : _AVCollection) {
            if (systemProcesses.length() > 1) {
                systemProcesses.append(", ");
            }
            systemProcesses.append(SoarTranslator.simplifiedString(UAT.getName()));
            instantiationsCollection.append(SoarTranslator.simplifiedString(UAT.getName()));
            instantiationsCollection.append(" = ");
            instantiationsCollection.append("Attribute_Value(");
            instantiationsCollection.append(UAT.getNumValues() + ", " + SoarTranslator.simplifiedString(UAT.getOperatorIndex()) + ", " + UAT.getAttributeIndex());
            instantiationsCollection.append(");\n");
        }

        if (systemProcesses.length() > 1) {
            systemProcesses.append(", ");
        }
        addExtraAV("AV_final_operator", 1, "finalOp", "operator", systemProcesses, instantiationsCollection);
        systemProcesses.append(", ");
        addExtraAV("AV_state_superstate", 1, "_state", "superstate", systemProcesses, instantiationsCollection);

        return new String[]{instantiationsCollection.toString(), systemProcesses.toString()};
    }

    private Element getAttributeValueTemplate() {
        String startId = getCounter();
        String middleAddLocationID = getCounter();

        Template attributeValueTemplate = makeTemplate("Attribute_Value");
        attributeValueTemplate.setProperty("parameter", "const int NUM_VALUES, const int OPERATOR_ID, const int ATTRIBUTE_INDEX");
        attributeValueTemplate.setProperty("declaration",
                "int values[NUM_VALUES];\n" +
                "int valuesIndex = 0;\n" +
                "int containsIndex = -1;\n" +
                "\n" +
                "void doValuesContain() {\n" +
                "\tif (globalValue == nilAnything) {\n" +
                "\t\tif (lookAheadArray[lookAheadIndex] < valuesIndex) {\n" +
                "\t\t\tglobalValue = values[lookAheadArray[lookAheadIndex]];\n" +
                "\t\t\tlookAheadArray[lookAheadIndex]++;\n" +
                "\t\t} else {\n" +
                "\t\t\tglobalDoesContain = -1;\n" +
                "\t\t\tlookAheadArray[lookAheadIndex] = 0;\n" +
                "\t\t}\n" +
                "\t} else {\n" +
                "\t\tint contains = -1;\n" +
                "\t\tif (globalValue == EMPTY && valuesIndex == 0) {\n" +
                "\t\t\tcontains = 1;\n" +
                "\t\t} else {\n" +
                "\t\t\tint i;\n" +
                "\t\t\tfor (i = 0; i < valuesIndex; i++) {\n" +
                "\t\t\t\tif (values[i] == globalValue) {\n" +
                "\t\t\t\t\tcontains = 1;\n" +
                "\t\t\t\t\ti = valuesIndex;\n" +
                "\t\t\t\t}\n" +
                "\t\t\t}\n" +
                "\t\t}\n" +
                "\t\tif (contains == 1) {\n" +
                "\t\t\tglobalDoesContain = 1;\n" +
                "\t\t} else {\n" +
                "\t\t\tglobalDoesContain = -1;\n" +
                "\t\t}\n" +
                "\t}\n" +
                "}\n" +
                "\n" +
                "void addValue() {\n" +
                "\tif (containsIndex == -1) {\n" +
                "\t\tvalues[valuesIndex] = globalValue;\n" +
                "\t\tif (valueFunction == addFunction) {\n" +
                "\t\t\tvalues[valuesIndex] += attributeFunction;\n" +
                "\t\t} else if (valueFunction == subtractFunction) {\n" +
                "\t\t\tvalues[valuesIndex] -= attributeFunction;\n" +
                "\t\t}\n" +
                "\t\tvaluesIndex++;\n" +
                "\t}\n" +
                "\taddOperator = false;\n" +
                "}\n" +
                "\n" +
                "int getIndexOfValue() {\n" +
                "\tint i = 0;\n" +
                "\tfor (i = 0; i < valuesIndex; i++) {\n" +
                "\t\tif (values[i] == globalValue) {\n" +
                "\t\t\treturn i;\n" +
                "\t\t}\n" +
                "\t}\n" +
                "\treturn -1;\n" +
                "}\n" +
                "\n" +
                "void removeValue() {\n" +
                "\twhile (valuesIndex > 0) {\n" +
                "\t\tvaluesIndex--;\n" +
                "\t\tvalues[valuesIndex] = 0;\n" +
                "\t}\n" +
                "\tcurrentNumAttributes--;\n" +
                "\tif (currentNumAttributes == 0) {\n" +
                "\t\tremoveNestedCheckArray();\n" +
                "\t\tglobalIndex++;\n" +
                "\t\tif (globalIndex == nestedCheckIndex) {\n" +
                "\t\t\tremoveOperator = false;\n" +
                "\t\t\tnestedCheckIndex = 0;\n" +
                "\t\t} else {\n" +
                "\t\t\tcurrentNumAttributes = getNumAttributes(nestedCheckArray[globalIndex]);\n" +
                "\t\t}\n" +
                "\t}\n" +
                "}\n" +
                "\n" +
                "void removeSpecificValue() {\n" +
                "\tint i = containsIndex;\n" +
                "\tif (i != -1) {\n" +
                "\t\tfor (i = containsIndex; i < valuesIndex - 1; i++) {\n" +
                "\t\t\tvalues[i] = values[i + 1];\n" +
                "\t\t}\n" +
                "\t\tvaluesIndex--;\n" +
                "\t\tvalues[valuesIndex] = 0;\n" +
                "\t}\n" +
                "\t if(isRetracting) {\n" +
                "\t\tint numAttributes = getNumAttributes(globalValue);\n" +
                "\t\tif (numAttributes > 0) {\n" +
                "\t\t\taddToNestedCheckArray(globalValue);\n" +
                "\t\t}\n" +
                "\t}\n" +
                "\taddOperator = false;\n" +
                "}");

        Location startLocation = makeLocationWithCoordinates(attributeValueTemplate, "Start", startId, true, true, -739, -195, -780, -229);
        Location middleAddLocation = makeLocationWithCoordinates(attributeValueTemplate, null, middleAddLocationID, true, false, -229, -195, null, null);

        makeEdgeWithNails(attributeValueTemplate, middleAddLocation, startLocation, null, null, null, null, "valueFunction == remove", new Integer[]{-425, -331}, "removeSpecificValue()", new Integer[]{-425, -314}, new Integer[]{-535, -340});
        makeEdgeWithNails(attributeValueTemplate, middleAddLocation, startLocation, null, null, null, null, "valueFunction != remove", new Integer[]{-382, -127}, "addValue()", new Integer[]{-382, -110}, new Integer[]{-535, -68});
        makeEdgeWithNails(attributeValueTemplate, startLocation, startLocation, null, null, null, null, "removeOperator &&\ncurrentNumAttributes > 0 &&\nnestedCheckArray[globalIndex] == OPERATOR_ID", new Integer[]{-790, -85}, "removeValue()", new Integer[]{-790, -34}, new Integer[]{-739, -144, -688, -93, -790, -93, -739, -144});
        makeEdgeWithNails(attributeValueTemplate, startLocation, startLocation, null, null, null, null, "globalDoesContain == 0 &&\nglobalIdentifier == OPERATOR_ID &&\nglobalAttribute == ATTRIBUTE_INDEX", new Integer[]{-1156, -204}, "doValuesContain()", new Integer[]{-1156, -153}, new Integer[]{-739, -144, -807, -144, -807, -195});
        makeEdge(attributeValueTemplate, startLocation, middleAddLocation, null, null, null, null, "addOperator &&\nglobalIdentifier == OPERATOR_ID &&\nglobalAttribute == ATTRIBUTE_INDEX", new Integer[]{-654, -255}, "containsIndex =getIndexOfValue()", new Integer[]{-654, -187});

        String[] instantiationsAndSystem = makeAttributeValueTemplates();
        attributeValueTemplate.setProperty("instantiations", instantiationsAndSystem[0]);
        attributeValueTemplate.setProperty("system", instantiationsAndSystem[1]);

        return attributeValueTemplate;
    }

    private void makeLoop(String direction, Template currentTemplate, Location loopLocation, String guard, String assignment) {
        int[] constants = {417, 51, 68};
        if (direction.equals("right")) {
            constants[0] = -75;
            constants[2] *= -1;
        }
        int xTextLocation = loopLocation.getX() - constants[0];
        Integer[] nails = new Integer[]{loopLocation.getX(), loopLocation.getY() + constants[1], loopLocation.getX() - constants[2], loopLocation.getY() + constants[1], loopLocation.getX() - constants[2], loopLocation.getY()};
        makeEdgeWithNails(currentTemplate, loopLocation, loopLocation, null, null, null, new Integer[]{xTextLocation, loopLocation.getY() - 10 - (SIZE_OF_TEXT * (getNumLines(guard, " &&") + getNumLines(assignment, ",")))}, guard, new Integer[]{xTextLocation, loopLocation.getY() - 10}, assignment, new Integer[]{xTextLocation, loopLocation.getY() - 10 + getNumLines(guard, " &&")*SIZE_OF_TEXT}, nails);
    }

    private Element getAVUtility() {
        Template AVUtilityTemplate = makeTemplate("Attribute_Value_Utility");

        AVUtilityTemplate.setProperty("declaration",
                "void checkCondition() {\n" +
                "\tbool conditionSatisfied = false;\n" +
                "\tif (valueFunction == isNotEqualTo && globalIdentifier != globalValue) {\n" +
                "\t\tconditionSatisfied = true;\n" +
                "\t} else if (valueFunction == isGreaterThan && globalIdentifier > globalValue) {\n" +
                "\t\tconditionSatisfied = true;\n" +
                "\t} else if (valueFunction == isLessThan && globalIdentifier < globalValue) {\n" +
                "\t\tconditionSatisfied = true;\n" +
                "\t}\n" +
                "\tif (conditionSatisfied) {\n" +
                "\t\tglobalDoesContain = 1;\n" +
                "\t} else {\n" +
                "\t\tglobalDoesContain = -1;\n" +
                "\t}\n" +
                "}\n" +
                "\n" +
                "void nextNumBut() {\n" +
                "\tint nextIndex = lookAheadArray[lookAheadIndex];\n" +
                "\tint nextElement = getNumButNextElement(globalAttribute, nextIndex);\n" +
                "\tint i;\n" +
                "\tif (nextElement == -1) {\n" +
                "\t\tlookAheadArray[lookAheadIndex] = 0;\n" +
                "\t\tglobalDoesContain = -1;\n" +
                "\t} else {\n" +
                "\t\tattributeFunction = nextElement;\n" +
                "\t\tlookAheadArray[lookAheadIndex] = nextIndex + 1;\n" +
                "\t\tglobalDoesContain = 1;\n" +
                "\t}\n" +
                "}\n" +
                "\n" +
                "void catchAll() {\n" +
                "\tglobalDoesContain = -1;\n" +
                "}\n" +
                "\n");

        Location startLocation = makeLocationWithCoordinates(AVUtilityTemplate, "Start", getCounter(), true, true, -739, -195, -780, -229);

        makeLoop("left", AVUtilityTemplate, startLocation, "globalDoesContain == 0 &&\nglobalAttribute == extraRestriction", "checkCondition()");
        if (_disjunctionArrayNameToArray.values().size() > 0) {
            makeLoop("right", AVUtilityTemplate, startLocation, "globalDoesContain == 0 &&\nglobalAttribute <= noneBut_1", "nextNumBut()");
        }

        StringBuilder catchAll = new StringBuilder("globalDoesContain == 0 &&\n(");
        int shift = 2;
        int count;
        boolean first = true;
        for (Map.Entry<String, LinkedList<String>> nextVariableToAttribute : _variableToAttributes.entrySet()) {
            if (!first) {
                catchAll.append(" ||\n");
                first = true;
            }
            String nextIdentifier = SoarTranslator.simplifiedString(nextVariableToAttribute.getKey());
            if (nextIdentifier.equals("state__1")) {
                nextIdentifier = "_state";
            }
            String operatorValue = "globalIdentifier == " + nextIdentifier + " &&\n";
            count = 0;
            catchAll.append("(");
            for (String nextAttribute : nextVariableToAttribute.getValue()) {
                if (count != 0) {
                    catchAll.append(" &&\n");
                } else if (nextIdentifier.equals("_state")) {
                    catchAll.append(operatorValue);
                    catchAll.append("globalAttribute != superstate &&\n");
                    count++;
                }
                catchAll.append(operatorValue);
                catchAll.append("globalAttribute != ").append(nextAttribute);
                count++;
                first = false;
            }
            shift += count*2;
            catchAll.append(")");
        }
        if (catchAll.length() > 0) {
            catchAll.append(" &&\n");
        }

        count = 0;
        for (Map.Entry<String, String[]> nextArrayNameToArray : _disjunctionArrayNameToArray.entrySet()) {
            if (count != 0) {
                catchAll.append(" &&\n");
            }
            catchAll.append("globalAttribute != ").append(nextArrayNameToArray.getKey());
            count++;
        }

        if (catchAll.length() > 0) {
            catchAll.append(" &&\n");
        }
        catchAll.append("globalAttribute != extraRestriction)");
        count += 1;
        shift += count;
        String guard = catchAll.toString();

        makeEdgeWithNails(AVUtilityTemplate, startLocation, startLocation, null, null, null, null, guard, new Integer[]{-790, -85}, "catchAll()", new Integer[]{-790, -85 + (shift*SIZE_OF_TEXT)}, new Integer[]{-739, -144, -688, -93, -790, -93, -739, -144});

        return AVUtilityTemplate;
    }

    private Element getOperatorPreferences() {
        Template operatorPreferencesTemplate = makeTemplate("preferenceResolutionTemplate");

        operatorPreferencesTemplate.setProperty("declaration",
                "bool requiredAndProhibited;\n" +
                        "int currentOp;\n" +
                        "int finalOperatorIndex;\n" +
                        "bool isRequiredAndProhibited() {\n" +
                        "\tint i = 0;\n" +
                        "\twhile (i < N && required[i] != 0) {\n" +
                        "\t\tif (operators[required[i]-1].operator.isProhibited) {\n" +
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
                        "\t\tif (operators[acceptable[i]-1].operator.isProhibited) {\n" +
                        "\t\t\tremove(i, acceptable);\n" +
                        "\t\t} else {\n" +
                        "\t\t\ti++;\n" +
                        "\t\t}\n" +
                        "\t}\n" +
                        "}\n" +
                        "\n" +
                        "int variablesContains(int testId) {\n" +
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
                        "\t\t\tcontainID = variablesContains(operators[acceptable[i]-1].better[j]);\n" +
                        "\t\t\tif (!temp[operators[acceptable[i]-1].better[j] - 1] && containID != -1) {\n" +
                        "\t\t\t\ttemp[operators[acceptable[i]-1].better[j] - 1] = true;\n" +
                        "\t\t\t}\n" +
                        "\t\t\tj++;\n" +
                        "\t\t}\n" +
                        "\t\tif (operators[acceptable[i]-1].operator.isRejected) {\n" +
                        "\t\t\ttemp[acceptable[i] - 1] = true;\n" +
                        "\t\t}\n" +
                        "\t\ti++;\n" +
                        "\t}\n" +
                        "\ti = 0;\n" +
                        "\twhile (i < N) {\n" +
                        "\t\tif (temp[i]) {\n" +
                        "\t\t\tcontainID = variablesContains(i+1);\n" +
                        "\t\t\tif (containID != -1) {\n" +
                        "\t\t\t\tremove(containID, acceptable);\n" +
                        "\t\t\t}\n" +
                        "\t\t}\n" +
                        "\t\ti++;\t\n" +
                        "\t}" +
                        "}\n" +
                        "\n" +
                        "void removeBest() {\n" +
                        "\tint i = 0;\n" +
                        "\twhile (i < N && acceptable[i] != 0) {\n" +
                        "\t\tif (!operators[acceptable[i]-1].operator.isBest) {\n" +
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
                        "\t\tif (operators[acceptable[i]-1].operator.isUnaryIndifferent == 0 && !operators[acceptable[i]-1].operator.hasNumericIndifferent) {\n" +
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
                        "\t\t\t\tif(variablesContains(operators[i].binaryIndifferent[j]) == -1) {\n" +
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
                        "}");
        Location noName = makeLocationWithCoordinates(operatorPreferencesTemplate, null, getCounter(), true, false, -3488, -864, null, null);
        Location noName1 = makeLocationWithCoordinates(operatorPreferencesTemplate, null, getCounter(), true, false, -3488, -920, null, null);
        Location noName2 = makeLocationWithCoordinates(operatorPreferencesTemplate, null, getCounter(), true, false, -3488, -1120, null, null);
        Location noName4 = makeLocationWithCoordinates(operatorPreferencesTemplate, null, getCounter(), true, false, -3808, -518, null, null);
        Location tie = makeLocationWithCoordinates(operatorPreferencesTemplate, "Tie", getCounter(), true, false, -2966, -706, -2976, -736);
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

        makeEdgeWithNails(operatorPreferencesTemplate, indifferentTest, done, "x : int[0, N-1]", new Integer[]{-3208, -648}, null, null, "areAllIndifferent()", new Integer[]{-3224, -616}, "finalOperatorIndex = acceptable[modulus(x)]", new Integer[]{-3280, -600}, new Integer[]{-2616, -624});
        makeEdge(operatorPreferencesTemplate, noName, worstFilter, null, null, null, null, null, null, "numLeft = getNumLeft(acceptable)", new Integer[]{-3760, -848});
        makeEdge(operatorPreferencesTemplate, bestFilter, noName1, null, null, null, null, null, null, "numLeft = getNumLeft(best)", new Integer[]{-3480, -960});
        makeEdge(operatorPreferencesTemplate, noName2, betterWorseFilter, null, null, null, null, null, null, "numLeft = getNumLeft(acceptable)", new Integer[]{-3480, -1104});
        makeEdge(operatorPreferencesTemplate, rejectFilter, noName2, null, null, null, null, "numLeft > 1", new Integer[]{-3480, -1176}, "removeWorseAndRejectedFromAcceptable()", new Integer[]{-3480, -1160});
        makeEdge(operatorPreferencesTemplate, betterWorseFilter, conflict, null, null, null, null, "numLeft == 0", new Integer[]{-3296, -1056}, null, null);
        makeEdgeWithNails(operatorPreferencesTemplate, indifferentTest, tie, null, null, null, null, "!areAllIndifferent()", new Integer[]{-3174, -730}, null, null, new Integer[]{-3296, -624, -3254, -706});
        makeEdge(operatorPreferencesTemplate, worstFilter, indifferentTest, null, null, null, null, "numLeft > 1", new Integer[]{-3480, -776}, "removeWorst()", new Integer[]{-3480, -760});
        makeEdgeWithNails(operatorPreferencesTemplate, noName1, noName, null, null, null, null, "numLeft > 0", new Integer[]{-3456, -920}, "removeBest()", new Integer[]{-3456, -880}, new Integer[]{-3456, -888});
        makeEdgeWithNails(operatorPreferencesTemplate, noName1, noName, null, null, null, null, "numLeft == 0", new Integer[]{-3624, -896}, null, null, new Integer[]{-3520, -888});
        makeEdgeWithNails(operatorPreferencesTemplate, worstFilter, done, null, null, null, null, "numLeft == 1", new Integer[]{-3112, -840}, "finalOperatorIndex = acceptable[0]", new Integer[]{-3112, -808}, new Integer[]{-2616, -816});
        makeEdgeWithNails(operatorPreferencesTemplate, worstFilter, noChange, null, null, null, null, "numLeft == 0", new Integer[]{-3224, -936}, null, null, new Integer[]{-3312, -816, -3264, -912, -2976, -912, -2872, -912});
        makeEdge(operatorPreferencesTemplate, betterWorseFilter, bestFilter, null, null, null, null, "numLeft > 0", new Integer[]{-3480, -1040}, null, null);
        makeEdgeWithNails(operatorPreferencesTemplate, rejectFilter, noChange, null, null, null, null, "numLeft == 0", new Integer[]{-3080, -1216}, null, null, new Integer[]{-3304, -1192, -2872, -1192});
        makeEdgeWithNails(operatorPreferencesTemplate, rejectFilter, done, null, null, null, null, "numLeft == 1", new Integer[]{-2856, -1296}, "finalOperatorIndex = acceptable[0]", new Integer[]{-2880, -1264}, new Integer[]{-3328, -1192, -3264, -1272, -2616, -1272});
        makeEdge(operatorPreferencesTemplate, prohibitFilter, rejectFilter, null, null, null, null, null, null, "numLeft = getNumLeft(acceptable)", new Integer[]{-3744, -1240});
        makeEdge(operatorPreferencesTemplate, acceptableCollect, prohibitFilter, null, null, null, null, null, null, "removeProhibitedFromAcceptable()", new Integer[]{-3472, -1312});
        makeEdgeWithNails(operatorPreferencesTemplate, requireTest, acceptableCollect, null, null, null, null, "numLeft == 0", new Integer[]{-3480, -1384}, null, null, new Integer[]{-3488, -1352});
        makeEdge(operatorPreferencesTemplate, noName3, constraintFailure, null, null, null, null, "operators[currentOp-1].operator.isProhibited", new Integer[]{-2968, -1488}, null, null);
        makeEdgeWithNails(operatorPreferencesTemplate, noName3, done, null, null, null, null, "!operators[currentOp-1].operator.isProhibited", new Integer[]{-2808, -1456}, "finalOperatorIndex = currentOp", new Integer[]{-2850, -1416}, new Integer[]{-2616, -1424});
        makeEdge(operatorPreferencesTemplate, requireTest, noName3, null, null, null, null, "numLeft == 1", new Integer[]{-3256, -1448}, "currentOp = required[0]", new Integer[]{-3272, -1416});
        makeEdgeWithNails(operatorPreferencesTemplate, requireTest, constraintFailure, null, null, null, null, "numLeft > 1", new Integer[]{-3144, -1552}, null, null, new Integer[]{-3320, -1424, -3264, -1520});
        makeEdge(operatorPreferencesTemplate, start, requireTest, null, null, "Require_Test?", new Integer[]{-3624, -1520}, null, null, "numLeft = getNumLeft(required)", new Integer[]{-3728, -1496});
        String nextAssignment = "addOperator = true,\nvalueFunction = 0,\nglobalIdentifier = finalOp,\nglobalAttribute = operator,\nglobalValue = finalOperatorIndex";
        makeEdge(operatorPreferencesTemplate, done, noName4, null, null, null, null, null, null, nextAssignment + ",\nselectedFinalOperatorIndex = finalOperatorIndex", new Integer[]{-3280, -504});
        makeEdgeWithNails(operatorPreferencesTemplate, noName4, start, null, null, "Continue_Run!", new Integer[]{-3918, -1113}, "!addOperator", new Integer[]{-3918, -1097}, null, null, new Integer[]{-3808, -1536});

        return null;
    }
}
