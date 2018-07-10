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

    static final int SIZE_OF_TEXT = 16;
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
    private HashSet<String> _retractOperatorIndexes;
    private Map<Integer, String> _operatorIDToInverseActions = new HashMap<>();
    private LinkedList<String> _uppaalOperatorCollection;
    private LinkedList<UppaalAttributeValueTriad> _AVCollection;
    private Map<String, Map<String, String>> _variablesToPathWithID;
    private Map<String, Integer> _attributesToIDs;
    private Map<String, String> conditionSideVariablesToTemps;
    private LinkedList<String> conditionProductionIdentifiers;
    private LinkedList<String> conditionProductionAttributes;
    private LinkedList<String> conditionProductionValues;
    private LinkedList<String> conditionProductionTemp;
    private LinkedList<String> actionProductionIdentifiers;
    private LinkedList<String> actionProductionAttributes;
    private LinkedList<String> actionProductionValues;
    private LinkedList<String> actionProductionFunctions;
    private int _latestNum;
    private int _maxQuerySize;
    private int _latestIndex;
    private Map<String, Boolean> _productionToOSupported;
    private Map<String, Integer> _variableToNumAttributes;

    public UPPAALSemanticVisitor(Set<String> stringAttributeNames, Map<String, Map<String, String>> variablesPerProductionContext, Set<String> boolAttributeNames, int numOperators, Map<String, ProductionVariables> actualVariablesPerProduction, HashSet<Integer> takenValues, LinkedList<String> uppaalOperatorCollection, LinkedList<UppaalAttributeValueTriad> AVCollection, Map<String, Map<String, String>> variablesToPathWithID, Map<String, Integer> attributesToIDs, int maxQuerySize, Map<String, Boolean> productionToOSupported, Map<String, Integer> variableToNumAttributes) {
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
        _attributesToIDs = attributesToIDs;
        _latestNum = attributesToIDs.size() > uppaalOperatorCollection.size() ? attributesToIDs.size() + 2 : uppaalOperatorCollection.size() + 2;
        _maxQuerySize += maxQuerySize;
        _productionToOSupported = productionToOSupported;
        _variableToNumAttributes = variableToNumAttributes;
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

        String vars = "";

        vars += _booleanGlobals
                .stream()
                .map(SoarTranslator::simplifiedString)
                .map(var -> "bool " + var + "; \n")
                .collect(Collectors.joining());

        vars += "const int nil = 0;\n" +
                "const int nilAnything = -1;\n";

        StringBuilder globalVariables = new StringBuilder();
        for (String variable : _globals) {
            addConstantToGlobals(globalVariables, SoarTranslator.simplifiedString(variable), globalToIndex.get(variable));
        }
        int index = 1;
        for (String variable : _uppaalOperatorCollection) {
            addConstantToGlobals(globalVariables, variable, index++);
        }
        addConstantToGlobals(globalVariables, "finalOp", index++);
        addConstantToGlobals(globalVariables, "_state", -1);
        for (String variable : _attributesToIDs.keySet()) {
            addConstantToGlobals(globalVariables, variable, _attributesToIDs.get(variable));
        }
        addConstantToGlobals(globalVariables, "superstate", _latestNum - 1);
        for (String variable : _variableToNumAttributes.keySet()) {
            String variableText;
            if (variable.equals("state_-1")) {
                variableText = "state";
            } else {
                variableText = variable;
            }
            addConstantToGlobals(globalVariables, variableText + "_num_attributes", _variableToNumAttributes.get(variable));
        }

        vars += globalVariables.toString();

        vars += "broadcast chan Run_Rule;\n" +
                "broadcast chan Halt;\n" +
                "bool halt = false;\n" +
                "chan Continue_Run;\n" +
                "chan Require_Test;\n" +
                "bool isRetracting;\n" +
                "bool addOperator;\n" +
                "bool productionFired;\n" +
                "bool removeOperator;\n" +
                "int doesContain = -2;\n" +
                "const int EMPTY = -2;\n" +
                "const int numTemplates = " + _templateNames.size() + ";\n" +
                "int stackCondition[numTemplates];\n" +
                "int stackAction[numTemplates];\n" +
                "int stackRetract[numTemplates];\n" +
                "int stackConditionIndex = -1;\n" +
                "int stackActionIndex = -1;\n" +
                "int stackRetractIndex = -1;\n" +
                "int function;\n" +
                "const int remove = -3;\n" +
                "const int MAX_GLOBAL_SIZE = " + _maxQuerySize + ";\n" +
                "const int numAVs = 8;\n" +
                "int numAVCounter = 0;\n" +
                "int TEMP_GLOBAL_SIZE;\n" +
                "int operatorArray[MAX_GLOBAL_SIZE];\n" +
                "int attributeArray[MAX_GLOBAL_SIZE];\n" +
                "int valueArray[MAX_GLOBAL_SIZE];\n" +
                "int tempOrFuncArray[MAX_GLOBAL_SIZE];\n" +
                "int doesContainArray[MAX_GLOBAL_SIZE];\n" +
                "int doesContainTrue[MAX_GLOBAL_SIZE];\n" +
                "int doesContainDefault[MAX_GLOBAL_SIZE];\n" +
                "int globalIndex = 0;\n" +
                "bool checkContains;\n" +
                "broadcast chan Reset;";


        vars += "\n" +
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
                "\tstackRetractIndex = -1;\n" +
                "}\n" +
                "\n" +
                "void clearFill(int &ref[N]) {\n" +
                "\tint i = 0;\n" +
                "\twhile(i < N && ref[i] != 0) {\n" +
                "\t\tref[i] = 0;\n" +
                "\t}\n" +
                "}" +
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
                "void updateDoesContainTrueAndFalse() {\n" +
                "\tint i;\n" +
                "\tfor (i = 0; i < TEMP_GLOBAL_SIZE; i++) {\n" +
                "\t\tdoesContainTrue[i] = 1;\n" +
                "\t} \n" +
                "\tfor (i = TEMP_GLOBAL_SIZE; i < MAX_GLOBAL_SIZE; i++) {\n" +
                "\t\tdoesContainTrue[i] = 0;\n" +
                "\t}\n" +
                "}\n";

        vars += "typedef struct {\n" +
                "\tint savedTempAndFunction[MAX_GLOBAL_SIZE];\n" +
                "} Production;\n" +
                "\n";


        ourDocument.setProperty("declaration", vars);
    }

    private void getSystemElement(Element attributeValuePairs) {
        List<String[]> compoundNames = _templateNames.stream().map(name -> new String[]{name + "_0", name}).collect(Collectors.toList());
        StringBuilder system = new StringBuilder();
        system.append(compoundNames.stream().map(name -> name[0] + " = " + name[1] + "(); \n").collect(Collectors.joining()));
        system.append(attributeValuePairs.getProperty("instantiations").getValue());
        system.append("preferenceResolution = preferenceResolutionTemplate(); \n");
        system.append("scheduler = Scheduler(); \n");
        system.append("system " + compoundNames.stream().map(cName -> cName[0]).collect(Collectors.joining(", ")) + ", preferenceResolution, scheduler,");
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

//    private Integer[] getNailsForConditions(boolean isLastLocation, int[] startNailLocations, Integer[] shiftPossibleNails, boolean leadsToStart) {
//        if (isLastLocation && !leadsToStart) {
//            return new Integer[]{startNailLocations[0] + shiftPossibleNails[0], startNailLocations[1] + shiftPossibleNails[1]};
//        } else {
//            return new Integer[]{startNailLocations[0] + shiftPossibleNails[0], startNailLocations[1] + shiftPossibleNails[1], startNailLocations[2] + shiftPossibleNails[2], startNailLocations[3] + shiftPossibleNails[1]};
//        }
//    }

    private int getNameLocation(String name, int lastLocationCoordsX) {
        if (name == null) {
            return 0;
        }
        return lastLocationCoordsX - 10 - 10*(name.length() - 1);
    }

    private Location addHorizontalCondition (Template currentTemplate, Location lastLocation, int[] lastLocationCoords, String name, String synchronization, String stackGuard, String assignment, boolean mirrored) {
        int xTextLocation = lastLocationCoords[0] + (mirrored ? -370 : 0) + 25;
        int xTempCoords = lastLocationCoords[0] + (mirrored ? -370 : 370);
        Location lastLocationTemp = makeLocationWithCoordinates(currentTemplate, name, getCounter(), true, false, xTempCoords, 0, getNameLocation(name, xTempCoords), lastLocationCoords[1] - 32);

        makeEdge(currentTemplate, lastLocation, lastLocationTemp, null, null, synchronization, new Integer[]{xTextLocation, lastLocationCoords[1] - (getNumLines(stackGuard, " &&") + 1)*SIZE_OF_TEXT}, stackGuard, new Integer[]{xTextLocation, lastLocationCoords[1] - getNumLines(stackGuard, " &&")*SIZE_OF_TEXT}, assignment, new Integer[]{xTextLocation, lastLocationCoords[1] + 8});
        lastLocationCoords[0] = xTempCoords;
        return lastLocationTemp;
    }

//    private Location moveToNextStage(Template currentTemplate, Location lastLocation, int[] lastLocationCoords, String locationName, String synchronisation, String guard, String addToStack) {
//        Location lastLocationTemp = makeLocationWithCoordinates(currentTemplate, locationName, getCounter(), true, false, lastLocationCoords[0] + 400, 0, lastLocationCoords[0] + 290, -34);
//        makeEdgeWithNails(currentTemplate, lastLocation, lastLocationTemp, null, null, synchronisation, new Integer[]{lastLocationCoords[0] + 75, lastLocationCoords[1] + 85}, guard, new Integer[]{lastLocationCoords[0] + 75, lastLocationCoords[1] + 85}, addToStack, new Integer[]{lastLocationCoords[0] + 75, lastLocationCoords[1] + 120}, new Integer[]{lastLocationCoords[0] + 51, lastLocationCoords[1] + 110, lastLocationCoords[0] + 400, lastLocationCoords[1] + 110});
//        lastLocationCoords[0] += 400;
//        lastLocationCoords[1] = 0;
//        return lastLocationTemp;
//    }
//
//    private Location addVerticalConditions(Template currentTemplate, Location lastLocation, int[] lastLocationCoords, String[] guardCollection, Location conditionSource, String removeStack, int xTextLocation, boolean addExtraNail) {
//        for (int i = 1; i < guardCollection.length; i++) {
//            int lastLocationYTemp = lastLocationCoords[1] + 110;
//            Location lastLocationTemp = makeLocationWithCoordinates(currentTemplate, null, getCounter(), true, false, lastLocationCoords[0], lastLocationYTemp, null, null);
//
//            makeEdge(currentTemplate, lastLocation, lastLocationTemp, null, null, null, null, "doesContain == 1", new Integer[]{lastLocationCoords[0]+ 17, lastLocationCoords[1] + 8}, guardCollection[i], new Integer[]{lastLocationCoords[0] + 17, lastLocationCoords[1] + 8 + SIZE_OF_TEXT});
//            if (guardCollection[i].contains(",")) {
//                Integer[] nails = getNailsForConditions(i == guardCollection.length - 1 && !addExtraNail, new int[]{lastLocationCoords[0], lastLocationYTemp, lastLocationCoords[0], lastLocationYTemp}, new Integer[]{-51, 110, -355}, getText(conditionSource, "name").equals("Start"));
//                makeEdgeWithNails(currentTemplate, lastLocationTemp, conditionSource, null, null, null, null, "doesContain == -1", new Integer[]{xTextLocation, lastLocationYTemp + 85}, removeStack, new Integer[]{xTextLocation, lastLocationYTemp + 115}, nails);
//            }
//
//            lastLocationCoords[1] = lastLocationYTemp;
//            lastLocation = lastLocationTemp;
//        }
//        return lastLocation;
//    }

    private void goBackToStart(Template currentTemplate, Location lastLocation, Location startLocation, int[] lastLocationCoords, String guard, String assignment, boolean mirrored) {
        Integer[] nails = new Integer[]{lastLocationCoords[0], lastLocationCoords[1] - 110, startLocation.getX(), -110};
        int assignmentSpace = lastLocationCoords[1] - 110 - SIZE_OF_TEXT * (assignment.contains("halt") ? 0 : getNumLines(assignment, ","));
        int textLocationX = lastLocationCoords[0] + (mirrored ? 0 : - 370);
        Integer[] guardLocation = new Integer[]{textLocationX,  assignmentSpace - SIZE_OF_TEXT * getNumLines(guard, " &&")};
        Integer[] assignmentLocation = new Integer[]{textLocationX, assignmentSpace};
        makeEdgeWithNails(currentTemplate, lastLocation, startLocation, null, null, assignment.contains("halt") ? "Halt?" : (guard.contains("!") ?"Reset!" : null), new Integer[]{textLocationX, guardLocation[1] - SIZE_OF_TEXT}, guard, guardLocation, assignment.contains("halt") ? null : assignment, assignmentLocation, nails);
    }

//    private Location addHorizontalAction(Template currentTemplate, Location lastLocation, int[] lastLocationCoords, String stackGuard, String assignment, boolean isLastLocation, Location startLocation, boolean isReflected, Integer runGuardLocationCoordX, boolean isLastAction, boolean halt) {
//        if (isLastAction && !halt) {
//            assignment += assignment.length() > 0 ? ",\n" : "";
//            assignment += "removeStackCondition()";
//        }
//        Location lastLocationTemp;
//        if (!isLastLocation) {
//            int lastLocationXTemp = lastLocationCoords[0];
//            lastLocationXTemp += isReflected ? -350 : 350;
//            lastLocationTemp = makeLocationWithCoordinates(currentTemplate, null, getCounter(), true, false, lastLocationXTemp, lastLocationCoords[1], null, null);
//            Integer[] assignmentCoords = new Integer[]{(isReflected ? lastLocationXTemp :lastLocationCoords[0]) + 17, lastLocationCoords[1] + 8};
//            makeEdge(currentTemplate, lastLocation, lastLocationTemp, null, null, null, null, stackGuard, new Integer[]{assignmentCoords[0], lastLocationCoords[1] - SIZE_OF_TEXT * 2}, assignment, assignmentCoords);
//            lastLocationCoords[0] = lastLocationXTemp;
//        } else {
//            goBackToStart(currentTemplate, lastLocation, startLocation, lastLocationCoords, stackGuard, assignment, null, runGuardLocationCoordX);
//            lastLocationTemp = lastLocation;
//        }
//        return lastLocationTemp;
//    }
//
//    private Location addVerticalAction(Template currentTemplate, Location lastLocation, int[] lastLocationCoords, String guard, String[] assignmentCollection, Location startLocation, boolean isLastLocation, Integer extraShiftDown, Integer runGuardLocationCoordX, boolean halt) {
//        lastLocationCoords[1] += extraShiftDown == null ? 0 : (extraShiftDown + 1) * SIZE_OF_TEXT;
//        boolean returnedToStart = false;
//        for (int i = 1; i < assignmentCollection.length; i++) {
//            if (!guard.equals("!removeOperator") && i == assignmentCollection.length - 1 && !halt) {
//                assignmentCollection[i] += assignmentCollection[i].length() > 0 ? ",\n" : "";
//                assignmentCollection[i] += "removeStackCondition()";
//            }
//            if (i != assignmentCollection.length - 1 || !isLastLocation || extraShiftDown != null) {
//                int lastLocationYTemp = lastLocationCoords[1] + 110;
//                Location lastLocationTemp = makeLocationWithCoordinates(currentTemplate, null, getCounter(), true, false, lastLocationCoords[0], lastLocationYTemp, null, null);
//                makeEdge(currentTemplate, lastLocation, lastLocationTemp, null, null, null, null, guard, new Integer[]{lastLocationCoords[0] + 17, lastLocationCoords[1] + 8}, assignmentCollection[i], new Integer[]{lastLocationCoords[0] + 17, lastLocationCoords[1] + 8 + SIZE_OF_TEXT});
//
//                lastLocationCoords[1] = lastLocationYTemp;
//                lastLocation = lastLocationTemp;
//            } else {
//                goBackToStart(currentTemplate, lastLocation, startLocation, lastLocationCoords, guard, assignmentCollection[i], null, runGuardLocationCoordX);
//                returnedToStart = true;
//            }
//        }
//        if (assignmentCollection.length > 1 && isLastLocation && !returnedToStart) {
//            goBackToStart(currentTemplate, lastLocation, startLocation, lastLocationCoords, guard, "removeStackRetract()", extraShiftDown, runGuardLocationCoordX);
//        }
//        return lastLocation;
//    }

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

    private StringBuilder getSpaces(int iterate) {
        StringBuilder spaces = new StringBuilder();
        for (int i = 0; i < iterate; i++) {
            spaces.append(" ");
        }
        return spaces;
    }

    private int getArrays(StringBuilder[] productionBuilders, LinkedList<String> array_1, LinkedList<String> array_2, LinkedList<String> array_3, LinkedList<String> array_4) {
        int count = 0;
        if (array_1.size() == count) {
            productionBuilders[0].append("0");
            productionBuilders[1].append("0");
            productionBuilders[2].append("0");
            productionBuilders[3].append("0");

        } else {
            for (int i = 0; i < array_1.size(); i++) {
                String nextIdentifier = array_1.get(i);
                String nextAttribute = array_2.get(i);
                String nextValue = array_3.get(i);
                String nextTemp = array_4.get(i);
                int maxSize = Math.max(Math.max(Math.max(nextIdentifier.length(), nextAttribute.length()), nextValue.length()), nextTemp.length());
                if (i > 0) {
                    for (StringBuilder nextStringBuilder : productionBuilders) {
                        nextStringBuilder.append(", ");
                    }
                }
                count += maxSize + 2;
                productionBuilders[0].append(nextIdentifier).append(getSpaces(maxSize - nextIdentifier.length()));
                productionBuilders[1].append(nextAttribute).append(getSpaces(maxSize - nextAttribute.length()));
                productionBuilders[2].append(nextValue).append(getSpaces(maxSize - nextValue.length()));
                productionBuilders[3].append(nextTemp).append(getSpaces(maxSize - nextTemp.length()));
            }
        }
        return count;
    }

    private void addZeroesAndClose(StringBuilder[] productionBuilders, StringBuilder currentTemplateDeclaration, StringBuilder label) {
        for (int i = 0; i < _maxQuerySize - (conditionProductionIdentifiers.size() + actionProductionIdentifiers.size() + 1); i++) {
            for (StringBuilder nextProductionBuilder : productionBuilders) {
                nextProductionBuilder.append(", 0");
            }
        }

        currentTemplateDeclaration.append(label).append("\n");

        for (StringBuilder nextProductionArray : productionBuilders) {
            currentTemplateDeclaration.append(nextProductionArray).append("};\n");
        }
        currentTemplateDeclaration.append("\n");
    }

    private StringBuilder[] getArrayBuilders() {
        StringBuilder operatorArray             = new StringBuilder("int productionOperatorArray[MAX_GLOBAL_SIZE]    = {");
        StringBuilder attributeArray            = new StringBuilder("int productionAttributeArray[MAX_GLOBAL_SIZE]   = {");
        StringBuilder valueArray                = new StringBuilder("int productionValueArray[MAX_GLOBAL_SIZE]       = {");
        StringBuilder temporaryAndFunctionArray = new StringBuilder("int productionTempAndFuncArray[MAX_GLOBAL_SIZE] = {");
        return new StringBuilder[]{operatorArray, attributeArray, valueArray, temporaryAndFunctionArray};
    }

    private void getNextElement(String nextElement, LinkedList<String> nextArrayElements, int index, String productionArray) {
        if (nextElement.equals("nilAnything")) {
            nextArrayElements.add("productionTempAndFuncArray[" + index + "]");
        } else if (nextElement.startsWith("dummy")) {
            int currentIndex = 0;
            for (String nextTemp : conditionProductionTemp) {
                if (nextTemp.equals(nextElement)) {
                    if (productionArray.equals("productionValueArray")) {
                        nextArrayElements.add("productionTempAndFuncArray[" + currentIndex + "]");
                    } else {
                        nextArrayElements.add("productions[productionIndexTemp].savedTempAndFunction[" + currentIndex + "]");
                    }
                }
                currentIndex++;
            }
        } else {
            nextArrayElements.add( productionArray + "[" + index + "]");
        }
    }

    private int fillListGiverIterators(Iterator<String> values, Iterator<String> identifers, LinkedList<String> nextValueElements, LinkedList<String> nextIdentifierElements, int index) {
        while (values.hasNext() && identifers.hasNext()) {
            getNextElement(values.next(), nextValueElements, index, "productionValueArray");
            getNextElement(identifers.next(), nextIdentifierElements, index, "productionOperatorArray");
            index++;
        }
        return index;
    }

    private void fillWithExtraZeroes(LinkedList<String> nextElements) {
        int currentSize = nextElements.size();
        for (int i = currentSize; i < _maxQuerySize; i++) {
            nextElements.add("0");
        }
    }

    private void getNextProductionArray(LinkedList<String> nextValueElements, LinkedList<String> nextIdentifierElements) {
        Iterator<String> valuesIterator = conditionProductionValues.iterator();
        Iterator<String> identiferIterator = conditionProductionIdentifiers.iterator();
        int index = 0;
        index = fillListGiverIterators(valuesIterator, identiferIterator, nextValueElements, nextIdentifierElements, index) + 1;
        nextValueElements.add("0");
        nextIdentifierElements.add("0");
        valuesIterator = actionProductionValues.iterator();
        identiferIterator = actionProductionFunctions.iterator();
        fillListGiverIterators(valuesIterator, identiferIterator, nextValueElements, nextIdentifierElements, index);
        fillWithExtraZeroes(nextValueElements);
        fillWithExtraZeroes(nextIdentifierElements);
    }

    private String getProductionDeclaration(String productionName) {
        StringBuilder currentTemplateDeclaration = new StringBuilder();
        int currentLatestNum = _latestNum;
        for (String dummyVariable : conditionSideVariablesToTemps.values()) {
            currentTemplateDeclaration.append("const int ");
            currentTemplateDeclaration.append(dummyVariable);
            currentTemplateDeclaration.append(" = ");
            currentTemplateDeclaration.append(currentLatestNum++ + ";\n");
        }

        for (String productionVariable : _productionVariables.values()) {
            currentTemplateDeclaration.append("int ");
            currentTemplateDeclaration.append(productionVariable);
            currentTemplateDeclaration.append(";\n");
        }
        currentTemplateDeclaration.append("\n");

        StringBuilder[] productionArrays = getArrayBuilders();
        String startingSpaces = "                                                   ";

        int extraSpaces = getArrays(productionArrays, conditionProductionIdentifiers, conditionProductionAttributes, conditionProductionValues, conditionProductionTemp);

        for (StringBuilder nextProductionArray : productionArrays) {
            nextProductionArray.append(", 0, ");
        }

        extraSpaces -= 9;
        if (extraSpaces < 0) {
            startingSpaces = startingSpaces.substring(0, startingSpaces.length() + extraSpaces);
        }
        StringBuilder label = new StringBuilder(startingSpaces).append("//Conditions");
        label.append(getSpaces(extraSpaces));
        label.append("//Assignments");

        getArrays(productionArrays, actionProductionIdentifiers, actionProductionAttributes, actionProductionValues, actionProductionFunctions);

        addZeroesAndClose(productionArrays, currentTemplateDeclaration, label);

        if (!_productionToOSupported.get(productionName)) {
            currentTemplateDeclaration.append("\n");
            currentTemplateDeclaration.append(
                    "Production productions[1];\n" +
                    "int productionIndex = 0;\n" +
                    "int productionIndexTemp;\n" +
                    "\n" +
                    "void fillNextProduction() {\n" +
                    "\tint nextArray[MAX_GLOBAL_SIZE] = {");
            LinkedList<String> nextValueElements = new LinkedList<>();
            LinkedList<String> nextIdentifierElements = new LinkedList<>();
            getNextProductionArray(nextValueElements, nextIdentifierElements);

            currentTemplateDeclaration.append(nextValueElements.stream().collect(Collectors.joining(", ")));
            currentTemplateDeclaration.append("};\n");
            currentTemplateDeclaration.append("\tproductions[productionIndex].savedTempAndFunction = nextArray;\n");
            currentTemplateDeclaration.append("\tproductionIndex++;\n");
            currentTemplateDeclaration.append("}\n").append("\n");

            currentTemplateDeclaration.append("void setOperatorArray() {\n");
            currentTemplateDeclaration.append("\tint nextArray [MAX_GLOBAL_SIZE] = {");
            currentTemplateDeclaration.append(nextIdentifierElements.stream().collect(Collectors.joining(", ")));
            currentTemplateDeclaration.append("};\n").append("\toperatorArray = nextArray;\n").append("}\n").append("\n");

            currentTemplateDeclaration.append("void setFunctionArray() {\n");
            StringBuilder newFunctionArray = new StringBuilder("0");
            for (int i = 0; i < conditionProductionIdentifiers.size(); i++) {
                newFunctionArray.append(", 0");
            }
            for (int i = 0; i < actionProductionIdentifiers.size(); i++) {
                newFunctionArray.append(", remove");
            }
            int currentSize = 1 + conditionProductionIdentifiers.size() + actionProductionIdentifiers.size();
            for (int i = currentSize; i < _maxQuerySize; i++) {
                newFunctionArray.append(", 0");
            }
            currentTemplateDeclaration.append("\tint nextArray[MAX_GLOBAL_SIZE] = {");
            currentTemplateDeclaration.append(newFunctionArray.toString()).append("};\n");
            currentTemplateDeclaration.append("\ttempOrFuncArray = nextArray;\n").append("}\n");
        }

        return currentTemplateDeclaration.toString();
    }

    private String getConditionOrAssignment(int tempGlobalSize, int globalIndex, String setBoolean, boolean isRetract, String operatorAssignments) {
        String commaNext = ",\n";
        boolean isCondition = setBoolean.startsWith("checkContains");

        StringBuilder builder = new StringBuilder("TEMP_GLOBAL_SIZE = ").append(tempGlobalSize).append(commaNext);
        builder.append("globalIndex = ").append(globalIndex).append(commaNext);
        builder.append(setBoolean).append(commaNext);
        if (isCondition || !isRetract) {
            if (isRetract) {
                builder.append("setOperatorArray()").append(commaNext);
            } else {
                builder.append("operatorArray = productionOperatorArray").append(commaNext);
            }
            builder.append("attributeArray = productionAttributeArray").append(commaNext);
            builder.append("valueArray = ");
            if (isRetract) {
                builder.append("productions[productionIndexTemp]");
            } else {
                builder.append("productionValueArray");
            }
            builder.append(commaNext).append("tempOrFuncArray = productionTempAndFuncArray");
            if (isCondition) {
                builder.append(commaNext).append("doesContainArray = doesContainDefault").append(commaNext);
                builder.append("updateDoesContainTrueAndFalse()");
            }
        } else {
            builder.append("setFunctionArray()");
        }
        if (operatorAssignments.length() > 0) {
            builder.append(commaNext).append(operatorAssignments);
        }
        return builder.toString();
    }

//    private LinkedList[] getInverseConditions() {
//        LinkedList<String> inverseIdentifiers = new LinkedList<>();
//        LinkedList<String> inverseAttributes = new LinkedList<>();
//        LinkedList<String> inverseValues = new LinkedList<>();
//        LinkedList<String> inverseFunctions = new LinkedList<>();
//        LinkedList[] inverseGuards = new LinkedList[4];
//        inverseGuards[0] = inverseIdentifiers;
//        inverseGuards[1] = inverseAttributes;
//        inverseGuards[2] = inverseValues;
//        inverseGuards[3] = inverseFunctions;
//        Iterator<String> identifiers = conditionProductionIdentifiers.iterator();
//        Iterator<String> attributes = conditionProductionAttributes.iterator();
//        Iterator<String> values = conditionProductionValues.iterator();
//        Iterator<String> tempOrFunction = conditionProductionTemp.iterator();
//        int continueIndex = -1;
//        for (int i = 0; i < conditionProductionIdentifiers.size(); i++) {
//            String nextValue = values.next();
//            if (!nextValue.equals("nilAnything")) {
//                continueIndex = i;
//                break;
//            }
//            inverseIdentifiers.add(identifiers.next());
//            inverseAttributes.add(attributes.next());
//            inverseValues.add(tempOrFunction.next());
//            inverseFunctions.add("0");
//        }
//        inverseValues.add("CONTINUE_" + continueIndex);
//        if (inverseIdentifiers.size() == 0) {
//            return null;
//        }
//        return inverseGuards;
//    }

    @Override
    public Node visitSoar_production(SoarParser.Soar_productionContext ctx) {
        _productionVariables = new HashMap<>();
        _retractOperatorIndexes = new HashSet<>();
        conditionSideVariablesToTemps = new HashMap<>();
        conditionProductionIdentifiers = new LinkedList<>();
        conditionProductionAttributes = new LinkedList<>();
        conditionProductionValues = new LinkedList<>();
        conditionProductionTemp = new LinkedList<>();
        actionProductionIdentifiers = new LinkedList<>();
        actionProductionAttributes = new LinkedList<>();
        actionProductionValues = new LinkedList<>();
        actionProductionFunctions = new LinkedList<>();
        _latestIndex = 0;

        String startStateID = getCounter();

        Template currentTemplate = makeTemplate(SoarTranslator.simplifiedString(ctx.sym_constant().getText()));
        _templateNames.add(getText(currentTemplate, "name"));

        Location startLocation = makeLocationWithCoordinates(currentTemplate, "Start", startStateID, true, true, -152, 0, -200, -32);

        ctx.condition_side().accept(this);
//        if (conditionSide.getProperty("inverseGuards") != null) {
//            inverseGuard = getText(conditionSide, "inverseGuards");
//            _learnInverseAssignments = true;
//        } else {
//            inverseGuard = null;
//            _learnInverseAssignments = false;
//        }

        Node actionSide = ctx.action_side().accept(this);
        String operatorAssignments = getText(actionSide, "operatorAssignments");

//        String inverseAssignment;
//        if (actionSide.getProperty("inverseAssignments") != null) {
//            inverseAssignment = getText(actionSide, "inverseAssignments");
//        } else {StringBuilder operatorArray =  new StringBuilder("int productionConditionOperatorArray[MAX_GLOBAL_SIZE] =   {");
//            inverseAssignment = null;
//        }

//        String[] guardCollection = guard.split("::");
//        for (String individualGuard : guardCollection) {
//            if (individualGuard.contains("addOp = finalOp")) {
//                Property guardProperty = startRunEdge.setProperty("guard", "finalOp != 0");
//                guardProperty.setProperty("x", 40);
//                guardProperty.setProperty("y", 0);
//                startRunEdge.getProperty("assignment").setProperty("y", SIZE_OF_TEXT);
//                break;
//            }
//        }




        boolean halt = getText(actionSide, "hasHalt").equals("yes");
        boolean needsRetraction = !_productionToOSupported.get(ctx.sym_constant().getText());

        int[] lastLocationCoords = new int[2];
        setLastLocationCoords(lastLocationCoords);
        Location lastLocation;
        String nextAssignment;

        if (needsRetraction && !halt) {
            lastLocation = addHorizontalCondition(currentTemplate, startLocation, lastLocationCoords, "Run_Retract", "Run_Rule?", "isRetracting", "addToStackRetract(" + _templateIndex + "),\nproductionIndexTemp = 0", true);
            Location runRetractLocation = lastLocation;

            goBackToStart(currentTemplate, lastLocation, startLocation, lastLocationCoords, "productionIndexTemp == productionIndex", "productionIndexTemp = 0", true);

            nextAssignment = getConditionOrAssignment(conditionProductionIdentifiers.size(), 0, "checkContains = true", true, "");
            lastLocation = addHorizontalCondition(currentTemplate, lastLocation, lastLocationCoords, null, null, "stackRetract[stackRetractIndex] == " + _templateIndex, nextAssignment, true);

            goBackToStart(currentTemplate, lastLocation, runRetractLocation, lastLocationCoords, "!checkContains &&\ndoesContainArray == doesContainTrue", "productionIndexTemp++", true);

            nextAssignment = getConditionOrAssignment(actionProductionIdentifiers.size(), conditionProductionIdentifiers.size() + 2, "addOperator = true", true, "");
            lastLocation = addHorizontalCondition(currentTemplate, lastLocation, lastLocationCoords, "Run_Retract_Assignments", null, "!checkContains &&\ndoesContainArray != doesContainTrue", nextAssignment, true);

            goBackToStart(currentTemplate, lastLocation, runRetractLocation, lastLocationCoords, "!addOperator", "productionIndex--", true);
        }

        setLastLocationCoords(lastLocationCoords);

        lastLocation = addHorizontalCondition(currentTemplate, startLocation, lastLocationCoords, "Run_Guard", "Run_Rule?", "!isRetracting", "addToStackCondition(" + _templateIndex + ")", false);

        goBackToStart(currentTemplate, lastLocation, startLocation, lastLocationCoords, null, "halt", false);

        nextAssignment = getConditionOrAssignment(conditionProductionIdentifiers.size(), 0, "checkContains = true", false, "");
        lastLocation = addHorizontalCondition(currentTemplate, lastLocation, lastLocationCoords, null, null, "stackCondition[stackConditionIndex] == " + _templateIndex + " &&\n!addOperator", nextAssignment, false);

        goBackToStart(currentTemplate, lastLocation, startLocation, lastLocationCoords, "!checkContains &&\ndoesContainArray != doesContainTrue", "removeStackCondition()", false);

        lastLocation = addHorizontalCondition(currentTemplate, lastLocation, lastLocationCoords, "Run_Assignment", "Reset!", "!checkContains &&\ndoesContainArray == doesContainTrue", "removeStackCondition(),\naddToStackAction(" + _templateIndex + ")", false);

        nextAssignment = getConditionOrAssignment(actionProductionIdentifiers.size(), conditionProductionIdentifiers.size() + 2, "addOperator = true", false, operatorAssignments);
        lastLocation = addHorizontalCondition(currentTemplate, lastLocation, lastLocationCoords, null, null, "stackConditionIndex == -1 &&\nstackAction[stackActionIndex] ==" +  _templateIndex, nextAssignment, false);

        nextAssignment = "removeStackAction()";
        if (needsRetraction) {
            nextAssignment = nextAssignment + ",\nfillNextProduction()";
//            lastLocation = addHorizontalCondition(currentTemplate, lastLocation, lastLocationCoords, "Run_Retract", "Run_Rule?", null, "addToStackRetract(" + _templateIndex + ")");

//            nextAssignment = getConditionOrAssignment(conditionProductionIdentifiers.size(), 0, "checkContains = true");
//            lastLocation = addHorizontalCondition(currentTemplate, lastLocation, lastLocationCoords, null, null, "stackCondition[stackConditionIndex] == " + _templateIndex + " &&\n!addOperator", nextAssignment);

        }
//        else {
//            goBackToStart(currentTemplate, lastLocation, startLocation, lastLocationCoords, "!addOperator", "removeStackAction()", null, null);
//        }
        goBackToStart(currentTemplate, lastLocation, startLocation, lastLocationCoords, "!addOperator", nextAssignment, false);


        //        Location lastLocation = addHorizontalCondition(currentTemplate, runGuardLocation, startLocation, lastLocationCoords, "stackCondition[stackConditionIndex] == " + _templateIndex + " &&\n!addOperator",guardCollection[0], "removeStackCondition()", xTextLocation, guardCollection.length <= 1);
//
//        lastLocation = addVerticalConditions(currentTemplate, lastLocation, lastLocationCoords, guardCollection, startLocation, "removeStackCondition()", xTextLocation, false);
//
//        lastLocation = moveToNextStage(currentTemplate, lastLocation, lastLocationCoords, "Run_Assignment", null, "doesContain == 1", null);
//
//        String[] assignmentCollection = operatorAssignments.split("::");
//
//        lastLocation = addHorizontalAction(currentTemplate, lastLocation, lastLocationCoords, null, assignmentCollection[0] + (assignmentCollection[0].length() > 0 ? ",\n" : "") + "productionFired = true" + (assignmentCollection[0].length() == 0 ? ",\nisRetracting = false" : ""), assignmentCollection.length <= 1 && inverseGuard == null, startLocation, false, runGuardCoords[0], assignmentCollection.length <= 1, halt);
//
//        lastLocation = addVerticalAction(currentTemplate, lastLocation, lastLocationCoords, "!addOperator", assignmentCollection, startLocation, inverseGuard == null, null, runGuardCoords[0], halt);
//
//        if (!halt){
//            makeEdgeWithNails(currentTemplate, runGuardLocation, startLocation, null, null, "Halt?", new Integer[]{runGuardCoords[0] + SIZE_OF_TEXT, -100}, null, null, null, null, new Integer[]{runGuardCoords[0], -110, -152, -110});
//            if (inverseGuard != null) {
//                String[] inverseGuardCollection = inverseGuard.split(" :: ");
//                Location lastAssignmentLocation = lastLocation;
//                int lastAssignmentLocationXCoord = lastLocationCoords[0];
//                lastLocation = moveToNextStage(currentTemplate, lastLocation, lastLocationCoords, "Run_Retract", "Run_Rule?",null, "addToStackRetract(" + _templateIndex + ")");
//                makeEdgeWithNails(currentTemplate, lastLocation, startLocation, null, null, "Halt?", new Integer[]{lastLocationCoords[0] - 50, lastLocationCoords[1] - 100}, null, null, null, null, new Integer[]{lastLocationCoords[0], lastLocationCoords[1] - 120, -152, lastLocationCoords[1] - 120});
//                xTextLocation = lastLocationCoords[0] + 17;
//                int extraShiftForRetraction = assignmentCollection.length <= 1 ? 0 : (inverseGuardCollection.length - assignmentCollection.length + 1) * 110;
//                int[] runRetractionAssignmentsCoords = new int[]{lastLocationCoords[0], lastLocationCoords[1] + inverseGuardCollection.length * 110 + extraShiftForRetraction};
//                Location runRetractionAssignmentsLocation = makeLocationWithCoordinates(currentTemplate, "Run_Retraction_Assignments", getCounter(), true, false, runRetractionAssignmentsCoords[0], runRetractionAssignmentsCoords[1], runRetractionAssignmentsCoords[0] - 220, runRetractionAssignmentsCoords[1] - 30);
//                lastLocation = addHorizontalCondition(currentTemplate, lastLocation, runRetractionAssignmentsLocation, lastLocationCoords, "!addOperator &&\nstackRetractIndex > -1 &&\nstackRetract[stackRetractIndex] == " + _templateIndex + " &&\nisRetracting &&\nstackConditionIndex == -1", inverseGuardCollection[0], null, xTextLocation, inverseGuardCollection.length <= 1);
//                lastLocation = addVerticalConditions(currentTemplate, lastLocation, lastLocationCoords, inverseGuardCollection, runRetractionAssignmentsLocation, null, xTextLocation, extraShiftForRetraction > 0);
//                makeEdgeWithNails(currentTemplate, lastLocation, lastAssignmentLocation, null, null, null, null, "doesContain == 1", new Integer[]{lastLocationCoords[0] + 75, lastLocationCoords[1] + 85}, "removeStackRetract()", new Integer[]{lastLocationCoords[0] + 75, lastLocationCoords[1] + 120}, new Integer[]{lastLocationCoords[0] + 51, lastLocationCoords[1] + 110, lastLocationCoords[0] + 400, lastLocationCoords[1] + 110, lastLocationCoords[0] + 400, -110, lastAssignmentLocationXCoord, -110});
//                lastLocation = runRetractionAssignmentsLocation;
//                lastLocationCoords = runRetractionAssignmentsCoords;
//                if (inverseAssignment != null) {
//                    String[] inverseAssignmentCollection = inverseAssignment.split(" :: ");
//                    String stackGuard;
//                    if (_retractOperatorIndexes.size() > 0) {
//                        String guardForRetractOperatorIndexes = _retractOperatorIndexes.stream().map(e -> "finalOp == " + e).collect(Collectors.joining(" ||\n"));
//                        currentTemplateDeclaration.append("bool resetFinalOp = true;\n");
//                        makeEdgeWithNails(currentTemplate, lastLocation, lastLocation, null, null, null, null, guardForRetractOperatorIndexes, new Integer[]{lastLocationCoords[0] + SIZE_OF_TEXT, lastLocationCoords[1] + SIZE_OF_TEXT}, "finalOp = 0,\nresetFinalOp = false", new Integer[]{lastLocationCoords[0] + SIZE_OF_TEXT, lastLocationCoords[1] + (SIZE_OF_TEXT*(1+_retractOperatorIndexes.size()))}, new Integer[]{lastLocationCoords[0], lastLocationCoords[1] + (SIZE_OF_TEXT*(1+_retractOperatorIndexes.size()*2))});
//                        stackGuard = "!resetFinalOp";
//                        extraShiftForRetraction = SIZE_OF_TEXT;
//                    } else {
//                        stackGuard = null;
//                        extraShiftForRetraction = 0;
//                    }
//                    StringBuilder tempInverseAssignment = new StringBuilder(inverseAssignmentCollection[0]);
//                    if (stackGuard != null) {
//                        if (tempInverseAssignment.length() > 0) {
//                            tempInverseAssignment.append(",\n");
//                        }
//                        tempInverseAssignment.append("resetFinalOp = true");
//                    }
//                    lastLocation = addHorizontalAction(currentTemplate, lastLocation, lastLocationCoords, stackGuard, tempInverseAssignment.toString(), inverseAssignmentCollection.length <= 1, startLocation, true, runGuardCoords[0], inverseAssignmentCollection.length <= 1, false);
//                    lastLocationCoords[1] += extraShiftForRetraction;
//                    lastLocation = addVerticalAction(currentTemplate, lastLocation, lastLocationCoords, "!removeOperator", inverseAssignmentCollection, startLocation, true, getNumLines(inverseAssignmentCollection[0], ","), runGuardCoords[0], false);
//                }
//            }
//        } else {
//            goBackToStart(currentTemplate, lastLocation, startLocation, lastLocationCoords, "isRetracting == false", "halt = true,\nclearStacks()", null, runGuardCoords[0]);
//        }

        currentTemplate.setProperty("declaration", getProductionDeclaration(ctx.sym_constant().getText()));

        _templateIndex++;
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

        innerConditionVisit(ctx.attr_value_tests(), localVariableDictionary, idTest, localActualVariables);

        return null;
    }

    private String determineInverseAssignment(String regularAssignment) {
        switch (regularAssignment) {
            case "==":
                return "!=";
            case "!=":
                return "==";
            case ">":
                return "<=";
            case "<":
                return ">=";
            default:
                return "==";
        }
    }

    private void addOperatorColumn(String dummyVariable) {
        conditionProductionIdentifiers.add("finalOp");
        conditionProductionAttributes.add("operator");
        conditionProductionValues.add(dummyVariable);
        conditionProductionTemp.add("0");
    }

    private void innerConditionVisit(List<SoarParser.Attr_value_testsContext> attrValueTestsCtxs, Map<String, String> localVariableDictionary, String idTest, ProductionVariables localActualVariables) {
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
                }

                String attrPath = attributeCtx.attr_test(attributeCtx.attr_test().size() - 1).getText();
                conditionProductionIdentifiers.add(attrPath.equals("operator") ? "finalOp" : lastVariable);
                conditionProductionAttributes.add(attrPath);

                String value;
                StringBuilder inverseValue = new StringBuilder("tempValue");

//                if (attrPath.contains("operator")) {
//                    inverseStateVariableComparisons = null;
//                }

                if (attributeCtx.getText().startsWith("-^")) {
                    conditionProductionValues.add("EMPTY");
                    conditionProductionTemp.add("0");
//                    if (inverseStateVariableComparisons != null) {
//                        inverseStateVariableComparisons.add(value.toString());
//                    }
                } else {
                    int numberOfValues = attributeCtx.value_test().size();

                    if (numberOfValues == 1) {
                        Node relationAndRightTerm = attributeCtx.value_test(0).accept(this);

                        if (relationAndRightTerm.getProperty("rel") != null) {

                            String relation = getText(relationAndRightTerm, "rel");
                            String inverseRelation = determineInverseAssignment(relation);

                            String rightTerm;

                            if (relation.equals("=")) {
                                relation = "==";
                                inverseRelation = "!=";
                            }

                            if (relationAndRightTerm.getProperty("var") != null) {
                                rightTerm = getText(relationAndRightTerm, "var");
                                if (conditionSideVariablesToTemps.get(rightTerm) == null) {
                                    value = "nilAnything";
                                    String withoutTempVariable = SoarTranslator.simplifiedString(localVariableDictionary.get(rightTerm));
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
//                                if (inverseStateVariableComparisons != null) {
//                                    inverseValue.append(" = " + newTempVariable + ",\n");
//                                }
                            } else {
                                rightTerm = getText(relationAndRightTerm, "const");
                                value = SoarTranslator.simplifiedString(rightTerm);
//                                inverseValue.append(addToValue);
                            }

                            if (rightTerm.equals("true") && relation.equals("==")) {
//                                stateVariableComparisons.add(SoarTranslator.simplifiedString(leftTerm));
                            } else if (rightTerm.equals("false") && relation.equals("==")) {
//                                stateVariableComparisons.add("!" + SoarTranslator.simplifiedString(leftTerm));
                            } else if (value.length() > 0) {
                                if (value.equals("nilAnything")) {
                                    conditionProductionValues.add(_latestIndex, value);
                                    conditionProductionIdentifiers.add(_latestIndex, conditionProductionIdentifiers.removeLast());
                                    conditionProductionAttributes.add(_latestIndex, conditionProductionAttributes.removeLast());
                                    conditionProductionTemp.add(_latestIndex, conditionProductionTemp.removeLast());
                                    _latestIndex++;
                                } else {
                                    conditionProductionValues.add(value);
                                    conditionProductionTemp.add("0");
                                }
//                                if (inverseStateVariableComparisons != null) {
//                                    inverseStateVariableComparisons.add(inverseValue.toString());
//                                }
                            }
                        } else if (relationAndRightTerm.getProperty("disjunction") != null) {
                            //FIXFIXFIX
                            String[] disjunctionCollection = getText(relationAndRightTerm, "disjunction").split(",");
                            String simplifiedLeftTerm = SoarTranslator.simplifiedString("REPLACEME");
                            StringBuilder disjunctionRelations = new StringBuilder();
                            disjunctionRelations.append("(");
                            for (int i = 0; i < disjunctionCollection.length; i++) {
                                if (i != 0) {
                                    disjunctionRelations.append(" || ");
                                }
                                disjunctionRelations.append(simplifiedLeftTerm);
                                disjunctionRelations.append(" == ");
                                disjunctionRelations.append(SoarTranslator.simplifiedString(disjunctionCollection[i]));
                            }
                            disjunctionRelations.append(")");
                            if (!disjunctionRelations.equals("()")) {
                                String disjunctionString = disjunctionRelations.toString();
//                                stateVariableComparisons.add(disjunctionString);
//                                inverseStateVariableComparisons.add("!" + disjunctionString);
                            }
                        }
                    } else {

                        // use "path_to_var[index] = constant" pattern
                    }
                }
            }
        }

//        if (inverseStateVariableComparisons != null) {
//            returnArray[1] = inverseStateVariableComparisons
//                    .stream()
//                    .filter(c -> c != null && !c.equals(""))
//                    .collect(Collectors.joining(" :: "));
//            returnArray[3] = "" + inverseStateVariableComparisons.size();
//        } else {
//            returnArray[1] = null;
//            returnArray[3] = "0";
//        }
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

        innerConditionVisit(ctx.attr_value_tests(), localVariableDictionary, idTest, localActualVariables);

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
        StringBuilder disjunctionCollection = new StringBuilder();
        for (int i = 0; i < ctx.constant().size(); i++) {
            if (i != 0) {
                disjunctionCollection.append(",");
            }
            disjunctionCollection.append(getText(ctx.constant(i).accept(this), "const"));
        }
        return textAsNode("disjunction", disjunctionCollection.toString());
    }

    @Override
    public Node visitRelational_test(SoarParser.Relational_testContext ctx) {
        String relation = "==";

        if (ctx.relation() != null) {
            relation = ctx.relation().getText();

            if (relation.equals("<>")) {
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
        String result = SoarTranslator.simplifiedString(ctx.getText());

        if (ctx.Print_string() != null) {
            result = LITERAL_STRING_PREFIX + ctx.Print_string().getText().split("|")[1];
        }
        return textAsNode("const", result);
    }

    @Override
    public Node visitAction_side(SoarParser.Action_sideContext ctx) {
        StringBuilder operatorAssignments = new StringBuilder();
//        StringBuilder inverseAssignments = new StringBuilder();
//        int numInverseAssignments = 0;
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
//            if (actionNode.getProperty("inverseAssignments") != null) {
//                inverseAssignments.append(getText(actionNode, "inverseAssignments"));
//                inverseAssignments.append(",\n");
//            }
//            numInverseAssignments += Integer.parseInt(getText(actionNode, "numInverseAssignments"));
        }

        Node returnNode = textAsNode("operatorAssignments", operatorAssignments.toString());

//        if (inverseAssignments.length() > 0) {
//            if (inverseAssignments.length() >= 2 && inverseAssignments.charAt(inverseAssignments.length() - 2) == ',') {
//                inverseAssignments.delete(inverseAssignments.length() - 2, inverseAssignments.length());
//            }
//            returnNode.setProperty("inverseAssignments", inverseAssignments.toString());
//        }

//        returnNode.setProperty("numInverseAssignments", "" + numInverseAssignments);

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
//        if (stateAssignmentsAndInverseAssignments[1].length() != 0) {
//            returnNode.setProperty("inverseAssignments", stateAssignmentsAndInverseAssignments[1]);
//        }
//        returnNode.setProperty("numInverseAssignments", stateAssignmentsAndInverseAssignments[2]);
        return returnNode;
    }

    private String innerVisitAction(List<SoarParser.Attr_value_makeContext> ctxs, String variableName, Map<String, String> localVariablePathsWithID) {
        LinkedList<String> operatorCollection = new LinkedList<>();
//        LinkedList<String> inverseOperatorCollection = new LinkedList<>();
//        HashSet<String> attributeCollection = new HashSet<>();
        String variable = conditionSideVariablesToTemps.get(variableName);
        if (variable == null) {
            String pathWithId = localVariablePathsWithID.get(variableName);
            int index = Integer.parseInt(pathWithId.substring(pathWithId.lastIndexOf("_") + 1));
            if (index == -1) {
                variable = "_" + pathWithId.substring(0, pathWithId.lastIndexOf("_"));
            } else {
                variable = pathWithId;
            }
        }
        for (SoarParser.Attr_value_makeContext attrCtx : ctxs) {
            String attribute = attrCtx.variable_or_sym_constant(attrCtx.variable_or_sym_constant().size() - 1).getText();
//            if (_learnInverseAssignments && !leftSide.startsWith("state_operator")) {
//                attributeCollection.add(attribute);
//            }

            for (SoarParser.Value_makeContext value_makeContext : attrCtx.value_make()) {
                actionProductionIdentifiers.add(variable);
                actionProductionAttributes.add(attribute);

                Node rightSideElement = value_makeContext.accept(this);
                String rightSide = determineAssignment(rightSideElement, localVariablePathsWithID);

                if (rightSide != null) {
                        operatorCollection.add(rightSide);
//                        getInverseOperator(rightSideElement, inverseOperatorCollection);
                }
            }
        }

//        StringBuilder inverseOperatorCollectionStringBuilder = new StringBuilder(inverseOperatorCollection.stream().collect(Collectors.joining(" :: ")));
//        String inverseOperatorCollectionString = inverseOperatorCollectionStringBuilder.toString();
//        if (!inverseOperatorCollectionString.equals("")) {
//            String stringID;
//            int indexOfID = inverseOperatorCollectionString.indexOf("addOp");
//            if (indexOfID == -1) {
//                indexOfID = inverseOperatorCollectionString.indexOf("operators[");
//                indexOfID += 10;
//                stringID = inverseOperatorCollectionString.substring(indexOfID, inverseOperatorCollectionString.indexOf("]", indexOfID));
//            } else {
//                indexOfID += 8;
//                stringID = inverseOperatorCollectionString.substring(indexOfID, inverseOperatorCollectionString.indexOf(",", indexOfID));
//            }
//            Integer intID = Integer.parseInt(stringID) + 1;
//            _operatorIDToInverseActions.put(intID, inverseOperatorCollectionString);
//        }

        String returnInverseStateAssignments = "";
        int numInverseAssignments = 0;
//        if (_learnInverseAssignments) {
//            final String setRemoveBoolean = "removeOperator = true";
//            StringBuilder inverseStateAssignmentsCollection = new StringBuilder(attributeCollection.stream().map(e -> operator + e + setRemoveBoolean).collect(Collectors.joining(" :: ")));
//            inverseStateAssignmentsCollection.append(inverseOperatorCollectionStringBuilder.length() > 0 && inverseStateAssignmentsCollection.length() > 0 ? " :: " : "");
//            inverseStateAssignmentsCollection.append(inverseOperatorCollectionStringBuilder);
//            returnInverseStateAssignments = inverseStateAssignmentsCollection.toString();
//
//            numInverseAssignments += attributeCollection.size();
//            numInverseAssignments += inverseOperatorCollection.size();
//        } else {
//            returnInverseStateAssignments = "";
//        }

        return operatorCollection.stream().collect(Collectors.joining(",\n"));
    }

    private String operatorBaseString(String index, String parameter) {
        StringBuilder returnString = new StringBuilder();
        returnString.append("operators[");
        returnString.append(index);
        returnString.append("].operator.");
        returnString.append(parameter);
        return returnString.toString();
    }

//    private void addToInverseAssignments(LinkedList<String> inverseAssignmentsCollection, SymbolTree operator, String operatorID, String thisOperatorIndex) {
//        LinkedList<SymbolTree> attributesAndPreferences = operator.DFSForAttributeValues(true);
//        for (SymbolTree attributeOrPreference : attributesAndPreferences) {
//            StringBuilder inverseAssignments = new StringBuilder();
//            if (attributeOrPreference.name.startsWith("is")) {
//                if (attributeOrPreference.isLeaf()) {
//                    inverseAssignments.append("operators[" + thisOperatorIndex + "].operator." + attributeOrPreference.name + " = false,\nremoveOperator = false");
//                } else {
//                    String thatOperatorIndex = getIndexFromID(attributeOrPreference.getChildren().get(0).name);
//                    if (attributeOrPreference.name.equals("isBetterTo")) {
//                        inverseAssignments.append(functionCallWithTwoIDs("removeBetterFrom", thisOperatorIndex, thatOperatorIndex));
//                    } else if (attributeOrPreference.name.equals("isUnaryOrBinaryIndifferentTo")) {
//                        inverseAssignments.append(functionCallWithTwoIDs("removeBinaryIndifferentFrom", thisOperatorIndex, thatOperatorIndex));
//                    }
//                }
//            } else {
//                inverseAssignments.append("addOp = " + operatorID + ",\n");
//                int attributeIndex = Integer.parseInt(attributeOrPreference.name.substring(1));
////                inverseAssignments.append("tempAttribute = state_operator_" + SoarTranslator.simplifiedString(_operatorsAttributesAndValues.get(attributeIndex).get(0)) + ",\n");
//                inverseAssignments.append("removeOperator = true");
//            }
//            inverseAssignmentsCollection.add(inverseAssignments.toString());
//        }
//    }

    private SymbolTree findOperator(int index) {
//        for (SymbolTree production : _operators) {
//            for (SymbolTree operator : production.getChildren()) {
//                if (operator.getIDFromTree() == index) {
//                    return operator;
//                }
//            }
//        }
        return null;
    }

//    private void getInverseOperator(Node rightSideElement, LinkedList<String> inverseAssignmentsCollection) {
//        if (rightSideElement.getProperty("var") != null) {
//            SymbolTree operator = null;/*_currentOperators.getSubtreeNoError(getText(rightSideElement, "var"));*/
//            if (operator != null && operator.getSubtreeNoError("create") != null) {
//                String operatorID = getIDFromProperty(operator.name);
//                String thisOperatorIndex = "" + (Integer.parseInt(operatorID) - 1);
//                _retractOperatorIndexes.add(operatorID);
//
//                addToInverseAssignments(inverseAssignmentsCollection, operator, operatorID, thisOperatorIndex);
//                SymbolTree nestedRemoveTree = operator.getSubtreeNoError("nestedRemoveOperator");
//                if (nestedRemoveTree != null) {
//                    Integer inverseOperatorID = Integer.parseInt(nestedRemoveTree.getChildren().get(0).name);
//                    if (_operatorIDToInverseActions.get(inverseOperatorID) != null) {
//                        String[] additionalInverseAssignments = _operatorIDToInverseActions.get(inverseOperatorID).split(" :: ");
//                        for (String nextInverseAssignment : additionalInverseAssignments) {
//                            inverseAssignmentsCollection.add(nextInverseAssignment);
//                        }
//                    } else {
//                        String inverseOperatorIDString = inverseOperatorID + "";
//                        String inverseOperatorIndex = (inverseOperatorID - 1) + "";
//                        SymbolTree otherOperator = findOperator(inverseOperatorID);
//                        LinkedList<String> otherOperatorInverseAssignments = new LinkedList<>();
//                        addToInverseAssignments(otherOperatorInverseAssignments, otherOperator, inverseOperatorIDString, inverseOperatorIndex);
//                        _operatorIDToInverseActions.put(inverseOperatorID, otherOperatorInverseAssignments.stream().collect(Collectors.joining(" :: ")));
//                        for (String inverseAssignment : otherOperatorInverseAssignments) {
//                            inverseAssignmentsCollection.add(inverseAssignment);
//                        }
//                    }
//                }
//
//            }
//        }
//    }
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
            if (rightSideElement.getProperty("const") != null) {
                actionProductionValues.add(getText(rightSideElement, "const"));
            } else if (rightSideElement.getProperty("expr") != null) {
                actionProductionValues.add(getText(rightSideElement, "expr"));
            } else if (rightSideElement.getProperty("pref") != null) {
                if (getText(rightSideElement, "pref").equals("remove")) {
                    String rightSideVar = getText(rightSideElement, "var");
                    String variable = conditionSideVariablesToTemps.get(rightSideVar);
                    if (variable == null) {
                        variable = getVariable(rightSideVar, localVariablePathsWithID);
                    }
                    actionProductionValues.add(variable);
                    actionProductionFunctions.add("remove");
                    shiftLists();
                } else {
                    actionProductionValues.add(getVariable(getText(rightSideElement, "var"), localVariablePathsWithID));

                    String operatorIndex = getIndexFromID(getText(rightSideElement, "var"), localVariablePathsWithID);

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
                        if (binaryPref.equals("isBetterTo")) {
                            rightSide = functionCallWithTwoIDs("addBetterTo", operatorIndex, thatValueID);
                        } else if (binaryPref.equals("isUnaryOrBinaryIndifferentTo")) {
                            rightSide = functionCallWithTwoIDs("addBinaryIndifferentTo", operatorIndex, thatValueID);
                        }
                    }
                }
            } else if (rightSideElement.getProperty("var") != null) {
                String rightSideVar = getText(rightSideElement, "var");
                String variable = conditionSideVariablesToTemps.get(rightSideVar);
                if (variable == null) {
                    variable = getVariable(rightSideVar, localVariablePathsWithID);
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
        return function + "(" + index1 + "," + index2 + ")";
    }


    @Override
    public Node visitPrint(SoarParser.PrintContext ctx) {
        return null;
    }

    private String getVariableOrTemp(SoarParser.ValueContext ctx, Map<String, String> localDictionary) {
        StringBuilder variableOrTemp = new StringBuilder();
        if (ctx.variable() == null) {
            variableOrTemp.append(ctx.constant().getText());
        } else {
            variableOrTemp.append(localDictionary.get(ctx.getText()));
            if (_productionVariables.get(variableOrTemp.toString() + "_temp") != null) {
                variableOrTemp.append("_temp");
            }
        }
        return variableOrTemp.toString();
    }

    @Override
    public Node visitFunc_call(SoarParser.Func_callContext ctx) {
        String productionName = ((SoarParser.Soar_productionContext) ctx.parent.parent.parent.parent.parent.parent).sym_constant().getText();
        Map<String, String> localDictionary = _variableDictionary.get(productionName);

        SoarParser.ValueContext leftContext = ctx.value(0);
        SoarParser.ValueContext rightContext = ctx.value(1);

        String leftSide = getVariableOrTemp(leftContext, localDictionary);

        String result;

        if (ctx.func_name().getText().equals("-") && rightContext == null) {
            result = "0 - " + SoarTranslator.simplifiedString(leftSide);
        } else {
            String rightSide = getVariableOrTemp(rightContext, localDictionary);
            String funcName = ctx.func_name().getText();

            if ("+-/*".contains(ctx.func_name().getText())) {
                result = SoarTranslator.simplifiedString(leftSide + " " + funcName + " " + rightSide);
            } else {
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

    @Override
    public Node visitValue_make(SoarParser.Value_makeContext ctx) {
        Node value = ctx.value().accept(this);

        if (((SoarParser.Attr_value_makeContext) ctx.parent).variable_or_sym_constant().get(0).getText().equals("operator")) {
            if (ctx.value_pref_binary_value() != null) {
                Node valuePrefBinaryValue = ctx.value_pref_binary_value().accept(this);

                try {
                    Integer.parseInt(getText(valuePrefBinaryValue, "secondValue"));
                } catch (NumberFormatException e) {
                    String replaceVariable = getText(valuePrefBinaryValue, "secondValue");
                    valuePrefBinaryValue.setProperty("secondValue", getIDFromProperty(getText(value, "var")));
                    value.setProperty("var", replaceVariable);
                }

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
            preferences.append(getText(value_pref_clauseContext.accept(this), "unaryPref") + ",");
        }
        return preferences.toString();
    }

    private String getIDFromProperty(String variableName) {
        SymbolTree otherOperator = null;/*_currentOperators.getSubtree(variableName);*/
        String otherOperatorID = otherOperator.getSubtree("create").getSubtree("id").getChildren().get(0).name;
        return otherOperatorID;
    }

    private String getIndexFromID(String variableName, Map<String, String> localVariablePathsWithID) {
        String pathWithID = localVariablePathsWithID.get(variableName);
        int indexOfLast_ = pathWithID.lastIndexOf("_");
        return (Integer.parseInt(pathWithID.substring(indexOfLast_ + 1)) - 1) + "";
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
                String otherOperatorID = getIDFromProperty(getText(secondValue, "var"));
                secondValueProperty = otherOperatorID;
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
        return getAttributeValueTemplate();
    }

    private String getTinyDeclaration(String[] operator, String[] attribute, String[] value) {
        StringBuilder currentTemplateDeclaration = new StringBuilder();
        actionProductionIdentifiers = new LinkedList<>();
        actionProductionAttributes = new LinkedList<>();
        actionProductionValues = new LinkedList<>();
        actionProductionFunctions = new LinkedList<>();
        actionProductionIdentifiers.add(operator[0]);
        actionProductionAttributes.add(attribute[0]);
        actionProductionValues.add(value[0]);
        actionProductionFunctions.add("0");
        if (operator.length == 2) {
            actionProductionIdentifiers.add("0");
            actionProductionIdentifiers.add(operator[1]);
            actionProductionAttributes.add("0");
            actionProductionAttributes.add(attribute[1]);
            for (int i = 0; i < 2; i++) {
                actionProductionValues.add("0");
                actionProductionFunctions.add("0");
            }
        }
        StringBuilder[] schedulerBuilders = getArrayBuilders();
        StringBuilder label = new StringBuilder("                                                            //Conditions");
        getArrays(schedulerBuilders, actionProductionIdentifiers, actionProductionAttributes, actionProductionValues, actionProductionFunctions);
        int start = operator.length == 1 ? 1 : 3;
        for (int i = start; i < _maxQuerySize; i++) {
            for (StringBuilder nextScheduleBuilder : schedulerBuilders) {
                nextScheduleBuilder.append(", 0");
            }
        }
        currentTemplateDeclaration.append(label).append("\n");
        for (StringBuilder nextScheduleBuilder : schedulerBuilders) {
            currentTemplateDeclaration.append(nextScheduleBuilder).append("};\n");
        }
        return currentTemplateDeclaration.toString();
    }

    private Element getRunScheduler() {
        String startId = getCounter();
        String proposalID = getCounter();
        String readyDecisionID = getCounter();
        String decisionID = getCounter();
        String readyApplicationID = getCounter();
        String applicationID = getCounter();
        String setSuperstateNilId = getCounter();
        String backToProposalId = getCounter();


        Template runScheduler = makeTemplate("Scheduler");

        runScheduler.setProperty("declaration", getTinyDeclaration(new String[]{"_state", "finalOp"}, new String[]{"superstate", "operator"}, new String[]{"nil"}));

        Location startLocation = makeLocationWithCoordinates(runScheduler, "Start", startId, true, true, -816, -102, -826, -136);
        Location proposalLocation = makeLocationWithCoordinates(runScheduler, "Proposal", proposalID, true, false, -323, -102, -391, -136);
        Location readyDecisionLocation = makeLocationWithCoordinates(runScheduler, "Ready_Decision", readyDecisionID, true, false, -119, -102, -238, -136);
        Location decisionLocation = makeLocationWithCoordinates(runScheduler, "Decision", decisionID, true, false, 136, -102, 102, -136);
        Location readyApplicationLocation = makeLocationWithCoordinates(runScheduler, "Ready_Application", readyApplicationID, true, false, 416, -102, 340, -136);
        Location applicationLocation = makeLocationWithCoordinates(runScheduler, "Application", applicationID, true, false, 620, -102, 578, -136);
        Location backToProposalLocation = makeLocationWithCoordinates(runScheduler, "Back_To_Proposal", backToProposalId, true, false, 782, -102, 790, -136);
        Location setSuperstateNilLocation = makeLocationWithCoordinates(runScheduler, "Set_Superstate_Nil", setSuperstateNilId, true, false, -569, -102, -663, -136);

        makeEdgeWithNails(runScheduler, readyDecisionLocation, proposalLocation, null, null, "Halt?", new Integer[]{-110, -416}, null, null, null, null, new Integer[]{-119, -425, -323, -425});
        makeEdgeWithNails(runScheduler, backToProposalLocation, proposalLocation, null, null, "Halt?", new Integer[]{-110, -416}, null, null, null, null, new Integer[]{782, -425, -323, -425});
        makeEdgeWithNails(runScheduler, backToProposalLocation, backToProposalLocation, null, null, "Run_Rule!", new Integer[]{841, 68}, "stackConditionIndex == -1 &&\nstackRetractIndex == -1 &&\n!addOperator &&\nproductionFired", new Integer[]{841, 85}, "productionFired = false", new Integer[]{841, 153}, new Integer[]{823, 85, 926, 85});
        makeEdgeWithNails(runScheduler, readyDecisionLocation, readyDecisionLocation, null, null, "Run_Rule!", new Integer[]{-153, 153}, "stackConditionIndex == -1 &&\nstackRetractIndex == -1 &&\n!addOperator &&\nproductionFired", new Integer[]{-161, 178}, "productionFired = false", new Integer[]{-161, 246}, new Integer[]{-161, 170, -76, 170, -119, -85});
        String nextAssignment = getConditionOrAssignment(1, 2, "removeOperator = true", false, "");
        makeEdgeWithNails(runScheduler, backToProposalLocation, proposalLocation, null, null, null, null, "stackConditionIndex == -1 &&\nstackRetractIndex == -1 &&\n!addOperator &&\n!productionFired", new Integer[]{68, -399}, "clearFill(required),\nclearFill(acceptable),\nclearFill(best),\nisRetracting = false,\n" + nextAssignment, new Integer[]{68, -314}, new Integer[]{782, -323, -323, -323});
        makeEdge(runScheduler, applicationLocation, backToProposalLocation, null, null, "Run_Rule!", new Integer[]{663, -127}, null, null, "isRetracting = true", new Integer[]{637, -93});
        makeEdge(runScheduler, startLocation, setSuperstateNilLocation, null, null, null, null, null, null, "addOperator = true", new Integer[]{-799, -93});
        makeEdge(runScheduler, setSuperstateNilLocation, proposalLocation, null, null, null, null, "!addOperator",  new Integer[]{-518, -127}, "initialize(operators)", new Integer[]{-527, -93});
        makeEdge(runScheduler, readyApplicationLocation, applicationLocation, null, null, "Continue_Run?", new Integer[]{467, -127}, null, null, null, null);
        makeEdge(runScheduler, decisionLocation, readyApplicationLocation, null, null, "Require_Test!", new Integer[]{178, -127}, null, null, null, null);
        makeEdge(runScheduler, readyDecisionLocation, decisionLocation, null, null, null, null, "stackConditionIndex == -1 &&\nstackRetractIndex == -1 &&\n!addOperator &&\n!productionFired", new Integer[]{-102, -93}, "fillOthers(),\nisRetracting = false", new Integer[]{-102, -25});
        makeEdge(runScheduler, proposalLocation, readyDecisionLocation, null, null, "Run_Rule!", new Integer[]{-306, -85}, "!halt", new Integer[]{-306, -68}, "isRetracting = true,\nproductionFired = false", new Integer[]{-306, -51});

        return runScheduler;
    }

    private String[] makeAttributeValueTemplates() {
        StringBuilder instantiationsCollection = new StringBuilder();
        StringBuilder systemProcesses = new StringBuilder(" ");
        for (UppaalAttributeValueTriad UAT : _AVCollection) {
            if (systemProcesses.length() > 1) {
                systemProcesses.append(", ");
            }
            systemProcesses.append(UAT.getName());
            instantiationsCollection.append(UAT.getName());
            instantiationsCollection.append(" = ");
            instantiationsCollection.append("Attribute_Value(");
            instantiationsCollection.append(UAT.getNumValues() + ", " + UAT.getOperatorIndex() + ", " + UAT.getAttributeIndex());
            instantiationsCollection.append(");\n");
        }

        if (systemProcesses.length() > 1) {
            systemProcesses.append(", ");
        }
        systemProcesses.append("AV_Final_Operator");
        instantiationsCollection.append("AV_Final_Operator");
        instantiationsCollection.append(" = ");
        instantiationsCollection.append("Attribute_Value(");
        instantiationsCollection.append(1 + ", finalOp, operator");
        instantiationsCollection.append(");\n");

        return new String[]{instantiationsCollection.toString(), systemProcesses.toString()};
    }
    private Element getAttributeValueTemplate() {
        String startId = getCounter();
        String middleAddLocationID = getCounter();

        Template attributeValueTemplate = makeTemplate("Attribute_Value");
        attributeValueTemplate.setProperty("parameter", "const int NUM_VALUES, const int ATTRIBUTE_INDEX, const int OPERATOR_ID");
        attributeValueTemplate.setProperty("declaration",
                "int values[NUM_VALUES];\n" +
                "int valuesIndex = 0;\n" +
                "int containsIndex = -1;\n" +
                "int lookAhead = 0;" +
                "\n" +
                "void resetLookAhead() {\n" +
                "\tlookAhead = 0;\n" +
                "}\n" +
                "\n" +
                "void doValuesContain() {\n" +
                "\tif (valueArray[globalIndex] == nilAnything) {\n" +
                "\t\tif (lookAhead < valuesIndex) {\n" +
                "\t\t\tint i;\n" +
                "\t\t\tfor (i = globalIndex + 1; i < TEMP_GLOBAL_SIZE; i++) {\n" +
                "\t\t\t\tif (operatorArray[i] == tempOrFuncArray[globalIndex]) {\n" +
                "\t\t\t\t\toperatorArray[i] = values[lookAhead];\n" +
                "\t\t\t\t}\n" +
                "\t\t\t\tif (valueArray[i] == tempOrFuncArray[globalIndex]) {\n" +
                "\t\t\t\t\tvalueArray[i] = values[lookAhead];\n" +
                "\t\t\t\t}\n" +
                "\t\t\t}\n" +
                "\t\t\ttempOrFuncArray[globalIndex] = values[lookAhead];\n" +
                "\t\t\tdoesContainArray[globalIndex] = 1;\n" +
                "\t\t\tglobalIndex++;\n" +
                "\t\t\tif (globalIndex >= TEMP_GLOBAL_SIZE) {\n" +
                "\t\t\t\tcheckContains = false;\n" +
                "\t\t\t}\n" +
                "\t\t\tlookAhead++;\n" +
                "\t\t} else {\n" +
                "\t\t\tdoesContainArray[globalIndex] = -1;\n" +
                "\t\t\tlookAhead = 0;\n" +
                "\t\t\tglobalIndex--;\n" +
                "\t\t\twhile (globalIndex != -1 && valueArray[globalIndex] != nilAnything) {\n" +
                "\t\t\t\tdoesContainArray[globalIndex] = -1;\n" +
                "\t\t\t\tglobalIndex--;\n" +
                "\t\t\t}\n" +
                "\t\t\tif (globalIndex == -1) {\n" +
                "\t\t\t\tcheckContains = false;\n" +
                "\t\t\t}\n" +
                "\t\t}\n" +
                "\t} else {\n" +
                "\t\tint contains = -1;\n" +
                "\t\tint i;\n" +
                "\t\tfor (i = 0; i < valuesIndex; i++) {\n" +
                "\t\t\tif (values[i] == valueArray[globalIndex]) {\n" +
                "\t\t\t\tcontains = 1;\n" +
                "\t\t\t\ti = valuesIndex;\n" +
                "\t\t\t}\n" +
                "\t\t}\n" +
                "\t\tif (contains == 1) {\n" +
                "\t\t\tdoesContainArray[globalIndex] = 1;\n" +
                "\t\t\tglobalIndex++;\n" +
                "\t\t\tif (globalIndex >= TEMP_GLOBAL_SIZE) {\n" +
                "\t\t\t\tcheckContains = false;\n" +
                "\t\t\t}\n" +
                "\t\t} else {\n" +
                "\t\t\tdoesContainArray[globalIndex] = -1;\n" +
                "\t\t\tglobalIndex--;\n" +
                "\t\t\twhile (globalIndex != -1 && valueArray[globalIndex] != nilAnything) {\n" +
                "\t\t\t\tdoesContainArray[globalIndex] = -1;\n" +
                "\t\t\t\tglobalIndex--;\n" +
                "\t\t\t}\n" +
                "\t\t\tif (globalIndex == -1) {\n" +
                "\t\t\t\tcheckContains = false;\n" +
                "\t\t\t}\n" +
                "\t\t}\n" +
                "\t}\n" +
                "}\n" +
                "\n" +
                "void addValue() {\n" +
                "\tif (containsIndex == -1) {\n" +
                "\t\tvalues[valuesIndex] = valueArray[globalIndex];\n" +
                "\t\tvaluesIndex++;\n" +
                "\t}\n" +
                "\tglobalIndex++;\n" +
                "\tif (globalIndex == TEMP_GLOBAL_SIZE) {\n" +
                "\t\taddOperator = false;\n" +
                "\t}\n" +
                "}\n" +
                "\n" +
                "int getIndexOfValue() {\n" +
                "\tint i = 0;\n" +
                "\tfor (i = 0; i < valuesIndex; i++) {\n" +
                "\t\tif (values[i] == valueArray[globalIndex]) {\n" +
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
                "\tglobalIndex++;\n" +
                "\tif (globalIndex == TEMP_GLOBAL_SIZE) {\n" +
                "\t\taddOperator = false;\n" +
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
                "\tglobalIndex++;\n" +
                "\tif (globalIndex == TEMP_GLOBAL_SIZE) {\n" +
                "\t\taddOperator = false;\n" +
                "\t}\n" +
                "}");

        Location startLocation = makeLocationWithCoordinates(attributeValueTemplate, "Start", startId, true, true, -739, -195, -780, -229);
        Location middleAddLocation = makeLocationWithCoordinates(attributeValueTemplate, null, middleAddLocationID, true, false, -229, -195, null, null);

        makeEdgeWithNails(attributeValueTemplate, middleAddLocation, startLocation, null, null, null, null, "tempOrFuncArray[globalIndex] == remove", new Integer[]{-425, -331}, "removeSpecificValue()", new Integer[]{-425, -314}, new Integer[]{-535, -340});
        makeEdgeWithNails(attributeValueTemplate, middleAddLocation, startLocation, null, null, null, null, "tempOrFuncArray[globalIndex] == 0", new Integer[]{-382, -127}, "addValue()", new Integer[]{-382, -110}, new Integer[]{-535, -68});
        makeEdgeWithNails(attributeValueTemplate, startLocation, startLocation, null, null, null, null, "removeOperator &&\noperatorArray[globalIndex] == OPERATOR_ID &&\nattributeArray[globalIndex] == ATTRIBUTE_INDEX", new Integer[]{-790, -85}, "removeValue()", new Integer[]{-790, -34}, new Integer[]{-739, -144, -688, -93, -790, -93, -739, -144});
        makeEdgeWithNails(attributeValueTemplate, startLocation, startLocation, null, null, null, null, "checkContains &&\noperatorArray[globalIndex] == OPERATOR_ID &&\nattributeArray[globalIndex] == ATTRIBUTE_INDEX", new Integer[]{-1156, -204}, "doValuesContain()", new Integer[]{-1156, -153}, new Integer[]{-739, -144, -807, -144, -807, -195});
        makeEdge(attributeValueTemplate, startLocation, middleAddLocation, null, null, null, null, "addOperator &&\noperatorArray[globalIndex] == OPERATOR_ID &&\nattributeArray[globalIndex] == ATTRIBUTE_INDEX", new Integer[]{-654, -255}, "containsIndex =getIndexOfValue()", new Integer[]{-654, -187});
        makeEdgeWithNails(attributeValueTemplate, startLocation, startLocation, null, null, "Reset?", new Integer[]{-867, -272}, null, null, "resetLookAhead()", new Integer[]{-867, -255}, new Integer[]{-739, -240 - 2*SIZE_OF_TEXT});

        String[] instantiationsAndSystem = makeAttributeValueTemplates();
        attributeValueTemplate.setProperty("instantiations", instantiationsAndSystem[0]);
        attributeValueTemplate.setProperty("system", instantiationsAndSystem[1]);

        return attributeValueTemplate;
    }

    private String getOperatorIfs() {
        StringBuilder ifStatements = new StringBuilder();
        for (String possibleOperator : _uppaalOperatorCollection) {
            if (possibleOperator.contains("operator")) {
                if (ifStatements.length() > 0) {
                    ifStatements.append(" else ");
                } else {
                    ifStatements.append("\t");
                }
                ifStatements.append("if (finalOperatorIndex == ").append(possibleOperator).append(") {\n");
                ifStatements.append("\t\treturn ").append(possibleOperator).append(";\n").append("\t}");
            }
        }
        ifStatements.append("\n").append("\treturn -1;\n");
        return ifStatements.toString();
    }

    private Element getOperatorPreferences() {
        Template operatorPreferencesTemplate = makeTemplate("preferenceResolutionTemplate");
        operatorPreferencesTemplate.setProperty("declaration",
                "bool requiredAndProhibited;\n" +
                        "int currentOp;\n" +
                        "int finalOperatorIndex;\n" +
                        "int getOperator() {\n" +
                        getOperatorIfs() +
                        "}\n" +
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
                        "}" + getTinyDeclaration(new String[]{"finalOp"}, new String[]{"operator"}, new String[]{"0"})
        );
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
        String nextAssignment = "productionValueArray[0] = getOperator(),\n" + getConditionOrAssignment(1, 0, "addOperator = true", false, "");
        makeEdge(operatorPreferencesTemplate, done, noName4, null, null, null, null, null, null, nextAssignment, new Integer[]{-3280, -504});
        makeEdgeWithNails(operatorPreferencesTemplate, noName4, start, null, null, "Continue_Run!", new Integer[]{-3918, -1113}, "!addOperator", new Integer[]{-3918, -1097}, null, null, new Integer[]{-3808, -1536});

        return null;
    }
}
