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
    private Map<Integer, Map<String, Map<String, HashSet<Integer>>>> _productionToTempToModifiedIndexes = new HashMap<>();
    private Map<Integer, Map<String, Integer>> _productionToDummyToIndex = new HashMap<>();
    private int _maxTemps = 0;

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
                "bool halt = false;\n" +
                "chan Continue_Run;\n" +
                "chan Require_Test;\n" +
                "bool isRetracting;\n" +
                "bool addOperator;\n" +
                "bool removeOperator;\n" +
                "bool productionFired;\n" +
                "bool checkMatches;\n" +
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
                "int attributeTempArray[MAX_GLOBAL_SIZE];\n" +
                "int lookAheadArray[MAX_GLOBAL_SIZE];\n" +
                "int defaultLookAheadArray[MAX_GLOBAL_SIZE];\n" +
                "int globalIndex = 0;\n" +
                "bool checkContains;\n" +
                "int currentNumAttributes;\n");
        int totalAttributeSize = 0;
        for (LinkedList<String> nextNumAttributes : _variableToAttributes.values()) {
            totalAttributeSize += nextNumAttributes.size();
        }
        vars.append("const int TOTAL_NUM_ATTRIBUTES = " +
                totalAttributeSize + ";\n" +
                "int nestedCheckArray[TOTAL_NUM_ATTRIBUTES];\n" +
                "int nestedCheckIndex = 0;\n");

        vars.append("const int MAX_DUMMY_SIZE = ").append(_maxTemps).append(";\n");
        vars.append("int dummyArray[MAX_DUMMY_SIZE];\n");
        vars.append("int dummyArrayDefault[MAX_DUMMY_SIZE];\n");


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
                "\tfor (i = 0; i < MAX_GLOBAL_SIZE; i++) {\n" +
                "\t\tdefaultLookAheadArray[i] = 0;\n" +
                "\t}\n" +
                "\tfor (i = 0; i < MAX_DUMMY_SIZE; i++) {\n" +
                "\t\tdummyArrayDefault[i] = 0;\n" +
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
                "}" +
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
                "void updateDoesContainTrueAndFalse() {\n" +
                "\tint i;\n" +
                "\tfor (i = 0; i < TEMP_GLOBAL_SIZE; i++) {\n" +
                "\t\tdoesContainTrue[i] = 1;\n" +
                "\t} \n" +
                "\tfor (i = TEMP_GLOBAL_SIZE; i < MAX_GLOBAL_SIZE; i++) {\n" +
                "\t\tdoesContainTrue[i] = 0;\n" +
                "\t}\n" +
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

        vars.append("typedef struct {\n" +
//                "\tint savedTempAndFunction[MAX_GLOBAL_SIZE];\n" +
//                "\tint savedAttributeTemp[MAX_GLOBAL_SIZE];\n" +
                "\tint savedDummyArray[MAX_DUMMY_SIZE];\n" +
                "} Production;\n" +
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

        vars.append("int getOperatorId(int operator) {\n");

        newSwitch = new StringBuilder();
        for (String nextOperator : actualOperatorCollection) {
            newSwitch.append("\t");
            if (newSwitch.length() > 1) {
                newSwitch.append("} else ");
            }
            int operatorIndex = Integer.parseInt(nextOperator.substring(nextOperator.lastIndexOf('_') + 1)) - 1;
            newSwitch.append("if (operator == ").append(nextOperator).append(") {\n\t\treturn ").append(operatorIndex).append(";\n");
        }
        if (newSwitch.length() > 0) {
            newSwitch.append("\t} else {\n\t\treturn -1;\n").append("\t}\n");
        } else {
            newSwitch.append("\treturn -1;\n");
        }
        newSwitch.append("}\n").append("\n");
        vars.append(newSwitch);

        if (noneButSwitch != null) {
            vars.append(noneButSwitch);
        }

        vars.append("bool checkDummyArraysEqual(int array1[MAX_DUMMY_SIZE], int array2[MAX_DUMMY_SIZE]) {\n");
        vars.append("\tint i;\n");
        vars.append("\tfor (i = 0; i < MAX_DUMMY_SIZE; i++) {\n");
        vars.append("\t\tif (array1[i] != array2[i]) {\n");
        vars.append("\t\t\treturn false;\n");
        vars.append("\t\t}\n");
        vars.append("\t}\n");
        vars.append("\treturn true;\n");
        vars.append("}\n").append("\n");

        vars.append("bool checkGlobalArraysEqual(int array1[MAX_GLOBAL_SIZE], int array2[MAX_GLOBAL_SIZE]) {\n");
        vars.append("\tint i;\n");
        vars.append("\tfor (i = 0; i < MAX_GLOBAL_SIZE; i++) {\n");
        vars.append("\t\tif (array1[i] != array2[i]) {\n");
        vars.append("\t\t\treturn false;\n");
        vars.append("\t\t}\n");
        vars.append("\t}\n");
        vars.append("\treturn true;\n");
        vars.append("}\n").append("\n");

        vars.append("void checkNextCombo() {\n");
        vars.append("\tdoesContainArray[globalIndex] = -1;\n");
        vars.append("\tglobalIndex--;\n");
        vars.append("\twhile (globalIndex != -1 && valueArray[globalIndex] != nilAnything && attributeArray[globalIndex] > noneBut_1) {\n");
        vars.append("\t\tdoesContainArray[globalIndex] = -1;\n");
        vars.append("\t\tglobalIndex--;\n");
        vars.append("\t}\n");
        vars.append("}\n").append("\n");

        newSwitch = new StringBuilder();
        vars.append("void replaceSpecificValues(int dummyValue, int replaceValue) {\n");
        boolean first;
        for (Map.Entry<Integer, Map<String, Map<String, HashSet<Integer>>>> productionIndexToModifiedIndexesEntry : _productionToTempToModifiedIndexes.entrySet()) {
            if (newSwitch.length() > 0) {
                newSwitch.append("\t else ");
            } else {
                newSwitch.append("\t");
            }

            newSwitch.append("if ((stackConditionIndex > -1 && stackCondition[stackConditionIndex] == " + productionIndexToModifiedIndexesEntry.getKey() + ") || (stackActionIndex > -1 && stackAction[stackActionIndex] == " + productionIndexToModifiedIndexesEntry.getKey() + ") || (stackRetractIndex > -1 && stackRetract[stackRetractIndex] =="  + productionIndexToModifiedIndexesEntry.getKey() + ")) {\n");
            first = true;
            for (Map.Entry<String, Map<String, HashSet<Integer>>> variableToModifiedIndexesEntry : productionIndexToModifiedIndexesEntry.getValue().entrySet()) {
                if (!first) {
                    newSwitch.append(" else ");
                } else {
                    first = false;
                    newSwitch.append("\t\t");
                }
                int dummyIndex = _productionToDummyToIndex.get(productionIndexToModifiedIndexesEntry.getKey()).get(variableToModifiedIndexesEntry.getKey());
                newSwitch.append("if (dummyValue == " + dummyIndex + ") {\n");
                for (Map.Entry<String, HashSet<Integer>> arrayNameToModifiedIndexes : variableToModifiedIndexesEntry.getValue().entrySet()) {
                    if (arrayNameToModifiedIndexes.getKey().equals("extraForDummy")) {
                        newSwitch.append("\t\t\tdummyArray[").append(dummyIndex - _latestNum).append("] = replaceValue;\n");
                    } else {
                        for (Integer nextIndex : arrayNameToModifiedIndexes.getValue()) {
                            newSwitch.append("\t\t\t").append(arrayNameToModifiedIndexes.getKey()).append("[").append(nextIndex).append("] = replaceValue;\n");
                        }
                    }
                }
                newSwitch.append("\t\t}");
            }
            newSwitch.append("\n").append("\t}");
        }
        vars.append(newSwitch.toString()).append("\n}\n");


        ourDocument.setProperty("declaration", vars.toString());
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

    private Location addHorizontalLocation(Template currentTemplate, Location lastLocation, int[] lastLocationCoords, String name, String synchronization, String stackGuard, String assignment, boolean mirrored) {
        int xTextLocation = lastLocationCoords[0] + (mirrored ? -370 : 0) + 25;
        int xTempCoords = lastLocationCoords[0] + (mirrored ? -370 : 370);
        Location lastLocationTemp = makeLocationWithCoordinates(currentTemplate, name, getCounter(), true, false, xTempCoords, 0, getNameLocation(name, xTempCoords), lastLocationCoords[1] - 32);

        makeEdge(currentTemplate, lastLocation, lastLocationTemp, null, null, synchronization, new Integer[]{xTextLocation, lastLocationCoords[1] - (getNumLines(stackGuard, " &&") + 1)*SIZE_OF_TEXT}, stackGuard, new Integer[]{xTextLocation, lastLocationCoords[1] - getNumLines(stackGuard, " &&")*SIZE_OF_TEXT}, assignment, new Integer[]{xTextLocation, lastLocationCoords[1] + 8});
        lastLocationCoords[0] = xTempCoords;
        return lastLocationTemp;
    }

    private void goBackToProvidedLocation(Template currentTemplate, Location lastLocation, Location startLocation, int[] lastLocationCoords, String guard, String assignment, boolean mirrored) {
        Integer[] nails = new Integer[]{lastLocationCoords[0], lastLocationCoords[1] - 110, startLocation.getX(), -110};
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
        int textLocationX = lastLocationCoords[0] + (mirrored ? 0 : - 370);
        Integer[] guardLocation = new Integer[]{textLocationX,  assignmentSpace - SIZE_OF_TEXT * getNumLines(guard, " &&")};
        Integer[] assignmentLocation = new Integer[]{textLocationX, assignmentSpace};
        makeEdgeWithNails(currentTemplate, lastLocation, startLocation, null, null, synchronization, new Integer[]{textLocationX, guardLocation[1] - SIZE_OF_TEXT}, guard, guardLocation, assignment, assignmentLocation, nails);
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
            productionBuilders[4].append("0");

        } else {
            for (int i = 0; i < array_1.size(); i++) {
                String nextIdentifier = array_1.get(i);
                String nextAttribute = array_2.get(i);
                String nextValue = array_3.get(i);
                String nextTemp = array_4.get(i);
                String nextAttributeTemp = attributeTemps.getFirst();
                attributeTemps.addLast(attributeTemps.removeFirst());
                int maxSize = Math.max(Math.max(Math.max(Math.max(nextIdentifier.length(), nextAttribute.length()), nextValue.length()), nextTemp.length()), nextAttributeTemp.length());
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
                productionBuilders[4].append(nextAttributeTemp).append(getSpaces(maxSize - nextAttributeTemp.length()));
            }
        }
        return count;
    }

    private void addZeroesAndClose(StringBuilder[] productionBuilders, StringBuilder currentTemplateDeclaration, StringBuilder label) {
        int iterateSize = _maxQuerySize - (conditionProductionIdentifiers.size() + actionProductionIdentifiers.size() + 1);
        if (actionProductionIdentifiers.size() == 0) {
            iterateSize--;
        }
        for (int i = 0; i < iterateSize; i++) {
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
        StringBuilder operatorArray                 = new StringBuilder("int productionOperatorArray[MAX_GLOBAL_SIZE]    = {");
        StringBuilder attributeArray                = new StringBuilder("int productionAttributeArray[MAX_GLOBAL_SIZE]   = {");
        StringBuilder valueArray                    = new StringBuilder("int productionValueArray[MAX_GLOBAL_SIZE]       = {");
        StringBuilder temporaryAndFunctionArray     = new StringBuilder("int productionTempAndFuncArray[MAX_GLOBAL_SIZE] = {");
        StringBuilder temporaryAttributeArray       = new StringBuilder("int productionAttributeTemp[MAX_GLOBAL_SIZE]    = {");
        return new StringBuilder[]{operatorArray, attributeArray, valueArray, temporaryAndFunctionArray, temporaryAttributeArray};
    }

    private void fillWithExtraZeroes(LinkedList<String> nextElements) {
        int currentSize = nextElements.size();
        for (int i = currentSize; i < _maxQuerySize; i++) {
            nextElements.add("0");
        }
    }

    private void getNextElement(LinkedList<String> nextIdentifierElements, LinkedList<String> nextAttributeElements, LinkedList<String> nextValueElements, String nextIdentifier, String nextAttribute, String nextValue, String nextValueTemp, String nextAttributeTemp, Map<String, Integer> dummyToIndex, int index) {
        if (nextIdentifier.startsWith("dummy")) {
            nextIdentifierElements.add("operatorArray[" + index + "] = productions[index].savedDummyArray[" + (dummyToIndex.get(nextIdentifier) - _latestNum) + "]");
        }
        if (nextAttribute.startsWith("dummy")) {
            nextAttributeElements.add("attributeArray[" + index + "] = productions[index].savedDummyArray[" + (dummyToIndex.get(nextAttribute) - _latestNum) + "]");
        } else if (nextAttribute.startsWith("noneBut") ) {
            nextAttributeElements.add("attributeArray[" + index + "] = productions[index].savedDummyArray[" + (dummyToIndex.get(nextAttributeTemp) - _latestNum) + "]");
        }
        if (nextValue.startsWith("dummy")) {
            nextValueElements.add("valueArray[" + index + "] = productions[index].savedDummyArray[" + (dummyToIndex.get(nextValue) - _latestNum) + "]");
        } else if (nextValue.equals("nilAnything")) {
            nextValueElements.add("valueArray[" + index + "] = productions[index].savedDummyArray[" + (dummyToIndex.get(nextValueTemp) - _latestNum) + "]");
        }
    }

    private void getNextProductionArray(LinkedList<String> nextIdentifierElements, LinkedList<String> nextAttributeElements, LinkedList<String> nextValueElements, Map<String, Integer> dummyToIndex) {
        for (int i = 0; i < conditionProductionIdentifiers.size(); i++) {
            getNextElement(nextIdentifierElements, nextAttributeElements, nextValueElements, conditionProductionIdentifiers.get(i), conditionProductionAttributes.get(i), conditionProductionValues.get(i), conditionProductionTemp.get(i), attributeTemps.get(i), dummyToIndex, i);
        }
//        nextIdentifierElements.add("0");
//        nextAttributeElements.add("0");
//        nextValueElements.add("0");
        int buffer = conditionProductionIdentifiers.size();
        for (int i = 0; i < actionProductionIdentifiers.size(); i++) {
            getNextElement(nextIdentifierElements, nextAttributeElements, nextValueElements, actionProductionIdentifiers.get(i), actionProductionAttributes.get(i), actionProductionValues.get(i), actionProductionFunctions.get(i), attributeTemps.get(i + buffer), dummyToIndex, i + buffer + 1);
        }
//        fillWithExtraZeroes(nextIdentifierElements);
//        fillWithExtraZeroes(nextAttributeElements);
//        fillWithExtraZeroes(nextValueElements);
    }

    private String getProductionDeclaration(String productionName, Set<String> operatorIndexes, Map<String, Integer> dummyToIndex) {
        StringBuilder currentTemplateDeclaration = new StringBuilder();
        int currentLatestNum = _latestNum;
        for (String dummyVariable : conditionSideVariablesToTemps.values()) {
            addConstantToGlobals(currentTemplateDeclaration, dummyVariable, currentLatestNum);
            dummyToIndex.put(dummyVariable, currentLatestNum);
            currentLatestNum++;
        }
        for (String dummyVariable : attributesToTemps.values()) {
            addConstantToGlobals(currentTemplateDeclaration, dummyVariable, currentLatestNum);
            dummyToIndex.put(dummyVariable, currentLatestNum);
            currentLatestNum++;
        }
        _maxTemps = Math.max(_maxTemps, currentLatestNum - _latestNum);

        //        for (String productionVariable : _productionVariables.values()) {
//            currentTemplateDeclaration.append("int ");
//            currentTemplateDeclaration.append(productionVariable);
//            currentTemplateDeclaration.append(";\n");
//        }
//        currentTemplateDeclaration.append("\n");

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
        currentTemplateDeclaration.append("\n");

        currentTemplateDeclaration.append(
                "Production productions[1];\n" +
                "int productionIndex = 0;\n" +
                "int productionIndexTemp;\n" +
                "\n" +
                "void fillNextProduction() {\n"/* +
                "\tint nextArray[MAX_GLOBAL_SIZE] = {"*/);
        LinkedList<String> nextIdentifierElements = new LinkedList<>();
        LinkedList<String> nextAttributeElements = new LinkedList<>();
        LinkedList<String> nextValueElements = new LinkedList<>();
        getNextProductionArray(nextIdentifierElements, nextAttributeElements, nextValueElements, dummyToIndex);

//        String nextArray = nextValueElements.stream().collect(Collectors.joining(", "));
//        String nextArray2 = nextAttributeElements.stream().collect(Collectors.joining(", "));
//        currentTemplateDeclaration.append(nextArray);
//        currentTemplateDeclaration.append("};\n");
//        currentTemplateDeclaration.append("\tint nextArray2[MAX_GLOBAL_SIZE] = {");
//        currentTemplateDeclaration.append(nextArray2);
//        currentTemplateDeclaration.append("};\n");
//        currentTemplateDeclaration.append("\tproductions[productionIndex].savedTempAndFunction = nextArray;\n");
//        currentTemplateDeclaration.append("\tproductions[productionIndex].savedAttributeTemp = nextArray2;\n");
        currentTemplateDeclaration.append("\tproductions[productionIndex].savedDummyArray = dummyArray;\n");
        currentTemplateDeclaration.append("\tproductionIndex++;\n");
        currentTemplateDeclaration.append("}\n").append("\n");

//        currentTemplateDeclaration.append("void setOperatorArray() {\n");
//        currentTemplateDeclaration.append("\tint nextArray [MAX_GLOBAL_SIZE] = {");
//        currentTemplateDeclaration.append(nextIdentifierElements.stream().collect(Collectors.joining(", ")));
//        currentTemplateDeclaration.append("};\n").append("\toperatorArray = nextArray;\n").append("}\n").append("\n");

        currentTemplateDeclaration.append("void setArraysToSavedValues(int index) {\n");
        currentTemplateDeclaration.append("\toperatorArray = productionOperatorArray;\n");
        for (String operatorSet : nextIdentifierElements) {
            currentTemplateDeclaration.append("\t").append(operatorSet).append(";\n");
        }
        currentTemplateDeclaration.append("\tattributeArray = productionAttributeArray;\n");
        for (String attributeSet : nextAttributeElements) {
            currentTemplateDeclaration.append("\t").append(attributeSet).append(";\n");
        }
        currentTemplateDeclaration.append("\tvalueArray = productionValueArray;\n");
        for (String valueSet : nextValueElements) {
            currentTemplateDeclaration.append("\t").append(valueSet).append(";\n");
        }
        currentTemplateDeclaration.append("}\n").append("\n");

        currentTemplateDeclaration.append("void checkProductionsContain() {\n");
        currentTemplateDeclaration.append("\tif (checkGlobalArraysEqual(doesContainArray, doesContainTrue)) {\n");
//        currentTemplateDeclaration.append("\t\tint checkArray1[MAX_GLOBAL_SIZE] = {").append(nextArray).append("};\n");
//        currentTemplateDeclaration.append("\t\tint checkArray2[MAX_GLOBAL_SIZE] = {").append(nextArray2).append("};\n");
//        currentTemplateDeclaration.append("\t\tint i;\n");
//        currentTemplateDeclaration.append("\t\tbool productionsContain = false;\n");
//        currentTemplateDeclaration.append("\t\tfor (i = 0; i < productionIndex; i++) {\n");
//        currentTemplateDeclaration.append("\t\t\tif (checkArraysEqual(checkArray1, productions[i].savedTempAndFunction) || checkArraysEqual(checkArray2, productions[i].savedAttributeTemp)) {\n");
//        currentTemplateDeclaration.append("\t\t\t\ti  = productionIndex;\n");
//        currentTemplateDeclaration.append("\t\t\t\tglobalIndex = TEMP_GLOBAL_SIZE - 1;\n");
//        currentTemplateDeclaration.append("\t\t\t\tcheckNextCombo();\n");
//        currentTemplateDeclaration.append("\t\t\t\tproductionsContain = true;\n");
//        currentTemplateDeclaration.append("\t\t\t}\n");
//        currentTemplateDeclaration.append("\t\t}\n");
        currentTemplateDeclaration.append("\t\tint i;\n");
        currentTemplateDeclaration.append("\t\tbool productionsContain = false;\n");
        currentTemplateDeclaration.append("\t\tfor (i = 0; i < productionIndex; i++) {\n");
        currentTemplateDeclaration.append("\t\t\tif (checkDummyArraysEqual(dummyArray, productions[i].savedDummyArray)) {\n");
        currentTemplateDeclaration.append("\t\t\t\ti  = productionIndex;\n");
        currentTemplateDeclaration.append("\t\t\t\tglobalIndex = TEMP_GLOBAL_SIZE - 1;\n");
        currentTemplateDeclaration.append("\t\t\t\tcheckNextCombo();\n");
        currentTemplateDeclaration.append("\t\t\t\tproductionsContain = true;\n");
        currentTemplateDeclaration.append("\t\t\t}\n");
        currentTemplateDeclaration.append("\t\t}\n");
        currentTemplateDeclaration.append("\t\tif (productionsContain) {\n");
        currentTemplateDeclaration.append("\t\t\tcheckContains = true;\n");
        currentTemplateDeclaration.append("\t\t} else {\n");
        currentTemplateDeclaration.append("\t\t\tcheckMatches = false;\n");
        if (_productionToOSupported.get(productionName)) {
            currentTemplateDeclaration.append("\t\t\tproductionIndex = 0;\n");
        }
        currentTemplateDeclaration.append("\t\t}\n");
        currentTemplateDeclaration.append("\t} else {\n");
        currentTemplateDeclaration.append("\t\tcheckMatches = false;\n");
        currentTemplateDeclaration.append("\t}\n");
        currentTemplateDeclaration.append("}\n").append("\n");

        if (!_productionToOSupported.get(productionName)) {
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

            if (operatorIndexes != null) {
                currentTemplateDeclaration.append("\nvoid checkAndClearFinalOperator() {\n");
                currentTemplateDeclaration.append("\t if(");
                for (String nextOperatorIndex : operatorIndexes) {
                    if (currentTemplateDeclaration.charAt(currentTemplateDeclaration.length() - 1) != '(') {
                        currentTemplateDeclaration.append(" || ");
                    }
                    currentTemplateDeclaration.append("selectedFinalOperatorIndex == " + (nextOperatorIndex + 1));
                }
                currentTemplateDeclaration.append(") {\n").append("\t\taddToNestedCheckArray(finalOp);\n").append("\t}\n").append("}\n");
            }
        } else {
            currentTemplateDeclaration.append("int numFiringPerCycle = 1;\n").append("int currentNumFiringPerCycle = 0;\n");
        }

        return currentTemplateDeclaration.toString();
    }

    private String getConditionOrAssignment(String tempGlobalSize, int globalIndex, String setBoolean, boolean isRetract, String operatorAssignments, boolean isScheduler, Set<String> operatorIndexes) {
        String commaNext = ",\n";
        boolean isCondition = setBoolean.startsWith("checkContains") || isScheduler;

        StringBuilder builder = new StringBuilder("TEMP_GLOBAL_SIZE = ").append(tempGlobalSize).append(commaNext);
        builder.append("globalIndex = ").append(globalIndex).append(commaNext);
        builder.append("lookAheadArray = defaultLookAheadArray").append(commaNext);
        try {
            int tempSize = Integer.parseInt(tempGlobalSize);
            if (tempSize == globalIndex) {
                builder.append(setBoolean.substring(0, setBoolean.indexOf('=') + 2) + "false").append(commaNext);
            } else {
                builder.append(setBoolean).append(commaNext);
            }
        } catch (NumberFormatException e) {
            builder.append(setBoolean).append(commaNext);
        }

        String attributeArray = "attributeArray = productionAttributeArray" + commaNext;
        if (isCondition) {
            if (isRetract) {
//                builder.append("setOperatorArray()").append(commaNext);
//                builder.append("attributeArray = productions[productionIndexTemp].savedAttributeTemp").append(commaNext);
//                builder.append("valueArray = productions[productionIndexTemp].savedTempAndFunction").append(commaNext);
                builder.append("setArraysToSavedValues(productionIndexTemp)").append(commaNext);
            } else {
                builder.append("operatorArray = productionOperatorArray").append(commaNext);
                builder.append(attributeArray);
                builder.append("valueArray = productionValueArray").append(commaNext);
                builder.append("attributeTempArray = productionAttributeTemp").append(commaNext);
                builder.append("checkMatches = true").append(commaNext);
                builder.append("dummyArray = dummyArrayDefault").append(commaNext);
            }
            builder.append("tempOrFuncArray = productionTempAndFuncArray").append(commaNext);
            builder.append("doesContainArray = doesContainDefault").append(commaNext);
            builder.append("updateDoesContainTrueAndFalse()");
        } else {
            if (isRetract) {
                try {
                    Integer.parseInt(tempGlobalSize);
                    builder.append("setFunctionArray()");
                    if (operatorAssignments.length() > 0) {
                        for (String opIndex : operatorIndexes) {
                            builder.append(commaNext).append("clearOperator(").append(opIndex).append(")");
                        }
                        builder.append(commaNext).append("checkAndClearFinalOperator()");
                    }
                } catch (NumberFormatException e) {
                    builder.append("currentNumAttributes = \ngetNumAttributes(nestedCheckArray[0])");
                }
            } else {
//                builder.append("setOperatorArray()").append(commaNext);
//                builder.append("attributeArray = productions[productionIndex - 1].savedAttributeTemp").append(commaNext);
//                builder.append("valueArray = productions[productionIndex - 1].savedTempAndFunction").append(commaNext);
                builder.append("setArraysToSavedValues(productionIndex - 1)").append(commaNext);
                builder.append("attributeTempArray = productionAttributeTemp").append(commaNext);
                builder.append("tempOrFuncArray = productionTempAndFuncArray");
                if (operatorAssignments.length() > 0) {
                    builder.append(commaNext).append(operatorAssignments);
                }
            }
        }

        return builder.toString();
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

    private void loopThroughValues(LinkedList<String> loopArray, String value, HashSet<Integer> foundIndexes, int index) {
        for (String nextValue : loopArray) {
            if (nextValue.equals(value)) {
                foundIndexes.add(index);
            }
            index++;
        }
    }

    private void loopThroughTemp(Map<String, String> tempMap, Map<String, Map<String, HashSet<Integer>>> tempVariableToModifiedIndexes) {
        Map<String, HashSet<Integer>> allModifiedIndexes;
        HashSet<Integer> tempSet;
        for (String nextTempVariable :  tempMap.values()) {
            allModifiedIndexes = new HashMap<>();
            tempSet = new HashSet<>();
            loopThroughValues(conditionProductionIdentifiers, nextTempVariable, tempSet, 0);
            loopThroughValues(actionProductionIdentifiers, nextTempVariable, tempSet, conditionProductionIdentifiers.size() + 1);
            if (tempSet.size() > 0) {
                allModifiedIndexes.put("operatorArray", tempSet);
            }
            tempSet = new HashSet<>();
            loopThroughValues(conditionProductionAttributes, nextTempVariable, tempSet, 0);
            loopThroughValues(actionProductionAttributes, nextTempVariable, tempSet, conditionProductionIdentifiers.size() + 1);
            if (tempSet.size() > 0) {
                allModifiedIndexes.put("attributeArray", tempSet);
            }
            tempSet = new HashSet<>();
            loopThroughValues(conditionProductionValues, nextTempVariable, tempSet, 0);
            loopThroughValues(actionProductionValues, nextTempVariable, tempSet, conditionProductionIdentifiers.size() + 1);
            if (tempSet.size() > 0) {
                allModifiedIndexes.put("valueArray", tempSet);
            }
            allModifiedIndexes.put("extraForDummy", new HashSet<>());
            tempVariableToModifiedIndexes.put(nextTempVariable, allModifiedIndexes);
        }
    }

    private void findWhereTempVariablesAreUsed(Map<String, Map<String, HashSet<Integer>>> tempVariableToModifiedIndexes) {
        loopThroughTemp(conditionSideVariablesToTemps, tempVariableToModifiedIndexes);
        loopThroughTemp(attributesToTemps, tempVariableToModifiedIndexes);
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
        Map<String, Map<String, HashSet<Integer>>> tempVariableToModifiedIndexes = new HashMap<>();
        Map<String, Integer> dummyToIndex = new HashMap<>();
        _productionToDummyToIndex.put(_templateIndex, dummyToIndex);

        String startStateID = getCounter();

        Template currentTemplate = makeTemplate(SoarTranslator.simplifiedString(ctx.sym_constant().getText()));
        _templateNames.add(getText(currentTemplate, "name"));

        Location startLocation = makeLocationWithCoordinates(currentTemplate, "Start", startStateID, true, true, -152, 0, -200, -32);

        ctx.condition_side().accept(this);

        Node actionSide = ctx.action_side().accept(this);

        findWhereTempVariablesAreUsed(tempVariableToModifiedIndexes);
        if (tempVariableToModifiedIndexes.size() > 0) {
            _productionToTempToModifiedIndexes.put(_templateIndex, tempVariableToModifiedIndexes);
        }

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
                    String nextIndex = operatorAssignments.substring(lookIndex, operatorAssignments.indexOf("]", lookIndex));
                    operatorIndexes.add(nextIndex);
                }
            } while (possibleIndex != -1);
        } else {
            operatorIndexes = null;
        }

        currentTemplate.setProperty("declaration", getProductionDeclaration(ctx.sym_constant().getText(), operatorIndexes, dummyToIndex));

        if (operatorAssignments.length() > 0) {
            int lookIndex = 0;
            int possibleIndex;
            int secondIndex;
            StringBuilder newOperatorAssignments = new StringBuilder();
            do {
                possibleIndex = operatorAssignments.indexOf("[", lookIndex);
                if (possibleIndex != -1) {
                    secondIndex = operatorAssignments.indexOf("]", possibleIndex);
                    newOperatorAssignments.append(operatorAssignments, lookIndex, secondIndex + 1);
                    try {
                        Integer.parseInt(operatorAssignments.substring(possibleIndex + 1, secondIndex));
                        lookIndex = secondIndex + 1;
                    } catch (NumberFormatException e) {
                        int indexOfDummy = operatorAssignments.indexOf("savedDummyArray[", secondIndex) + ("savedDummyArray[").length();
                        int endIndexOfDummy = operatorAssignments.indexOf("]", indexOfDummy);
                        newOperatorAssignments.append(operatorAssignments, secondIndex + 1, indexOfDummy).append(dummyToIndex.get(operatorAssignments.substring(indexOfDummy, endIndexOfDummy)) - _latestNum).append("]");
                        lookIndex = endIndexOfDummy + 1;
                    }
                } else {
                    newOperatorAssignments.append(operatorAssignments, lookIndex, operatorAssignments.length());
                }
            } while (possibleIndex != -1);
            operatorAssignments = newOperatorAssignments.toString();
        }

        boolean halt = getText(actionSide, "hasHalt").equals("yes");
        boolean needsRetraction = !_productionToOSupported.get(ctx.sym_constant().getText());

        int[] lastLocationCoords = new int[2];
        setLastLocationCoords(lastLocationCoords);
        Location lastLocation;
        String nextAssignment;

        if (!halt) {
            if (needsRetraction) {
                lastLocation = addHorizontalLocation(currentTemplate, startLocation, lastLocationCoords, "Run_Retract", "Run_Rule?", "isRetracting", "addToStackRetract(" + _templateIndex + "),\nproductionIndexTemp = 0", true);
                Location runRetractLocation = lastLocation;

                goBackToProvidedLocation(currentTemplate, lastLocation, startLocation, lastLocationCoords, "stackRetract[stackRetractIndex] == " + _templateIndex + " &&\nproductionIndexTemp == productionIndex", "productionIndexTemp = 0,\nremoveStackRetract()", true);

                nextAssignment = getConditionOrAssignment(conditionProductionIdentifiers.size() + "", 0, "checkContains = true", true, "", false, operatorIndexes);
                lastLocation = addHorizontalLocation(currentTemplate, lastLocation, lastLocationCoords, null, null, "productionIndexTemp != productionIndex &&\nstackRetract[stackRetractIndex] == " + _templateIndex, nextAssignment, true);

                goBackToProvidedLocation(currentTemplate, lastLocation, runRetractLocation, lastLocationCoords, "!checkContains &&\ndoesContainArray == doesContainTrue", "productionIndexTemp++", true);

                nextAssignment = getConditionOrAssignment((actionProductionIdentifiers.size() + conditionProductionIdentifiers.size() + 1) + "", conditionProductionIdentifiers.size() + 1, "addOperator = true", true, operatorAssignments, false, operatorIndexes);
                lastLocation = addHorizontalLocation(currentTemplate, lastLocation, lastLocationCoords, "Run_Retract_Assignments", null, "!checkContains &&\ndoesContainArray != doesContainTrue", nextAssignment, true);

                nextAssignment = getConditionOrAssignment("nestedCheckIndex", 0, "removeOperator = true", true, "", false, operatorIndexes);
                lastLocation = addHorizontalLocation(currentTemplate, lastLocation, lastLocationCoords, "Run_Remove_Attributes", null, "!addOperator", nextAssignment, true);

                goBackToProvidedLocation(currentTemplate, lastLocation, runRetractLocation, lastLocationCoords, "!removeOperator &&\ncurrentNumAttributes == 0", "productionIndex--", true);
            } else {
                makeEdgeWithNails(currentTemplate, startLocation, startLocation, null, null, "Run_Rule?", new Integer[]{lastLocationCoords[0] + SIZE_OF_TEXT, lastLocationCoords[1] + SIZE_OF_TEXT*2}, "!productionFired &&\nisRetracting", new Integer[]{lastLocationCoords[0] + SIZE_OF_TEXT, lastLocationCoords[1] + SIZE_OF_TEXT*3}, "currentNumFiringPerCycle = 0", new Integer[]{lastLocationCoords[0] + SIZE_OF_TEXT, lastLocationCoords[1] + SIZE_OF_TEXT*5}, new Integer[]{lastLocationCoords[0], lastLocationCoords[1] + SIZE_OF_TEXT*5});
            }
        }

        setLastLocationCoords(lastLocationCoords);

        lastLocation = addHorizontalLocation(currentTemplate, startLocation, lastLocationCoords, "Run_Guard", "Run_Rule?", "!isRetracting &&\n" + (needsRetraction ? "productionIndex != 1" : "currentNumFiringPerCycle != numFiringPerCycle"), "addToStackCondition(" + _templateIndex + ")", false);

        goBackToProvidedLocation(currentTemplate, lastLocation, startLocation, lastLocationCoords, null, "halt", false);

        nextAssignment = getConditionOrAssignment(conditionProductionIdentifiers.size() + "", 0, "checkContains = true", false, "", false, operatorIndexes);
        lastLocation = addHorizontalLocation(currentTemplate, lastLocation, lastLocationCoords, null, null, "stackCondition[stackConditionIndex] == " + _templateIndex + " &&\n!addOperator", nextAssignment, false);

        goBackToProvidedLocation(currentTemplate, lastLocation, startLocation, lastLocationCoords, "!checkMatches &&\ndoesContainArray != doesContainTrue", "removeStackCondition()", false);

        makeEdgeWithNails(currentTemplate, lastLocation, lastLocation, null, null, null, null, "!checkContains &&\ncheckMatches", new Integer[]{lastLocationCoords[0] + SIZE_OF_TEXT, lastLocationCoords[1] + SIZE_OF_TEXT*9}, "checkProductionsContain()", new Integer[]{lastLocationCoords[0] + SIZE_OF_TEXT, lastLocationCoords[1] + SIZE_OF_TEXT*10}, new Integer[]{lastLocationCoords[0], lastLocationCoords[1] + SIZE_OF_TEXT*10});

        lastLocation = addHorizontalLocation(currentTemplate, lastLocation, lastLocationCoords, "Run_Assignment", null, "!checkMatches &&\ndoesContainArray == doesContainTrue", "removeStackCondition(),\naddToStackAction(" + _templateIndex + "),\nproductionFired = true,\nfillNextProduction()", false);

        nextAssignment = getConditionOrAssignment((actionProductionIdentifiers.size() + conditionProductionIdentifiers.size() + 1) + "", conditionProductionIdentifiers.size() + 1, "addOperator = true", false, operatorAssignments, false, operatorIndexes);
        lastLocation = addHorizontalLocation(currentTemplate, lastLocation, lastLocationCoords, null, null, "stackConditionIndex == -1 &&\nstackAction[stackActionIndex] ==" +  _templateIndex, nextAssignment, false);

        if (!halt) {
            nextAssignment = "removeStackAction()";
            if (!needsRetraction) {
                nextAssignment = nextAssignment + ",\ncurrentNumFiringPerCycle++";
            }
        } else {
            nextAssignment = "Halt!";
        }
        goBackToProvidedLocation(currentTemplate, lastLocation, startLocation, lastLocationCoords, "!addOperator", nextAssignment, false);

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

    private String getDummyIndex(String match) {
//        int index = 0;
//        for (String nextDummy : conditionProductionTemp) {
//            if (nextDummy.equals(match)) {
//                break;
//            }
//            index++;
//        }
        return "productions[productionIndex-1].savedDummyArray[" + match + "]";
    }

    private String getOperatorId(String index) {
        String returnString;
        try {
            Integer.parseInt(index);
            returnString = index;
        } catch (NumberFormatException e) {
            returnString = "getOperatorId(" + getDummyIndex(index) + ")";
        }
        return returnString;
    }

    private String operatorBaseString(String index, String parameter) {
        StringBuilder returnString = new StringBuilder();
        returnString.append("operators[");
        returnString.append(getOperatorId(index));
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
            if (rightSideElement.getProperty("const") != null) {
                actionProductionValues.add(getText(rightSideElement, "const"));
            } else if (rightSideElement.getProperty("expr") != null) {
                actionProductionValues.add(getText(rightSideElement, "firstValue"));
                actionProductionFunctions.add(getText(rightSideElement, "expr"));
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
                        operatorIndex = getOperatorId(operatorIndex);
                        thatValueID = getOperatorId(thatValueID);
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
        attributeTemps = new LinkedList<>();
        for (int i = 0; i < _maxQuerySize; i++) {
            attributeTemps.add("0");
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

        Template runScheduler = makeTemplate("Scheduler");

        runScheduler.setProperty("declaration", getTinyDeclaration(new String[]{"_state", "finalOp"}, new String[]{"superstate", "operator"}, new String[]{"nil"}));

        int[] lastLocationCoords = {-152, 0};
        Location lastLocation = makeLocationWithCoordinates(runScheduler, "Start", startId, true, true, lastLocationCoords[0], lastLocationCoords[1], lastLocationCoords[0] - 48, lastLocationCoords[1] - 32);

        String nextAssignment = getConditionOrAssignment("1", 0, "addOperator = true", false, "", true, null);
        lastLocation = addHorizontalLocation(runScheduler, lastLocation, lastLocationCoords, "Set_Superstate_Nil", null, null, nextAssignment, false);

        Location proposalLocation = addHorizontalLocation(runScheduler, lastLocation, lastLocationCoords, "Proposal", null, "!addOperator", "initialize(operators)", false);
        lastLocation = proposalLocation;

        lastLocation = addHorizontalLocation(runScheduler, lastLocation, lastLocationCoords, "Run_Retract", "Run_Rule!", "!halt", "productionFired = false", false);
        goBackToProvidedLocation(runScheduler, lastLocation, proposalLocation, lastLocationCoords, null, "halt", false);
        lastLocation = addHorizontalLocation(runScheduler, lastLocation, lastLocationCoords, null, null, "stackConditionIndex == -1 &&\nstackActionIndex == -1 &&\n!addOperator", "isRetracting = true", false);
        lastLocation = addHorizontalLocation(runScheduler, lastLocation, lastLocationCoords, "Ready_Decision", "Run_Rule!", null, null, false);
        goBackToProvidedLocation(runScheduler, lastLocation, proposalLocation, lastLocationCoords, "productionFired &&\nstackRetractIndex == -1", "isRetracting = false", false);
        lastLocation = addHorizontalLocation(runScheduler, lastLocation, lastLocationCoords, "Decision", null, "!productionFired &&\nstackRetractIndex == -1", "isRetracting = false,\nfillOthers()", false);
        lastLocation = addHorizontalLocation(runScheduler, lastLocation, lastLocationCoords, "Ready_Application", "Require_Test!", null, null, false);
        Location applicationLocation = addHorizontalLocation(runScheduler, lastLocation, lastLocationCoords, "Application", "Continue_Run?", null, null, false);
        lastLocation = applicationLocation;
        lastLocation = addHorizontalLocation(runScheduler, lastLocation, lastLocationCoords, "Back_To_Proposal", "Run_Rule!", null, "productionFired = false", false);
        goBackToProvidedLocation(runScheduler, lastLocation, proposalLocation, lastLocationCoords, null, "halt", false);
        lastLocation = addHorizontalLocation(runScheduler, lastLocation, lastLocationCoords, null, null, "stackConditionIndex == -1 &&\nstackActionIndex == -1 &&\n!addOperator", "isRetracting = true", false);
        lastLocation = addHorizontalLocation(runScheduler, lastLocation, lastLocationCoords, "Run_Retract_Again", "Run_Rule!", null, null, false);
        nextAssignment = getConditionOrAssignment("1", 2, "removeOperator = true", false, "", true, null);
        goBackToProvidedLocation(runScheduler, lastLocation, proposalLocation, lastLocationCoords, "!productionFired &&\nstackRetractIndex == -1", "clearFill(required),\nclearFill(acceptable),\nclearFill(best),\nisRetracting = false,\n" + nextAssignment, false);
        goBackToProvidedLocation(runScheduler, lastLocation, applicationLocation, lastLocationCoords, "productionFired &&\nstackRetractIndex == -1", "isRetracting = false", true);

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
                "\tif (valueArray[globalIndex] == nilAnything) {\n" +
                "\t\tif (lookAheadArray[globalIndex] < valuesIndex) {\n" +
//                "\t\t\tint i;\n" +
//                "\t\t\tfor (i = globalIndex + 1; i < MAX_GLOBAL_SIZE; i++) {\n" +
//                "\t\t\t\tif (operatorArray[i] == tempOrFuncArray[globalIndex]) {\n" +
//                "\t\t\t\t\toperatorArray[i] = values[lookAheadArray[globalIndex]];\n" +
//                "\t\t\t\t}\n" +
//                "\t\t\t\tif (attributeArray[i] == tempOrFuncArray[globalIndex]) {\n" +
//                "\t\t\t\t\tattributeArray[i] = values[lookAheadArray[globalIndex]];\n" +
//                "\t\t\t\t}\n" +
//                "\t\t\t\tif (valueArray[i] == tempOrFuncArray[globalIndex]) {\n" +
//                "\t\t\t\t\tvalueArray[i] = values[lookAheadArray[globalIndex]];\n" +
//                "\t\t\t\t}\n" +
//                "\t\t\t}\n" +
                "\t\t\tint lookForValue = tempOrFuncArray[globalIndex];\n" +
                "\t\t\tint replaceValue = values[lookAheadArray[globalIndex]];\n" +
                "\t\t\treplaceSpecificValues(lookForValue, replaceValue);\n" +
//                "\t\t\ttempOrFuncArray[globalIndex] = values[lookAheadArray[globalIndex]];\n" +
                "\t\t\tdoesContainArray[globalIndex] = 1;\n" +
                "\t\t\tlookAheadArray[globalIndex]++;\n" +
                "\t\t\tglobalIndex++;\n" +
                "\t\t\tif (globalIndex >= TEMP_GLOBAL_SIZE) {\n" +
                "\t\t\t\tcheckContains = false;\n" +
                "\t\t\t}\n" +
                "\t\t} else {\n" +
                "\t\t\tlookAheadArray[globalIndex] = 0;\n" +
                "\t\t\tcheckNextCombo();\n" +
//                "\t\t\tdoesContainArray[globalIndex] = -1;\n" +
//                "\t\t\tglobalIndex--;\n" +
//                "\t\t\twhile (globalIndex != -1 && valueArray[globalIndex] != nilAnything) {\n" +
//                "\t\t\t\tdoesContainArray[globalIndex] = -1;\n" +
//                "\t\t\t\tglobalIndex--;\n" +
//                "\t\t\t}\n" +
                "\t\t\tif (globalIndex == -1) {\n" +
                "\t\t\t\tcheckContains = false;\n" +
                "\t\t\t}\n" +
                "\t\t}\n" +
                "\t} else {\n" +
                "\t\tint contains = -1;\n" +
                "\t\tif (valueArray[globalIndex] == EMPTY && valuesIndex == 0) {\n" +
                "\t\t\tcontains = 1;\n" +
                "\t\t} else {\n" +
                "\t\t\tint i;\n" +
                "\t\t\tfor (i = 0; i < valuesIndex; i++) {\n" +
                "\t\t\t\tif (values[i] == valueArray[globalIndex]) {\n" +
                "\t\t\t\t\tcontains = 1;\n" +
                "\t\t\t\t\ti = valuesIndex;\n" +
                "\t\t\t\t}\n" +
                "\t\t\t}\n" +
                "\t\t}\n" +
                "\t\tif (contains == 1) {\n" +
                "\t\t\tdoesContainArray[globalIndex] = 1;\n" +
                "\t\t\tglobalIndex++;\n" +
                "\t\t\tif (globalIndex >= TEMP_GLOBAL_SIZE) {\n" +
                "\t\t\t\tcheckContains = false;\n" +
                "\t\t\t}\n" +
                "\t\t} else {\n" +
                "\t\t\tcheckNextCombo();\n" +
//                "\t\t\tdoesContainArray[globalIndex] = -1;\n" +
//                "\t\t\tglobalIndex--;\n" +
//                "\t\t\twhile (globalIndex != -1 && valueArray[globalIndex] != nilAnything) {\n" +
//                "\t\t\t\tdoesContainArray[globalIndex] = -1;\n" +
//                "\t\t\t\tglobalIndex--;\n" +
//                "\t\t\t}\n" +
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
                "\t\tif (tempOrFuncArray[globalIndex] == addFunction) {\n" +
                "\t\t\tvalues[valuesIndex] += valueArray[globalIndex + 1];\n" +
                "\t\t\tglobalIndex++;\n" +
                "\t\t} else if (tempOrFuncArray[globalIndex] == subtractFunction) {\n" +
                "\t\t\tvalues[valuesIndex] -= valueArray[globalIndex + 1];\n" +
                "\t\t\tglobalIndex++;\n" +
                "\t\t}\n" +
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
                "\t\tint numAttributes = getNumAttributes(valueArray[globalIndex]);\n" +
                "\t\tif (numAttributes > 0) {\n" +
                "\t\t\taddToNestedCheckArray(valueArray[globalIndex]);\n" +
                "\t\t}\n" +
                "\t}\n" +
                "\tglobalIndex++;\n" +
                "\tif (globalIndex == TEMP_GLOBAL_SIZE) {\n" +
                "\t\taddOperator = false;\n" +
                "\t}\n" +
                "}");

        Location startLocation = makeLocationWithCoordinates(attributeValueTemplate, "Start", startId, true, true, -739, -195, -780, -229);
        Location middleAddLocation = makeLocationWithCoordinates(attributeValueTemplate, null, middleAddLocationID, true, false, -229, -195, null, null);

        makeEdgeWithNails(attributeValueTemplate, middleAddLocation, startLocation, null, null, null, null, "tempOrFuncArray[globalIndex] == remove", new Integer[]{-425, -331}, "removeSpecificValue()", new Integer[]{-425, -314}, new Integer[]{-535, -340});
        makeEdgeWithNails(attributeValueTemplate, middleAddLocation, startLocation, null, null, null, null, "tempOrFuncArray[globalIndex] != remove", new Integer[]{-382, -127}, "addValue()", new Integer[]{-382, -110}, new Integer[]{-535, -68});
        makeEdgeWithNails(attributeValueTemplate, startLocation, startLocation, null, null, null, null, "removeOperator &&\ncurrentNumAttributes > 0 &&\nnestedCheckArray[globalIndex] == OPERATOR_ID", new Integer[]{-790, -85}, "removeValue()", new Integer[]{-790, -34}, new Integer[]{-739, -144, -688, -93, -790, -93, -739, -144});
        makeEdgeWithNails(attributeValueTemplate, startLocation, startLocation, null, null, null, null, "checkContains &&\noperatorArray[globalIndex] == OPERATOR_ID &&\nattributeArray[globalIndex] == ATTRIBUTE_INDEX", new Integer[]{-1156, -204}, "doValuesContain()", new Integer[]{-1156, -153}, new Integer[]{-739, -144, -807, -144, -807, -195});
        makeEdge(attributeValueTemplate, startLocation, middleAddLocation, null, null, null, null, "addOperator &&\noperatorArray[globalIndex] == OPERATOR_ID &&\nattributeArray[globalIndex] == ATTRIBUTE_INDEX", new Integer[]{-654, -255}, "containsIndex =getIndexOfValue()", new Integer[]{-654, -187});

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
        makeEdgeWithNails(currentTemplate, loopLocation, loopLocation, null, null, null, null, guard, new Integer[]{xTextLocation, loopLocation.getY() - 10}, assignment, new Integer[]{xTextLocation, loopLocation.getY() - 10 + getNumLines(guard, " &&")*SIZE_OF_TEXT}, nails);
    }

    private Element getAVUtility() {
        Template AVUtilityTemplate = makeTemplate("Attribute_Value_Utility");

        AVUtilityTemplate.setProperty("declaration",
                "void catchNumBut() {\n" +
                "\tdoesContainArray[globalIndex] = 1;\n" +
                "\tglobalIndex++;\n" +
                "\tif (globalIndex >= TEMP_GLOBAL_SIZE) {\n" +
                "\t\tcheckContains = false;\n" +
                "\t}\n" +
                "}\n" +
                "\n" +
                "void checkCondition() {\n" +
                "\tbool conditionSatisfied = false;\n" +
                "\tif (tempOrFuncArray[globalIndex] == isNotEqualTo && operatorArray[globalIndex] != valueArray[globalIndex]) {\n" +
                "\t\tconditionSatisfied = true;\n" +
                "\t} else if (tempOrFuncArray[globalIndex] == isGreaterThan && operatorArray[globalIndex] > valueArray[globalIndex]) {\n" +
                "\t\tconditionSatisfied = true;\n" +
                "\t} else if (tempOrFuncArray[globalIndex] == isLessThan && operatorArray[globalIndex] < valueArray[globalIndex]) {\n" +
                "\t\tconditionSatisfied = true;\n" +
                "\t}\n" +
                "\tif (conditionSatisfied) {\n" +
                "\t\tdoesContainArray[globalIndex] = 1;\n" +
                "\t\tglobalIndex++;\n" +
                "\t\tif (globalIndex >= TEMP_GLOBAL_SIZE) {\n" +
                "\t\t\tcheckContains = false;\n" +
                "\t\t}\n" +
                "\t} else {\n" +
                "\t\tcheckNextCombo();\n" +
//                "\t\tdoesContainArray[globalIndex] = -1;\n" +
//                "\t\tglobalIndex--;\n" +
//                "\t\twhile (globalIndex != -1 && valueArray[globalIndex] != nilAnything) {\n" +
//                "\t\t\tdoesContainArray[globalIndex] = -1;\n" +
//                "\t\t\tglobalIndex--;\n" +
//                "\t\t}\n" +
                "\t\tif (globalIndex == -1) {\n" +
                "\t\t\tcheckContains = false;\n" +
                "\t\t}\n" +
                "\t}\n" +
                "}\n" +
                "\n" +
                "void nextNumBut() {\n" +
                "\tint nextIndex = valueArray[globalIndex] + 1;\n" +
                "\tint nextElement = getNumButNextElement(attributeArray[globalIndex], nextIndex);\n" +
                "\tint i;\n" +
                "\tif (nextElement == -1) {\n" +
                "\t\tvalueArray[globalIndex] = -1;\n" +
                "\t\tdoesContainArray[globalIndex] = -1;\n" +
                "\t\tglobalIndex--;\n" +
                "\t} else {\n" +
//                "\t\tfor (i = globalIndex + 1; i < MAX_GLOBAL_SIZE; i++) {\n" +
//                "\t\t\tif (operatorArray[i] == attributeTempArray[globalIndex]) {\n" +
//                "\t\t\t\toperatorArray[i] = nextElement;\n" +
//                "\t\t\t}\n" +
//                "\t\t\tif (attributeArray[i] == attributeTempArray[globalIndex]) {\n" +
//                "\t\t\t\tattributeArray[i] = nextElement;\n" +
//                "\t\t\t}\n" +
//                "\t\t\tif (valueArray[i] == attributeTempArray[globalIndex]) {\n" +
//                "\t\t\t\tvalueArray[i] = nextElement;\n" +
//                "\t\t\t}\n" +
//                "\t\t}\n" +
                "\t\tint lookForValue = attributeTempArray[globalIndex];\n" +
                "\t\tint replaceValue = nextElement;\n" +
                "\t\treplaceSpecificValues(lookForValue, replaceValue);\n" +
//                "\t\tattributeTempArray[globalIndex] = nextElement;\n" +
                "\t\tvalueArray[globalIndex] = nextIndex;\n" +
                "\t\tdoesContainArray[globalIndex] = 1;\n" +
                "\t\tglobalIndex++;\n" +
                "\t}\n" +
                "\tif (globalIndex >= TEMP_GLOBAL_SIZE || globalIndex < 0) {\n" +
                "\t\tcheckContains = false;\n" +
                "\t}\n" +
                "}\n" +
                "\n" +
                "void catchAll() {\n" +
                "\tcheckNextCombo();\n" +
//                "\tdoesContainArray[globalIndex] = -1;\n" +
//                "\tglobalIndex--;\n" +
//                "\twhile (globalIndex != -1 && valueArray[globalIndex] != nilAnything) {\n" +
//                "\t\tdoesContainArray[globalIndex] = -1;\n" +
//                "\t\tglobalIndex--;\n" +
//                "\t}\n" +
                "\tif (globalIndex == -1) {\n" +
                "\t\tcheckContains = false;\n" +
                "\t}\n" +
                "}\n" +
                "\n");

        Location startLocation = makeLocationWithCoordinates(AVUtilityTemplate, "Start", getCounter(), true, true, -739, -195, -780, -229);

        makeLoop("left", AVUtilityTemplate, startLocation, "checkContains &&\nattributeArray[globalIndex] == extraRestriction", "checkCondition()");
        if (_disjunctionArrayNameToArray.values().size() > 0) {
            makeLoop("right", AVUtilityTemplate, startLocation, "checkContains &&\nattributeArray[globalIndex] <= noneBut_1", "nextNumBut()");
        }

        StringBuilder catchAll = new StringBuilder("(checkContains &&\nglobalIndex >= 0) &&\n(");
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
            String operatorValue = "operatorArray[globalIndex] == " + nextIdentifier + " &&\n";
            count = 0;
            catchAll.append("(");
            for (String nextAttribute : nextVariableToAttribute.getValue()) {
                if (count != 0) {
                    catchAll.append(" &&\n");
                } else if (nextIdentifier.equals("_state")) {
                    catchAll.append(operatorValue);
                    catchAll.append("attributeArray[globalIndex] != superstate &&\n");
                    count++;
                }
                catchAll.append(operatorValue);
                catchAll.append("attributeArray[globalIndex] != ").append(nextAttribute);
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
            catchAll.append("attributeArray[globalIndex] != ").append(nextArrayNameToArray.getKey());
            count++;
        }

        if (catchAll.length() > 0) {
            catchAll.append(" &&\n");
        }
        catchAll.append("attributeArray[globalIndex] != extraRestriction)");
        count += 1;
        shift += count;
        String guard = catchAll.toString();

        makeEdgeWithNails(AVUtilityTemplate, startLocation, startLocation, null, null, null, null, guard, new Integer[]{-790, -85}, "catchAll()", new Integer[]{-790, -85 + (shift*SIZE_OF_TEXT)}, new Integer[]{-739, -144, -688, -93, -790, -93, -739, -144});

        Integer[] nails = new Integer[]{startLocation.getX() + 68, startLocation.getY(), startLocation.getX() + 68, startLocation.getY() - 51, startLocation.getX(), startLocation.getY() - 51};
        makeEdgeWithNails(AVUtilityTemplate, startLocation, startLocation, null, null, null, null, "isRetracting &&\ncheckContains &&\noperatorArray[globalIndex] == 0 &&\nvalueArray[globalIndex] == -1", new Integer[]{startLocation.getX() + 75, startLocation.getY() - 10 - (SIZE_OF_TEXT * 7)}, "catchNumBut()", new Integer[]{startLocation.getX() + 75, startLocation.getY() - 10 - (SIZE_OF_TEXT * 3)}, nails);
        return AVUtilityTemplate;
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
                ifStatements.append("if (finalOperatorIndex == operators[").append(Integer.parseInt(possibleOperator.substring(possibleOperator.lastIndexOf('_') + 1)) - 1).append("].operator.id) {\n");
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
        String nextAssignment = "productionValueArray[0] = getOperator(),\n" + getConditionOrAssignment("1", 0, "addOperator = true", false, "", true, null);
        makeEdge(operatorPreferencesTemplate, done, noName4, null, null, null, null, null, null, nextAssignment + ",\nselectedFinalOperatorIndex = finalOperatorIndex", new Integer[]{-3280, -504});
        makeEdgeWithNails(operatorPreferencesTemplate, noName4, start, null, null, "Continue_Run!", new Integer[]{-3918, -1113}, "!addOperator", new Integer[]{-3918, -1097}, null, null, new Integer[]{-3808, -1536});

        return null;
    }
}
