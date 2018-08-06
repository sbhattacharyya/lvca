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

/**
 * Created and updated by Daniel Griessler throughout the summer of 2018
 * Generates an XML document that can be then opened by Uppaal based on a Soar analysis provided by SymbolVisitor and SoarTranslator and ultimately on a Soar agent provided
 * Uses package produced by makers of Uppaal to create and modify XML document
 */

public class UPPAALSemanticVisitor extends SoarBaseVisitor<Node> {

    //Everything is run through the visitor pattern.  The visitor pattern follows the ANTLR grammar and is able to pass ONE data structure UP through the structure
    //This limitation resulted in us adding many global variables that are modified and accessed throughout the visitor pattern.  This eliminates the requirement of sending only one
    //complex data structure and we can add and remove structures as needed.
    //Most of the maps will map production names to another map.  They also often work in pairs, one as the "current" one for the production and one that is the "global" one
    //There are some structures specific to UppaalSemanticVisitor but there are also many that are just passed through from SymbolVisitor and SoarTranslator
    private static final int SIZE_OF_TEXT = 17; //How far to shift text down in Uppaal model. Found by guess and check
    static final String LITERAL_STRING_PREFIX = "literal_string__";
    private final Set<String> _globals;
    private HashMap<String, Integer> _globalToIndex;
    private final Set<String> _booleanGlobals;
    private final int NUM_OPERATORS;
    private final Map<String, Map<String, String>> _variableDictionary;
    private Integer _locationCounter = 0;
    private Document ourDocument = new Document(new PrototypeDocument());
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
    private Map<String, String> _conditionSideVariablesToTemps;
    private LinkedList<String> _conditionProductionIdentifiers;
    private LinkedList<String> _conditionProductionAttributes;
    private LinkedList<String> _conditionProductionValues;
    private LinkedList<String> _conditionProductionTemp;
    private LinkedList<String> _actionProductionIdentifiers;
    private LinkedList<String> _actionProductionAttributes;
    private LinkedList<String> _actionProductionValues;
    private LinkedList<String> _actionProductionFunctions;
    private Map<String, String> _attributesToTemps;
    private LinkedList<String> _attributeTemps;
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
    private Map<String, Integer> _productionToProductionSize;

    /**
     * Creates a new UPPAALSemanticVisitor and copies all of the passed in structures to globals stored in here
     * @param stringAttributeNames Set of string constants used in the Soar agent
     * @param variablesPerProductionContext Map from production name to a mapping from a variable to its path
     * @param boolAttributeNames Set of constants which are boolean values
     * @param numOperators Number of operators that will be needed by Soar
     * @param actualVariablesPerProduction Map from production name to ProductionVariables which distinguishes which variables are actual variables and which are used as identifiers later
     * @param takenValues List of numbers which are reserved by Soar as constants
     * @param uppaalOperatorCollection List of names of the all of the identifiers needed by Soar
     * @param AVCollection List of UppaalAttributeValueTriad which make it easy to enumerate all of the AV templates
     * @param variablesToPathWithID Map from production name to mapping from a variable to its path with ID
     * @param maxQuerySize Maximum number of conditions and actions needed by a production
     * @param productionToOSupported Map from production name to whether or not it is O-supported
     * @param variableToAttributes Map from variable (identifier) to its list of attributes that are associated with it
     * @param attributeVariableToDisjunctionTestPerProduction Map from production name to a mapping from variable (attribute) to a String array of the values it has to match
     * @param productionToProductionSize Map from production name to how many conditions and actions it needs
     */
    public UPPAALSemanticVisitor(Set<String> stringAttributeNames, Map<String, Map<String, String>> variablesPerProductionContext, Set<String> boolAttributeNames, int numOperators, Map<String, ProductionVariables> actualVariablesPerProduction, HashSet<Integer> takenValues, LinkedList<String> uppaalOperatorCollection, LinkedList<UppaalAttributeValueTriad> AVCollection, Map<String, Map<String, String>> variablesToPathWithID, int maxQuerySize, Map<String, Boolean> productionToOSupported, Map<String, LinkedList<String>> variableToAttributes, Map<String, Map<String, String[]>> attributeVariableToDisjunctionTestPerProduction, Map<String, Integer> productionToProductionSize) {
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
        _productionToProductionSize = productionToProductionSize;
    }

    /**
     * Utility for cleanAttributeVariableToArrayName
     * Goes through all the productions and collects all distinct arrays into a mapping from an array name to that array.
     * @param checkArray String array to be checked
     * @param index Most recent index for giving unique names to all of the arrays. It is an array so that it is passed by reference and not by value
     * @return Name of the array to be stored in the currentVariableToArrayName
     */
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
     * This is super space inefficient right now.  It's checking if the arrays are equal by looping through all the elements in both arrays
     * This can be made much more efficient by storing the arrays as encoded single values which can then be compared
     * #todo make this more efficient
     * @return Map from production to mapping from variable (attribute) to the name of the array
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

    /**
     * Increments the provided value by 1 and then continually by 1 until it doesn't match the next element of _takenValues
     * @param i The index to be incremented
     * @return The next available index
     */
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

    /**
     * Fills _globalToIndex with a mapping from the variable to its index in Uppaal
     */
    private void fillGlobalToIndex() {
        _globalToIndex = new HashMap<>();
        int i = getNextIndex(0);
        for (String variable : _globals) {
            if (!variable.equals("nil")) {
                _globalToIndex.put(variable, i);
                i = getNextIndex(i);
            }
        }
    }

    /**
     * Gets the String equivalent of the current value in _locationCounter and increments _locationCounter
     * @return Current value of _locationCounter as a String
     */
    private String getCounter() {
        String i = _locationCounter.toString();
        _locationCounter++;
        return i;
    }

    /**
     * Adds the provided variable with its provided variableIndex to the StringBuilder provided as a constant int
     * @param globalVariables StringBuilder to be adding the new constant to
     * @param variable Variable name to be added
     * @param variableIndex Index to which the variable is associated. If null, the value will begin uninitialized
     */
    private void addConstantToBuilder(StringBuilder globalVariables, String variable, Integer variableIndex) {
        globalVariables.append("const ");
        globalVariables.append("int ");
        globalVariables.append(variable);
        if (variableIndex != null) {
            globalVariables.append(" = ");
            globalVariables.append(variableIndex);
        }
        globalVariables.append(";\n");
    }

    /**
     * Gets the global declaration that is found in Uppaal. There is one StringBuilder that is filled with a lot of static text as well as some that depends on the specific Soar model
     * This method can only be run after the condition and action side of the productions have been visited since it depends on many of the global variables being changed and updated
     */
    private void getGlobalDeclaration() {
        _globals.remove("nil"); // added later so that nil always equals 0

        StringBuilder globalDeclaration = new StringBuilder();

        globalDeclaration.append(_booleanGlobals
                .stream()
                .map(SoarTranslator::simplifiedString)
                .map(var -> "bool " + var + "; \n")
                .collect(Collectors.joining()));

        globalDeclaration.append("const int nil = 0;\n" +
                "const int nilAnything = -1;\n");

        // This initial part goes through and adds in all of the arbitrary indexes that Uppaal needs to use to represent "strings" since it can only handling storing ints
        // Note: There is a cap to how large the ints can go in Uppaal, if you are having overflow int problems then start here with any fixes
        // The counter starts at 1 and increments up. Currently, nil takes 0 and then some of the initial negative numbers are reserved for special keywords needing in the model
        StringBuilder globalVariables = new StringBuilder();
        int index = 1;
        for (String variable : _globals) {
            int nextGlobalIndex = _globalToIndex.get(variable);
            addConstantToBuilder(globalVariables, SoarTranslator.simplifiedString(variable), nextGlobalIndex);
            index = Math.max(nextGlobalIndex, index);
        }
        index++;
        LinkedList<String> actualOperatorCollection = new LinkedList<>();
        for (String variable : _uppaalOperatorCollection) {
            addConstantToBuilder(globalVariables, SoarTranslator.simplifiedString(variable), index++);
            if (variable.startsWith("state_operator")) {
                actualOperatorCollection.add(variable);
            }
        }
        addConstantToBuilder(globalVariables, "finalOp", index++);
        addConstantToBuilder(globalVariables, "_state", -1);

        for (String variable : _variableToAttributes.keySet()) {
            String variableText;
            if (variable.equals("state_-1")) {
                variableText = "state";
            } else {
                variableText = variable;
            }
            addConstantToBuilder(globalVariables, SoarTranslator.simplifiedString(variableText) + "_num_attributes", _variableToAttributes.get(variable).size());
        }

        //index is set to latest negative number.  Currently, -12. Based on what other values are needed , you can move this further negative. These just need to be distinct values
        index = -12;
        int max = -1;

        // This not only adds in all the noneBut (disjunction tests) as declarations
        // It also adds a switch statement to retrieve the value of the noneBut array at the provided index if the index is valid
        // The switch is actually added to the globalDeclaration until close to the very end since I wanted to list the other variables first
        // The switch is made all the way up here because it adds to globalVariables
        StringBuilder noneButSwitch = _disjunctionArrayNameToArray.values().size() > 0 ? new StringBuilder("int getNumButNextElement(int numBut, int index) {\n") : null;
        boolean hasIf = false;
        for (Map.Entry<String, String[]> disjunctionMap : _disjunctionArrayNameToArray.entrySet()) {
            max = Math.max(max, disjunctionMap.getValue().length);
            addConstantToBuilder(globalVariables, disjunctionMap.getKey(), index--);
            globalVariables.append("const int ").append(disjunctionMap.getKey()).append("_array[").append(disjunctionMap.getValue().length).append("] = {");
            for (int i = 0; i< disjunctionMap.getValue().length; i++) {
                if (i != 0) {
                    globalVariables.append(", ");
                }
                globalVariables.append(SoarTranslator.simplifiedString(disjunctionMap.getValue()[i]));
            }
            globalVariables.append("};\n");
            addConstantToBuilder(globalVariables, disjunctionMap.getKey() + "_array_size", disjunctionMap.getValue().length);
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

        // Adds all of the declarations for the identifiers, attributes, and values that are needed for this particular Soar agent into the global declaration
        globalDeclaration.append(globalVariables.toString());

        // This is a large static bit of text that is needed for every Soar model no matter the size or complexity.
        // If you need to change a part of the Uppaal model that is accessed by at least two templates, you will need to add its declaration in here somewhere
        // We have it mostly separated by groups so try and keep things sorted
        globalDeclaration.append("broadcast chan Run_Rule;\n" +
                "broadcast chan Halt;\n" +
                "chan Continue_Run;\n" +
                "chan Require_Test;\n" +
                "bool halt = false;\n" +
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
        globalDeclaration.append("const int TOTAL_NUM_ATTRIBUTES = " +
                totalAttributeSize + ";\n" +
                "int nestedCheckArray[TOTAL_NUM_ATTRIBUTES];\n" +
                "int nestedCheckIndex = 0;\n");

        globalDeclaration.append("const int MAX_DUMMY_SIZE = ").append(_maxTemps).append(";\n");
        globalDeclaration.append("int dummyArray[MAX_DUMMY_SIZE];\n");
        globalDeclaration.append("int dummyArrayDefault[MAX_DUMMY_SIZE];\n");

        // Static string
        // Contains two structures used for operators
        // Also contains, all the methods that are needed for stacks and operators right now.  Some can probably be condensed
        globalDeclaration.append("\n" +
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

        globalDeclaration.append("typedef struct {\n" +
                "\tint savedDummyArray[MAX_DUMMY_SIZE];\n" +
                "} Production;\n" +
                "\n");

        // Switch statement to get the number of attributes associated with each identifier
        // Used for recursive retraction
        globalDeclaration.append("int getNumAttributes(int variable) {\n");

        StringBuilder newSwitch = new StringBuilder();
        newSwitch.append("\tif (variable == finalOp){\n\t\treturn 1;\n\t}");
        for (String variable : _uppaalOperatorCollection) {
            String correctedName = SoarTranslator.simplifiedString(variable);
            newSwitch.append(" else if (variable == " + correctedName + ") {\n").append("\t\treturn " + correctedName + "_num_attributes;\n").append("\t}");
        }
        newSwitch.append(" else {\n").append("\t\treturn -1;\n").append("\t}\n");
        globalDeclaration.append(newSwitch).append("}\n").append("\n");

        globalDeclaration.append("int getOperatorId(int operator) {\n");

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
        globalDeclaration.append(newSwitch);

        if (noneButSwitch != null) {
            globalDeclaration.append(noneButSwitch);
        }

        // I don't think I need this actually because Uppaal checks this already when you say array1 == array2
        globalDeclaration.append("bool checkDummyArraysEqual(int array1[MAX_DUMMY_SIZE], int array2[MAX_DUMMY_SIZE]) {\n");
        globalDeclaration.append("\tint i;\n");
        globalDeclaration.append("\tfor (i = 0; i < MAX_DUMMY_SIZE; i++) {\n");
        globalDeclaration.append("\t\tif (array1[i] != array2[i]) {\n");
        globalDeclaration.append("\t\t\treturn false;\n");
        globalDeclaration.append("\t\t}\n");
        globalDeclaration.append("\t}\n");
        globalDeclaration.append("\treturn true;\n");
        globalDeclaration.append("}\n").append("\n");

        // I don't think I need this actually because Uppaal checks this already when you say array1 == array2
        globalDeclaration.append("bool checkGlobalArraysEqual(int array1[MAX_GLOBAL_SIZE], int array2[MAX_GLOBAL_SIZE]) {\n");
        globalDeclaration.append("\tint i;\n");
        globalDeclaration.append("\tfor (i = 0; i < MAX_GLOBAL_SIZE; i++) {\n");
        globalDeclaration.append("\t\tif (array1[i] != array2[i]) {\n");
        globalDeclaration.append("\t\t\treturn false;\n");
        globalDeclaration.append("\t\t}\n");
        globalDeclaration.append("\t}\n");
        globalDeclaration.append("\treturn true;\n");
        globalDeclaration.append("}\n").append("\n");

        globalDeclaration.append("void checkNextCombo() {\n");
        globalDeclaration.append("\tdoesContainArray[globalIndex] = -1;\n");
        globalDeclaration.append("\tglobalIndex--;\n");
        globalDeclaration.append("\twhile (globalIndex != -1 && valueArray[globalIndex] != nilAnything && attributeArray[globalIndex] > noneBut_1) {\n");
        globalDeclaration.append("\t\tdoesContainArray[globalIndex] = -1;\n");
        globalDeclaration.append("\t\tglobalIndex--;\n");
        globalDeclaration.append("\t}\n");
        globalDeclaration.append("}\n").append("\n");

        newSwitch = new StringBuilder();
        globalDeclaration.append("void replaceSpecificValues(int dummyValue, int replaceValue, int stackAtIndex) {\n");
        boolean first;
        for (Map.Entry<Integer, Map<String, Map<String, HashSet<Integer>>>> productionIndexToModifiedIndexesEntry : _productionToTempToModifiedIndexes.entrySet()) {
            if (newSwitch.length() > 0) {
                newSwitch.append("\t else ");
            } else {
                newSwitch.append("\t");
            }

            newSwitch.append("if (stackAtIndex == " + productionIndexToModifiedIndexesEntry.getKey() + ") {\n");
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
        globalDeclaration.append(newSwitch.toString()).append("\n}\n");


        ourDocument.setProperty("declaration", globalDeclaration.toString());
    }

    /**
     * Sets the system declaration for Uppaal based on all the templates that were created.
     * @param attributeValuePairs These are all the attributeValuePairs that are created in the getScheduler method based on the UppaalAttributeValueTriad
     */
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

    /**
     * Visits each production, sets up the global declaration, builds the AV pairs and the supporter templates, and finally saves the document
     * @param ctx Entire Soar file
     * @return Null
     */
    @Override
    public Node visitSoar(SoarParser.SoarContext ctx) {

        ctx.soar_production().forEach(sp -> sp.accept(this));

        getGlobalDeclaration();

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

    /**
     * Calculates the X location of where a name should go in Uppaal based on the length of the name. Calculation based on guess and check in Uppaal
     * @param name Name of the location
     * @param lastLocationCoordsX Initial location from which to calculate the names location
     * @return Calculated locatoin for the name
     */
    private int getNameLocation(String name, int lastLocationCoordsX) {
        if (name == null) {
            return 0;
        }
        // The 10 is a magic constant based on guess and check in Uppaal.  It works almost all the time.
        return lastLocationCoordsX - 10 - 10*(name.length() - 1);
    }

    /**
     * Adds a location in Uppaal horizontally with an edge going back to the provided lastLocation.  The distance was chosen arbitrarily so it can be manipulated
     * @param currentTemplate The current template where the location will be added
     * @param lastLocation The last location where the edge will be coming from and then going to the new location created
     * @param lastLocationCoords The coordinates of the last location. They can also be found with a .getX() and .getY() method from the location but it's a little easier with them stored this way
     * @param name Name of the new location
     * @param synchronization Text for the synchronization. If null, then there won't be any synchronization on the edge
     * @param stackGuard Text for the guard. If null, then there won't be any guard on the edge
     * @param assignment Text for the assignment.  If null, then there won't be any assignmnet on the edge
     * @param mirrored If true, then the new location will be added to the right of the last location.  If false, to the left.
     * @return The new last location is the newly created location
     */
    private Location addHorizontalLocation(Template currentTemplate, Location lastLocation, int[] lastLocationCoords, String name, String synchronization, String stackGuard, String assignment, boolean mirrored) {
        // Both of these variables allow you to easily change where the text is
        // These constants should be extracted todo: extract constants
        int xTextLocation = lastLocationCoords[0] + (mirrored ? -370 : 0) + 20;
        int xTempCoords = lastLocationCoords[0] + (mirrored ? -370 : 370);
        Location lastLocationTemp = makeLocationWithCoordinates(currentTemplate, name, getCounter(), true, false, xTempCoords, 0, getNameLocation(name, xTempCoords), lastLocationCoords[1] - 32);

        makeEdge(currentTemplate, lastLocation, lastLocationTemp, null, null, synchronization, new Integer[]{xTextLocation, lastLocationCoords[1] - (getNumLines(stackGuard, " &&") + 1)*SIZE_OF_TEXT}, stackGuard, new Integer[]{xTextLocation, lastLocationCoords[1] - getNumLines(stackGuard, " &&")*SIZE_OF_TEXT}, assignment, new Integer[]{xTextLocation, lastLocationCoords[1] + 8});
        lastLocationCoords[0] = xTempCoords;
        return lastLocationTemp;
    }

    /**
     * Adds an edge back to the provided location going up and over the other locations
     * @param currentTemplate The current template where the location will be added
     * @param lastLocation The last location where the edge will be coming from and then going to the new location created
     * @param startLocation The start location of the template
     * @param lastLocationCoords The coordinates of the last location. They can also be found with a .getX() and .getY() method from the location but it's a little easier with them stored this way
     * @param guard Text for the guard. If null, then there won't be any guard on the edge
     * @param assignment Text for the assignment.  If null, then there won't be any assignmnet on the edge.  In this case, it also signals if there needs to be a synchronization
     * @param mirrored Changes which nails are placed and what direction the text is moved from the lastLocation
     */
    private void goBackToProvidedLocation(Template currentTemplate, Location lastLocation, Location startLocation, int[] lastLocationCoords, String guard, String assignment, boolean mirrored) {
        Integer[] nails = new Integer[]{lastLocationCoords[0], lastLocationCoords[1] - 110, startLocation.getX(), -110};
        String synchronization;
        if (assignment == null) {
            synchronization = null;
        } else {
            // Note the difference between Halt! and halt
            // Halt! is the signal from at least one production in a Soar agent that halts the other Soar agents
            // halt is for Halt? which is waiting for a halt command and is needed to stop checking the other conditions and assignments because we halted the Soar agent
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
        // These variables move the text around so that it looks good. Guess and check with Uppaal. Modify as needed
        int assignmentSpace = lastLocationCoords[1] - 110 - SIZE_OF_TEXT * (assignment != null && assignment.contains("halt") ? 0 : getNumLines(assignment, ","));
        int textLocationX = lastLocationCoords[0] + (mirrored ? 0 : - 370);
        Integer[] guardLocation = new Integer[]{textLocationX,  assignmentSpace - SIZE_OF_TEXT * getNumLines(guard, " &&")};
        Integer[] assignmentLocation = new Integer[]{textLocationX, assignmentSpace};

        makeEdgeWithNails(currentTemplate, lastLocation, startLocation, null, null, synchronization, new Integer[]{textLocationX, guardLocation[1] - SIZE_OF_TEXT}, guard, guardLocation, assignment, assignmentLocation, nails);
    }

    /**
     * Sets the start location coordinates.  Alter here if you want to the template locations around
     * @param lastLocationCoords Location of the last location. This initializes the first two values to be X and Y values respectively
     */
    private void setLastLocationCoords(int[] lastLocationCoords) {
        lastLocationCoords[0] = -152;
        lastLocationCoords[1] = 0;
    }

    /**
     * Helpful utility for counting how far to move text up or down
     * @param text Text to be analyzed
     * @param lookFor What snippet to look for. Guards have " &&" for each new line to be added. Assignments have " ," for each new line
     * @return The count of how many new lines are in the given text based on the lookFor
     */
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

    /**
     * Makes a String that is all spaces of the length provided
     * @param iterate Number of spaces to return
     * @return A String of spaces of length iterate
     */
    private StringBuilder getSpaces(int iterate) {
        StringBuilder spaces = new StringBuilder();
        for (int i = 0; i < iterate; i++) {
            spaces.append(" ");
        }
        return spaces;
    }

    /**
     * Fills the provided productionBuilders with the elements in the provided lists
     * @param productionBuilders Array of StringBuilders that will contain the conditions and actions of the production
     * @param list_1 List of elements to be added to the first productionBuilder
     * @param list_2 List of elements to be added to the second productionBuilder
     * @param list_3 List of elements to be added to the third productionBuilder
     * @param list_4 List of elements to be added to the fourth productionBuilder
     * @return Offset for text above the production arrays
     */
    private int getArrays(StringBuilder[] productionBuilders, LinkedList<String> list_1, LinkedList<String> list_2, LinkedList<String> list_3, LinkedList<String> list_4) {
        int count = 0;
        if (list_1.size() == count) {
            productionBuilders[0].append("0");
            productionBuilders[1].append("0");
            productionBuilders[2].append("0");
            productionBuilders[3].append("0");
            productionBuilders[4].append("0");

        } else {
            for (int i = 0; i < list_1.size(); i++) {
                String nextIdentifier = list_1.get(i);
                String nextAttribute = list_2.get(i);
                String nextValue = list_3.get(i);
                String nextTemp = list_4.get(i);
                String nextAttributeTemp = _attributeTemps.getFirst();
                _attributeTemps.addLast(_attributeTemps.removeFirst());
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

//    /**
//     * Adds any extra zeroes needed to the arrays and closes their initialization with a closing curly brace
//     * @param productionBuilders Array of StringBuilders containing the conditions and actions of the production.
//     * @param currentTemplateDeclaration StringBuilder that contains the current declaration of the production
//     * @param label Text that indicates where the conditions and actions start
//     * @param productionSize Calculated based on number of conditions and actions
//     */
//    private void addZeroesAndClose(StringBuilder[] productionBuilders, StringBuilder currentTemplateDeclaration, StringBuilder label, int productionSize) {
//        int iterateSize = _maxQuerySize - (conditionProductionIdentifiers.size() + actionProductionIdentifiers.size() + 1);
//        if (actionProductionIdentifiers.size() == 0) {
//            iterateSize--;
//        }
//        for (int i = 0; i < iterateSize; i++) {
//            for (StringBuilder nextProductionBuilder : productionBuilders) {
//                nextProductionBuilder.append(", 0");
//            }
//        }
//
//        currentTemplateDeclaration.append(label).append("\n");
//
//        for (StringBuilder nextProductionArray : productionBuilders) {
//            currentTemplateDeclaration.append(nextProductionArray).append("};\n");
//        }
//        currentTemplateDeclaration.append("\n");
//    }

    /**
     * Gets the static text that sets up the arrays for the conditions and actions of the production
     * @return An array of StringBuilders that contains all of the arrays needed for the production
     */
    private StringBuilder[] getArrayBuilders() {
        StringBuilder operatorArray                 = new StringBuilder("int productionOperatorArray[PRODUCTION_GLOBAL_SIZE]    = {");
        StringBuilder attributeArray                = new StringBuilder("int productionAttributeArray[PRODUCTION_GLOBAL_SIZE]   = {");
        StringBuilder valueArray                    = new StringBuilder("int productionValueArray[PRODUCTION_GLOBAL_SIZE]       = {");
        StringBuilder temporaryAndFunctionArray     = new StringBuilder("int productionTempAndFuncArray[PRODUCTION_GLOBAL_SIZE] = {");
        StringBuilder temporaryAttributeArray       = new StringBuilder("int productionAttributeTemp[PRODUCTION_GLOBAL_SIZE]    = {");
        return new StringBuilder[]{operatorArray, attributeArray, valueArray, temporaryAndFunctionArray, temporaryAttributeArray};
    }

    /**
     * If the size of nextElements is lesss than _maxQuerySize then it adds zeroes until it reaches that size
     * @param nextElements List of elements to add 0s to
     */
    private void fillWithExtraZeroes(LinkedList<String> nextElements) {
        int currentSize = nextElements.size();
        for (int i = currentSize; i < _maxQuerySize; i++) {
            nextElements.add("0");
        }
    }

    /**
     * Static text that includes the copy production method for Uppaal
     * @param currentTemplateDeclaration Builder to add the method to
     */
    private void getCopyProductionMethod(StringBuilder currentTemplateDeclaration) {
        currentTemplateDeclaration.append("void copyProductionArrayToGlobal(int &productionArray[PRODUCTION_GLOBAL_SIZE], int &globalArray[MAX_GLOBAL_SIZE]) {\n");
        currentTemplateDeclaration.append("\tint i;\n");
        currentTemplateDeclaration.append("\tfor (i = 0; i < PRODUCTION_GLOBAL_SIZE; i++) {\n");
        currentTemplateDeclaration.append("\t\tglobalArray[i] = productionArray[i];\n");
        currentTemplateDeclaration.append("\t}\n");
        currentTemplateDeclaration.append("\tfor (i = PRODUCTION_GLOBAL_SIZE; i < MAX_GLOBAL_SIZE - PRODUCTION_GLOBAL_SIZE; i++) {\n");
        currentTemplateDeclaration.append("\t\tglobalArray[i] = 0;\n");
        currentTemplateDeclaration.append("\t}\n");
        currentTemplateDeclaration.append("}\n").append("\n");
    }

    /**
     * Checks each provided value and adds it to the corresponding list if it is a dummy variable and will need to be replaced
     * @param nextIdentifierElements List of the identifiers
     * @param nextAttributeElements List of the attributes
     * @param nextValueElements List of the values
     * @param nextIdentifier Next identifier to check
     * @param nextAttribute Next attribute to check
     * @param nextValue Next value to check
     * @param nextValueTemp Next temporary value to check
     * @param nextAttributeTemp Next temporary attribute to check
     * @param dummyToIndex Map from dummy variable to its location in the production declaration
     * @param index Index in the global sense. Conditions will provide 0. Assignments have an offset by the number of conditions plus one
     */
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

    /**
     * Gets all of the assignments needed to retrieve a stored set of variables to the different arrays
     * @param nextIdentifierElements List of the identifiers
     * @param nextAttributeElements List of the attributes
     * @param nextValueElements List of the values
     * @param dummyToIndex Map from dummy variable to its location in the production declaration
     */
    private void getNextProductionArray(LinkedList<String> nextIdentifierElements, LinkedList<String> nextAttributeElements, LinkedList<String> nextValueElements, Map<String, Integer> dummyToIndex) {
        for (int i = 0; i < _conditionProductionIdentifiers.size(); i++) {
            getNextElement(nextIdentifierElements, nextAttributeElements, nextValueElements, _conditionProductionIdentifiers.get(i), _conditionProductionAttributes.get(i), _conditionProductionValues.get(i), _conditionProductionTemp.get(i), _attributeTemps.get(i), dummyToIndex, i);
        }
//        nextIdentifierElements.add("0");
//        nextAttributeElements.add("0");
//        nextValueElements.add("0");
        int buffer = _conditionProductionIdentifiers.size();
        for (int i = 0; i < _actionProductionIdentifiers.size(); i++) {
            getNextElement(nextIdentifierElements, nextAttributeElements, nextValueElements, _actionProductionIdentifiers.get(i), _actionProductionAttributes.get(i), _actionProductionValues.get(i), _actionProductionFunctions.get(i), _attributeTemps.get(i + buffer), dummyToIndex, i + buffer + 1);
        }
//        fillWithExtraZeroes(nextIdentifierElements);
//        fillWithExtraZeroes(nextAttributeElements);
//        fillWithExtraZeroes(nextValueElements);
    }

    /**
     * Sets up the declaration for each production. Needs to be called after the visits to the condition and action side of the production at least.
     * @param productionName Name of the production
     * @param operatorIndexes Set of the operator indexes that are accessed in this production
     * @param dummyToIndex Map from dummy variable to its location in the production declaration. Used later for correct
     *                     indexing by the storage and retrieval of dummy variables
     * @return The production's declaration
     */
    private String getProductionDeclaration(String productionName, Set<String> operatorIndexes, Map<String, Integer> dummyToIndex) {
        StringBuilder currentTemplateDeclaration = new StringBuilder();
        int currentLatestNum = _latestNum;
        for (String dummyVariable : _conditionSideVariablesToTemps.values()) {
            addConstantToBuilder(currentTemplateDeclaration, dummyVariable, currentLatestNum);
            dummyToIndex.put(dummyVariable, currentLatestNum);
            currentLatestNum++;
        }
        for (String dummyVariable : _attributesToTemps.values()) {
            addConstantToBuilder(currentTemplateDeclaration, dummyVariable, currentLatestNum);
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

        int productionSize = _productionToProductionSize.get(productionName) + 1;
        addConstantToBuilder(currentTemplateDeclaration, "PRODUCTION_GLOBAL_SIZE", productionSize);

        StringBuilder[] productionArrays = getArrayBuilders();
        String startingSpaces = "                                                   ";

        int extraSpaces = getArrays(productionArrays, _conditionProductionIdentifiers, _conditionProductionAttributes, _conditionProductionValues, _conditionProductionTemp);

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

        getArrays(productionArrays, _actionProductionIdentifiers, _actionProductionAttributes, _actionProductionValues, _actionProductionFunctions);

//        addZeroesAndClose(productionArrays, currentTemplateDeclaration, label, productionSize);
        currentTemplateDeclaration.append(label).append("\n");

        for (int i = _conditionProductionIdentifiers.size() + 2 + _actionProductionIdentifiers.size(); i < productionSize; i++) {
            for (StringBuilder builder : productionArrays) {
                builder.append(", 0");
            }
        }
        for (StringBuilder nextProductionArray : productionArrays) {
            currentTemplateDeclaration.append(nextProductionArray).append("};\n");
        }
        currentTemplateDeclaration.append("\n");
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

        getCopyProductionMethod(currentTemplateDeclaration);

//        currentTemplateDeclaration.append("void setOperatorArray() {\n");
//        currentTemplateDeclaration.append("\tint nextArray [MAX_GLOBAL_SIZE] = {");
//        currentTemplateDeclaration.append(nextIdentifierElements.stream().collect(Collectors.joining(", ")));
//        currentTemplateDeclaration.append("};\n").append("\toperatorArray = nextArray;\n").append("}\n").append("\n");

        currentTemplateDeclaration.append("void setArraysToSavedValues(int index) {\n");
        currentTemplateDeclaration.append("\tcopyProductionArrayToGlobal(productionOperatorArray, operatorArray);\n");
        for (String operatorSet : nextIdentifierElements) {
            currentTemplateDeclaration.append("\t").append(operatorSet).append(";\n");
        }
        currentTemplateDeclaration.append("\tcopyProductionArrayToGlobal(productionAttributeArray, attributeArray);\n");
        for (String attributeSet : nextAttributeElements) {
            currentTemplateDeclaration.append("\t").append(attributeSet).append(";\n");
        }
        currentTemplateDeclaration.append("\tcopyProductionArrayToGlobal(productionValueArray, valueArray);\n");
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
            for (int i = 0; i < _conditionProductionIdentifiers.size(); i++) {
                newFunctionArray.append(", 0");
            }
            for (int i = 0; i < _actionProductionIdentifiers.size(); i++) {
                newFunctionArray.append(", remove");
            }
            int currentSize = 1 + _conditionProductionIdentifiers.size() + _actionProductionIdentifiers.size();
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
                    currentTemplateDeclaration.append("selectedFinalOperatorIndex == ").append((Integer.parseInt(nextOperatorIndex) + 1));
//                    String operatorName = "state_operator_" + (Integer.parseInt(nextOperatorIndex) + 1);
//                    int index = _globals.size();
//                    for (String possibleOperator : _uppaalOperatorCollection) {
//                        if (operatorName.equals(possibleOperator)) {
//                            break;
//                        }
//                        index++;
//                    }
//                    currentTemplateDeclaration.append(index);
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

        String attributeArray = "copyProductionArrayToGlobal(productionAttributeArray, attributeArray)" + commaNext;
        if (isCondition) {
            if (isRetract) {
//                builder.append("setOperatorArray()").append(commaNext);
//                builder.append("attributeArray = productions[productionIndexTemp].savedAttributeTemp").append(commaNext);
//                builder.append("valueArray = productions[productionIndexTemp].savedTempAndFunction").append(commaNext);
                builder.append("setArraysToSavedValues(productionIndexTemp)").append(commaNext);
            } else {
                builder.append("copyProductionArrayToGlobal(productionOperatorArray, operatorArray)").append(commaNext);
                builder.append(attributeArray);
                builder.append("copyProductionArrayToGlobal(productionValueArray, valueArray)").append(commaNext);
                builder.append("copyProductionArrayToGlobal(productionAttributeTemp, attributeTempArray)").append(commaNext);
                builder.append("checkMatches = true").append(commaNext);
                builder.append("dummyArray = dummyArrayDefault").append(commaNext);
            }
            builder.append("copyProductionArrayToGlobal(productionTempAndFuncArray, tempOrFuncArray)").append(commaNext);
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
                builder.append("copyProductionArrayToGlobal(productionAttributeTemp, attributeTempArray)").append(commaNext);
                builder.append("copyProductionArrayToGlobal(productionTempAndFuncArray, tempOrFuncArray)");
                if (operatorAssignments.length() > 0) {
                    builder.append(commaNext).append(operatorAssignments);
                }
            }
        }

        return builder.toString();
    }

    /**
     * Adds boolean values indicating which of the flags that the production has. Unfortunately, you can't loop through the possibilities so _flags is a mapping
     * @param ctx Text following the ":" in the production which indicates which flags it has
     */
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

    /**
     * Loops through provided LinkedList to add all found indexes to the provided set
     * @param loopArray List to loop through to find indexes where value occurs
     * @param value Value to be found in the loopArray
     * @param foundIndexes Set of indexes where value occurs in loopArray
     * @param index Index where we are in the global list.  Conditions provide 0. Actions provide the length of conditions
     *              plus 1 for a buffer
     */
    private void loopThroughValues(LinkedList<String> loopArray, String value, HashSet<Integer> foundIndexes, int index) {
        for (String nextValue : loopArray) {
            if (nextValue.equals(value)) {
                foundIndexes.add(index);
            }
            index++;
        }
    }

    /**
     * Loops through the conditions and actions to find all of the temporaries for identifiers, attributes, and values
     * and the indices where they are used
     * @param tempMap Map from variable name its temporary value
     * @param tempVariableToModifiedIndexes Map from production to mapping from variable to its set of indices where it is used
     */
    private void loopThroughTemp(Map<String, String> tempMap, Map<String, Map<String, HashSet<Integer>>> tempVariableToModifiedIndexes) {
        Map<String, HashSet<Integer>> allModifiedIndexes;
        HashSet<Integer> tempSet;
        for (String nextTempVariable :  tempMap.values()) {
            allModifiedIndexes = new HashMap<>();
            tempSet = new HashSet<>();
            loopThroughValues(_conditionProductionIdentifiers, nextTempVariable, tempSet, 0);
            loopThroughValues(_actionProductionIdentifiers, nextTempVariable, tempSet, _conditionProductionIdentifiers.size() + 1);
            if (tempSet.size() > 0) {
                allModifiedIndexes.put("operatorArray", tempSet);
            }
            tempSet = new HashSet<>();
            loopThroughValues(_conditionProductionAttributes, nextTempVariable, tempSet, 0);
            loopThroughValues(_actionProductionAttributes, nextTempVariable, tempSet, _conditionProductionIdentifiers.size() + 1);
            if (tempSet.size() > 0) {
                allModifiedIndexes.put("attributeArray", tempSet);
            }
            tempSet = new HashSet<>();
            loopThroughValues(_conditionProductionValues, nextTempVariable, tempSet, 0);
            loopThroughValues(_actionProductionValues, nextTempVariable, tempSet, _conditionProductionIdentifiers.size() + 1);
            if (tempSet.size() > 0) {
                allModifiedIndexes.put("valueArray", tempSet);
            }
            allModifiedIndexes.put("extraForDummy", new HashSet<>());
            tempVariableToModifiedIndexes.put(nextTempVariable, allModifiedIndexes);
        }
    }

    /**
     * Finds the Set of indices that have temporary variables
     * @param tempVariableToModifiedIndexes Map from production to mapping from variable to its set of indices where it is used
     */
    private void findWhereTempVariablesAreUsed(Map<String, Map<String, HashSet<Integer>>> tempVariableToModifiedIndexes) {
        loopThroughTemp(_conditionSideVariablesToTemps, tempVariableToModifiedIndexes);
        loopThroughTemp(_attributesToTemps, tempVariableToModifiedIndexes);
    }

    /**
     * Visits the condition and action side of the production to fill the global variables
     * Also creates the declaration, locations, and edges in the Uppaal document for the template corresponding to the production
     * @param ctx Individual production
     * @return Null
     */
    @Override
    public Node visitSoar_production(SoarParser.Soar_productionContext ctx) {
        _productionVariables = new HashMap<>();
        _conditionSideVariablesToTemps = new HashMap<>();
        _conditionProductionIdentifiers = new LinkedList<>();
        _conditionProductionAttributes = new LinkedList<>();
        _conditionProductionValues = new LinkedList<>();
        _conditionProductionTemp = new LinkedList<>();
        _actionProductionIdentifiers = new LinkedList<>();
        _actionProductionAttributes = new LinkedList<>();
        _actionProductionValues = new LinkedList<>();
        _actionProductionFunctions = new LinkedList<>();
        _attributesToTemps = new HashMap<>();
        _attributeTemps = new LinkedList<>();
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
        // This can probably can be done while the condition and action side of the production are being visited. I collect the different indexes used in the operatorAssignments
        // so I can add the corresponding retracting operator assignments later on
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
                    lookIndex = endIndex;
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
            // This section adds the left branch off the Start location. For retraction, it mirrors the conditions and actions on the right side
            // For non retraction, it just adds an edge off to the left
            // To follow which location is which, follow the methods which add different locations horizontally and look at the Names of the locations
            if (needsRetraction) {
                lastLocation = addHorizontalLocation(currentTemplate, startLocation, lastLocationCoords, "Run_Retract", "Run_Rule?", "isRetracting", "addToStackRetract(" + _templateIndex + "),\nproductionIndexTemp = 0", true);
                Location runRetractLocation = lastLocation;

                goBackToProvidedLocation(currentTemplate, lastLocation, startLocation, lastLocationCoords, "stackRetract[stackRetractIndex] == " + _templateIndex + " &&\nproductionIndexTemp == productionIndex", "productionIndexTemp = 0,\nremoveStackRetract()", true);

                nextAssignment = getConditionOrAssignment(_conditionProductionIdentifiers.size() + "", 0, "checkContains = true", true, "", false, operatorIndexes);
                lastLocation = addHorizontalLocation(currentTemplate, lastLocation, lastLocationCoords, null, null, "productionIndexTemp != productionIndex &&\nstackRetract[stackRetractIndex] == " + _templateIndex, nextAssignment, true);

                goBackToProvidedLocation(currentTemplate, lastLocation, runRetractLocation, lastLocationCoords, "!checkContains &&\ndoesContainArray == doesContainTrue", "productionIndexTemp++", true);

                nextAssignment = getConditionOrAssignment((_actionProductionIdentifiers.size() + _conditionProductionIdentifiers.size() + 1) + "", _conditionProductionIdentifiers.size() + 1, "addOperator = true", true, operatorAssignments, false, operatorIndexes);
                lastLocation = addHorizontalLocation(currentTemplate, lastLocation, lastLocationCoords, "Run_Retract_Assignments", null, "!checkContains &&\ndoesContainArray != doesContainTrue", nextAssignment, true);

                nextAssignment = getConditionOrAssignment("nestedCheckIndex", 0, "removeOperator = true", true, "", false, operatorIndexes);
                lastLocation = addHorizontalLocation(currentTemplate, lastLocation, lastLocationCoords, "Run_Remove_Attributes", null, "!addOperator", nextAssignment, true);

                goBackToProvidedLocation(currentTemplate, lastLocation, runRetractLocation, lastLocationCoords, "!removeOperator &&\ncurrentNumAttributes == 0", "productionIndex--", true);
            } else {
                makeEdgeWithNails(currentTemplate, startLocation, startLocation, null, null, "Run_Rule?", new Integer[]{lastLocationCoords[0] + SIZE_OF_TEXT, lastLocationCoords[1] + SIZE_OF_TEXT*2}, "!productionFired &&\nisRetracting", new Integer[]{lastLocationCoords[0] + SIZE_OF_TEXT, lastLocationCoords[1] + SIZE_OF_TEXT*3}, "currentNumFiringPerCycle = 0", new Integer[]{lastLocationCoords[0] + SIZE_OF_TEXT, lastLocationCoords[1] + SIZE_OF_TEXT*5}, new Integer[]{lastLocationCoords[0], lastLocationCoords[1] + SIZE_OF_TEXT*5});
            }
        }
        // Restores the lastLocationCoords to the start location. If you move the start location, change the constants in this method. Or better yet, hook them up together
        setLastLocationCoords(lastLocationCoords);

        lastLocation = addHorizontalLocation(currentTemplate, startLocation, lastLocationCoords, "Run_Guard", "Run_Rule?", "!isRetracting &&\n" + (needsRetraction ? "productionIndex != 1" : "currentNumFiringPerCycle != numFiringPerCycle"), "addToStackCondition(" + _templateIndex + ")", false);

        goBackToProvidedLocation(currentTemplate, lastLocation, startLocation, lastLocationCoords, null, "halt", false);

        nextAssignment = getConditionOrAssignment(_conditionProductionIdentifiers.size() + "", 0, "checkContains = true", false, "", false, operatorIndexes);
        lastLocation = addHorizontalLocation(currentTemplate, lastLocation, lastLocationCoords, null, null, "stackCondition[stackConditionIndex] == " + _templateIndex + " &&\n!addOperator", nextAssignment, false);

        goBackToProvidedLocation(currentTemplate, lastLocation, startLocation, lastLocationCoords, "!checkMatches &&\ndoesContainArray != doesContainTrue", "removeStackCondition()", false);

        makeEdgeWithNails(currentTemplate, lastLocation, lastLocation, null, null, null, null, "!checkContains &&\ncheckMatches", new Integer[]{lastLocationCoords[0] + SIZE_OF_TEXT, lastLocationCoords[1] + SIZE_OF_TEXT*9}, "checkProductionsContain()", new Integer[]{lastLocationCoords[0] + SIZE_OF_TEXT, lastLocationCoords[1] + SIZE_OF_TEXT*10}, new Integer[]{lastLocationCoords[0], lastLocationCoords[1] + SIZE_OF_TEXT*10});

        lastLocation = addHorizontalLocation(currentTemplate, lastLocation, lastLocationCoords, "Run_Assignment", null, "!checkMatches &&\ndoesContainArray == doesContainTrue", "removeStackCondition(),\naddToStackAction(" + _templateIndex + "),\nproductionFired = true,\nfillNextProduction()", false);

        nextAssignment = getConditionOrAssignment((_actionProductionIdentifiers.size() + _conditionProductionIdentifiers.size() + 1) + "", _conditionProductionIdentifiers.size() + 1, "addOperator = true", false, operatorAssignments, false, operatorIndexes);
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

    /**
     * Does exactly what the non overridden version would do, but returns null
     * @param ctx Condition side of the production
     * @return Null
     */
    @Override
    public Node visitCondition_side(SoarParser.Condition_sideContext ctx) {
        ctx.state_imp_cond().accept(this);
        ctx.cond().forEach(cond -> cond.accept(this));
        return null;
    }

    /**
     * Utility function that generates a new node and gives it the provided property with the provided value
     * @param property Property that the new node should get
     * @param text Value for the property
     * @return The newly generated Node
     */
    private Node textAsNode(String property, String text) {
        Node node = generateNode();
        node.setProperty(property, text);
        return node;
    }

    /**
     * Gets the value of the provided property from the provided Node.
     * @param accept Node from which the property should be retrieved
     * @param property Property that should be retrieved
     * @return Value of the property from the accept Node
     */
    private String getText(Node accept, String property) {
        return (String) accept.getProperty(property).getValue();
    }

    /**
     * Creates a new template in the global Document
     * @return The newly generated Template which is a Node
     */
    private Node generateNode() {
        return ourDocument.createTemplate();
    }

    /**
     * Visits the state condition using the utility method innerConditionVisit which is shared with the other conditions
     * @param ctx State condition of production
     * @return Null
     */
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

    /**
     * Retrieves the variable from inside a conjunctive test because it can be anywhere in the test
     * @param ctx The conjunctive test
     * @return The variable that the test will bind to
     */
    private String getVariableFromConjunctive(SoarParser.Conjunctive_testContext ctx) {
        String variable = null;
        for (SoarParser.Simple_testContext simple_testContext : ctx.simple_test()) {
            if (simple_testContext.relational_test() != null && simple_testContext.relational_test().relation() == null) {
                variable = simple_testContext.relational_test().single_test().variable().getText();
                break;
            }
        }
        return variable;
    }

    /**
     * Main method for processing a condition. Utility used by all of the conditions
     * @param attrValueTestsCtxs List of all the attribute value tests
     * @param localVariableDictionary Map from variable to its path
     * @param idTest Identifier for the condition
     * @param localActualVariables Keeps track of which variables that are found are actually variables and which are later identifiers
     * @param attributeVariableToArrayName Map from a variable (attribute) to the name of the noneBut array that contains the values that it has to match
     */
    private void innerConditionVisit(List<SoarParser.Attr_value_testsContext> attrValueTestsCtxs, Map<String, String> localVariableDictionary, String idTest, ProductionVariables localActualVariables, Map<String, String> attributeVariableToArrayName) {
        // Variable in left hand side
        if (localVariableDictionary.containsKey(idTest)) {
            // Build the comparisons
            for (SoarParser.Attr_value_testsContext attributeCtx : attrValueTestsCtxs) {

                String lastVariable;
                if (localVariableDictionary.get(idTest).equals("state")) {
                    lastVariable = "_state";
                } else {
                    lastVariable = _conditionSideVariablesToTemps.get(idTest);
                }

                // This hasn't been fully tested. It likely is currently broken.  It is used when you have attribute.attribute.attribute etc.
                // For each of them, you need a new condition that connects them all
                // todo: Fully test this to make sure it works
                for (int i = 0; i < attributeCtx.attr_test().size() - 1; i++) {
                    String attributeText = attributeCtx.attr_test(i).getText();
                    _conditionProductionIdentifiers.add(attributeText.equals("operator") ? "finalOp" : lastVariable);
                    _conditionProductionAttributes.add(attributeText);
                    _conditionProductionValues.add("nilAnything");
                    String withoutTempVariable = lastVariable + "_" + attributeText;
                    String dummyVariable = "dummy" + (withoutTempVariable.charAt(0) != '_' ? "_" : "") + withoutTempVariable;
                    _conditionProductionTemp.add(dummyVariable);
                    String newTempVariable = withoutTempVariable + "_temp";
                    _productionVariables.put(dummyVariable, newTempVariable);
                    _conditionSideVariablesToTemps.put(dummyVariable, dummyVariable);
                    lastVariable = dummyVariable;
                    _attributeTemps.add("0");
                }

                String attrPath = attributeCtx.attr_test(attributeCtx.attr_test().size() - 1).getText();
                String dummyValue = _conditionSideVariablesToTemps.get(attrPath);
                if (dummyValue != null) {
                    attrPath = dummyValue;
                } else if (attributeCtx.attr_test(attributeCtx.attr_test().size() - 1).test().conjunctive_test() != null) {
                    attrPath = getVariableFromConjunctive(attributeCtx.attr_test(attributeCtx.attr_test().size() - 1).test().conjunctive_test());
                    if (_attributesToTemps.get(attrPath) == null) {
                        String dummy = "dummy_state_" + SoarTranslator.simplifiedString(attrPath);
                        _attributesToTemps.put(attrPath, dummy);
                    }
                    _attributeTemps.add(0, _attributesToTemps.get(attrPath));
                    _conditionProductionIdentifiers.add(0, "0");
                    _conditionProductionAttributes.add(0, attributeVariableToArrayName.get(attrPath));
                    _conditionProductionValues.add(0, "-1");
                    _conditionProductionTemp.add(0, "0");
                    _latestIndex++;

                    attrPath = _attributesToTemps.get(attrPath);
                } else if (_attributesToTemps.get(attrPath) != null) {
                    attrPath = _attributesToTemps.get(attrPath);
                } else {
                    attrPath = SoarTranslator.simplifiedString(attrPath);
                }

                _conditionProductionIdentifiers.add(_flags.get("chunk") || !attrPath.equals("operator") ? lastVariable : "finalOp");
                _conditionProductionAttributes.add(attrPath);
                if (_attributeTemps.size() < _conditionProductionIdentifiers.size()) {
                    _attributeTemps.add("0");
                }

                String value;

                if (attributeCtx.getText().startsWith("-^")) {
                    _conditionProductionValues.add("EMPTY");
                    _conditionProductionTemp.add("0");
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
                                if (_conditionSideVariablesToTemps.get(rightTerm) == null) {
                                    value = "nilAnything";
                                    String withoutTempVariable = SoarTranslator.simplifiedString(localVariableDictionary.get(rightTerm) + "_" + rightTerm);
                                    String dummyVariable = "dummy_" + withoutTempVariable;
                                    _conditionSideVariablesToTemps.put(rightTerm, dummyVariable);
                                    _conditionProductionTemp.add(dummyVariable);
                                    if (localActualVariables.variablesContains(rightTerm)) {
                                        String newTempVariable = withoutTempVariable + "_temp";
                                        _productionVariables.put(rightTerm, newTempVariable);
                                    }
                                } else {
                                    value = _conditionSideVariablesToTemps.get(rightTerm);
                                }
                            } else {
                                rightTerm = getText(relationAndRightTerm, "const");
                                value = SoarTranslator.simplifiedString(rightTerm);
                            }

                            if (value.length() > 0) {
                                // At the moment, the selection of the nilAnythings are prioritized to the front
                                // The order that the conditions can be optimized so that they don't have to be tested as much
                                // todo: Optimize the order that the conditions are checked
                                if (value.equals("nilAnything")) {
                                    _conditionProductionValues.add(_latestIndex, value);
                                    _conditionProductionIdentifiers.add(_latestIndex, _conditionProductionIdentifiers.removeLast());
                                    _conditionProductionAttributes.add(_latestIndex, _conditionProductionAttributes.removeLast());
                                    _conditionProductionTemp.add(_latestIndex, _conditionProductionTemp.removeLast());
                                    _attributeTemps.add(_latestIndex, _attributeTemps.removeLast());
                                    _latestIndex++;
                                } else {
                                    _conditionProductionValues.add(value);
                                    _conditionProductionTemp.add("0");
                                }
                                if (relations != null) {
                                    String identifier = _conditionProductionTemp.get(_latestIndex - 1);
                                    for(int i = 0; i < relations.length; i++) {
                                        _conditionProductionIdentifiers.add(_latestIndex, identifier);
                                        _conditionProductionAttributes.add(_latestIndex, "extraRestriction");
                                        _conditionProductionValues.add(_latestIndex, variablesForRelations[i]);
                                        _conditionProductionTemp.add(_latestIndex, relations[i]);
                                        _attributeTemps.add(_latestIndex, "0");
                                        _latestIndex++;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /**
     * Does what the non overridden one does right now.  This will need to be expanded to handle larger negated groups of conditions
     * @param ctx Condition on the condition side of the production
     * @return The result of visiting the positive condition
     */
    @Override
    public Node visitCond(SoarParser.CondContext ctx) {
        return ctx.positive_cond().accept(this);
    }

    /**
     * Visits the condition with one id. Ignores conjunctive groups of conditions at the moment
     * @param ctx Either a conjunctive group of conditions or one condition for one id
     * @return The result from visiting conds for one id
     */
    @Override
    public Node visitPositive_cond(SoarParser.Positive_condContext ctx) {
        return ctx.conds_for_one_id().accept(this);
    }

    /**
     * Mirror image of state implicit condition. For each condition it uses the utility function innerConditionVisit
     * @param ctx Condition on the condition side of a production
     * @return Null
     */
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

    /**
     * Don't want to do any visiting with this component yet so it just returns null
     * @param ctx Identifier for a condition
     * @return Null
     */
    @Override
    public Node visitId_test(SoarParser.Id_testContext ctx) {
        return null;
    }

    /**
     * Don't want to do any visiting with this component yet so it just returns null.
     * This would do what innerConditionVisit does, but you can pass arguments to innerConditionVisit and you can't here
     * @param ctx Attributes and vlues
     * @return Null
     */
    @Override
    public Node visitAttr_value_tests(SoarParser.Attr_value_testsContext ctx) {
        return null;
    }

    /**
     * Don't want to do any visiting with this component yet so it just returns null
     * @param ctx Test
     * @return Null
     */
    @Override
    public Node visitAttr_test(SoarParser.Attr_testContext ctx) {
        return null;
    }

    /**
     * Just visits whichever child is in there. There will only ever be one child
     * @param ctx Test or condition for one id
     * @return The result from visiting the child
     */
    @Override
    public Node visitValue_test(SoarParser.Value_testContext ctx) {
        return ctx.children.get(0).accept(this);
    }

    /**
     * A test is one of three options: conjunctive_test | simple_test | multi_value_test so it visits whichever is there
     * @param ctx Either conjunctive_test, simple_test, or multi_value_test
     * @return The result from visiting the children
     */
    @Override
    public Node visitTest(SoarParser.TestContext ctx) {
        return ctx.children.get(0).accept(this);
    }

    /**
     * Implemented for the use with attribute conjunctive tests and probably value conjunctive tests. This would need to be expanded before use with conjunctive groups of conditions
     * @param ctx Group of simple tests
     * @return Node with the lower components added
     */
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

    /**
     * Visits its child either a disjunction_test or a relational_test
     * @param ctx Disjunction test or relational test
     * @return The result of visiting its child
     */
    @Override
    public Node visitSimple_test(SoarParser.Simple_testContext ctx) {
        return ctx.children.get(0).accept(this);
    }

    /**
     * Not implemented yet so it returns null
     * @param ctx Group of int constants
     * @return Null
     */
    @Override
    public Node visitMulti_value_test(SoarParser.Multi_value_testContext ctx) {
        return null;
    }

    /**
     * SymbolVisitor takes care of this method right now so it doesn't need to do anything in this class
     * @param ctx Group of constants that a variable must match to at least one of
     * @return Null
     */
    @Override
    public Node visitDisjunction_test(SoarParser.Disjunction_testContext ctx) {
        return null;
    }

    /**
     * Visits children which are the single_test and optional relation
     * @param ctx Value (simple_test) with an optional relation
     * @return A Node that contains the properties from the lower visits
     */
    @Override
    public Node visitRelational_test(SoarParser.Relational_testContext ctx) {
        Node relationNode = ctx.single_test().accept(this);

        if (ctx.relation() != null) {
            relationNode.setProperty("rel", getText(ctx.relation().accept(this), "rel"));
        }
        return relationNode;
    }

    /**
     * Uses relationToText from UtilityForVisitors to get the String representation of the relation and sets it as a property of the return Node
     * @param ctx Relation
     * @return A Node with relation under "rel" property
     */
    @Override
    public Node visitRelation(SoarParser.RelationContext ctx) {

        String relationText = UtilityForVisitors.relationToText(ctx.getText());
        Node returnTree = generateNode();
        if (relationText != null) {
            returnTree.setProperty("rel", relationText);
        }
        return returnTree;
    }

    /**
     * Visits its child either a variable or a constant
     * @param ctx Either a variable or constant
     * @return The result of visiting its child
     */
    @Override
    public Node visitSingle_test(SoarParser.Single_testContext ctx) {
        return ctx.children.get(0).accept(this);
    }

    /**
     * Sets the text of the variable under "var"
     * @param ctx The variable
     * @return A new node with the variable under "var" property
     */
    @Override
    public Node visitVariable(SoarParser.VariableContext ctx) {
        return textAsNode("var", ctx.getText());
    }

    /**
     * Simplifies and stores the constant under "const" property
     * @param ctx Constant
     * @return A Node with the constant under "const" property
     */
    @Override
    public Node visitConstant(SoarParser.ConstantContext ctx) {
        String result = SoarTranslator.simplifiedString(ctx.getText());

        if (ctx.Print_string() != null) {
            result = LITERAL_STRING_PREFIX + ctx.Print_string().getText().split("|")[1];
        }
        return textAsNode("const", result);
    }

    /**
     * Collects together all of the operatorAssignments and visits the individual actions
     * @param ctx Action side of the production
     * @return A Node with the operatorAssignments under "operatorAssignments" property and whether the production calls halt under "hasHalt"
     */
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

    /**
     * Retrieves information from the global variables and uses innerVisitAction
     * @param ctx Action on the action side of the production
     * @return Any of the operatorAssignments found in the innerVisitAction
     */
    @Override
    public Node visitAction(SoarParser.ActionContext ctx) {
        String productionName = ((SoarParser.Soar_productionContext) ctx.parent.parent).sym_constant().getText();
        Map<String, String> localVariablePathsWithID = _variablesToPathWithID.get(productionName);
        String variableName = ctx.variable().getText();

        String operatorCollection = innerVisitAction(ctx.attr_value_make(), variableName, localVariablePathsWithID);
        Node returnNode = textAsNode("operatorAssignments", operatorCollection);
        return returnNode;
    }

    /**
     * Visits and separates the components of the actions
     * @param ctxs The attribute and values of the actions
     * @param variableName Name of the identifier
     * @param localVariablePathsWithID Map from variable name to path with ID
     * @return The operator assignments found during the method
     */
    private String innerVisitAction(List<SoarParser.Attr_value_makeContext> ctxs, String variableName, Map<String, String> localVariablePathsWithID) {
        LinkedList<String> operatorCollection = new LinkedList<>();
        String variable = _conditionSideVariablesToTemps.get(variableName);
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
            // Doesn't handle the "." notation yet
            String attribute = attrCtx.variable_or_sym_constant(attrCtx.variable_or_sym_constant().size() - 1).getText();
            if (_attributesToTemps.get(attribute) != null) {
                attribute = _attributesToTemps.get(attribute);
            } else {
                attribute = SoarTranslator.simplifiedString(attribute);
            }

            for (SoarParser.Value_makeContext value_makeContext : attrCtx.value_make()) {
                _actionProductionIdentifiers.add(variable);
                _actionProductionAttributes.add(attribute);
                _attributeTemps.add("0");

                Node rightSideElement = value_makeContext.accept(this);
                String rightSide = determineAssignment(rightSideElement, localVariablePathsWithID);
                if (rightSideElement.getProperty("expr") != null) {
                    _actionProductionIdentifiers.add("0");
                    _actionProductionAttributes.add("0");
                    _actionProductionValues.add(getText(rightSideElement, "secondValue"));
                    _actionProductionFunctions.add("0");
                    _attributeTemps.add("0");
                }

                if (rightSide != null) {
                    operatorCollection.add(rightSide);
                }
            }
        }

        return operatorCollection.stream().collect(Collectors.joining(",\n"));
    }

    /**
     * Gets the assignment needed to retrieve the value of the dummy variable from the last saved production
     * @param match Index for array inside saved production
     * @return Assignment needed to retrieve the value of the dummy variable at the provided index from the last saved production
     */
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

    /**
     * Returns either the index if it is a number already or the method call with the index to get the number during run time of Uppaal
     * @param index Index to be checked
     * @return The index that Uppaal will use
     */
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

    /**
     * Accesses the operator related to the index provided and accesses the provided parameter
     * @param index Index of the operator to be accessed
     * @param parameter Component of the operator to be accessed
     * @return Concatenated String with the default way to access the operator and parameter
     */
    private String operatorBaseString(String index, String parameter) {
        StringBuilder returnString = new StringBuilder();
        returnString.append("operators[");
        returnString.append(getOperatorId(index));
        returnString.append("].operator.");

        returnString.append(parameter);
        return returnString.toString();
    }

    /**
     * Cycles the lists to prioritize removing memory elements before adding new ones
     */
    private void shiftLists() {
        _actionProductionIdentifiers.addFirst(_actionProductionIdentifiers.removeLast());
        _actionProductionAttributes.addFirst(_actionProductionAttributes.removeLast());
        _actionProductionValues.addFirst(_actionProductionValues.removeLast());
        _actionProductionFunctions.addFirst(_actionProductionFunctions.removeLast());
    }

    /**
     * Gets variable from temporary variables or its path in the local map
     * @param text The variable to be found
     * @param localVariablePathsWithID Map from variable to its path with ID
     * @return Dummy variable or the provided variables path
     */
    private String getVariable(String text, Map<String, String> localVariablePathsWithID) {
        String variable = _productionVariables.get(text);
        if (variable == null) {
            variable = localVariablePathsWithID.get(text);
        }
        return variable;
    }

    /**
     * Handles all of the cases that the value can be
     * @param rightSideElement Node returned by visiting the value
     * @param localVariablePathsWithID Map from variable name to path with ID
     * @return Any operator assignments found
     */
    private String determineAssignment(Node rightSideElement, Map<String, String> localVariablePathsWithID) {
        String rightSide = null;
        if (rightSideElement != null) {
            // This is a function
            if (rightSideElement.getProperty("expr") != null) {
                _actionProductionValues.add(getText(rightSideElement, "firstValue"));
                _actionProductionFunctions.add(getText(rightSideElement, "expr"));
            } else if (rightSideElement.getProperty("pref") != null) {
                // The value is being removed from memory
                if (getText(rightSideElement, "pref").equals("remove")) {
                    String rightSideVarOrConst = getText(rightSideElement, "constVarExpr");
                    String variableOrConst;
                    if (rightSideVarOrConst.equals("const")) {
                        variableOrConst = getText(rightSideElement, "const");
                    } else {
                        rightSideVarOrConst = getText(rightSideElement, "var");
                        variableOrConst = _conditionSideVariablesToTemps.get(rightSideVarOrConst);
                        if (variableOrConst == null) {
                            variableOrConst = getVariable(rightSideVarOrConst, localVariablePathsWithID);
                        }
                    }
                    _actionProductionValues.add(variableOrConst);
                    _actionProductionFunctions.add("remove");
                    shiftLists();
                    // The value is an operator with preferences
                } else {
                    String operatorIndex = getIndexFromID(getText(rightSideElement, "var"), localVariablePathsWithID);

                    try {
                        Integer.parseInt(operatorIndex);
                        _actionProductionValues.add(getVariable(getText(rightSideElement, "var"), localVariablePathsWithID));
                    } catch (NumberFormatException e) {
                        _actionProductionIdentifiers.removeLast();
                        _actionProductionAttributes.removeLast();
                        _attributeTemps.removeLast();
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
                //Otherwise, it is a normal constant or variable
            } else if (rightSideElement.getProperty("const") != null) {
                _actionProductionValues.add(getText(rightSideElement, "const"));
            } else if (rightSideElement.getProperty("var") != null) {
                String rightSideVar = getText(rightSideElement, "var");
                String variable = _conditionSideVariablesToTemps.get(rightSideVar);
                if (variable == null) {
                    variable = SoarTranslator.simplifiedString(getVariable(rightSideVar, localVariablePathsWithID));
                }
                _actionProductionValues.add(variable);
            }
        }
        if (_actionProductionFunctions.size() < _actionProductionValues.size()) {
            _actionProductionFunctions.add("0");
        }
        return rightSide;
    }

    /**
     * Generates text for function call in Uppaal. Used for addBetterTo and addUnaryIndifferentTo
     * @param function Name of the function
     * @param index1 Value of the first index
     * @param index2 Value of the second index
     * @return A concatenated String that Uppaal can recognize
     */
    private String functionCallWithTwoIDs(String function, String index1, String index2) {
        return function + "(" + index1 + ", " + index2 + ")";
    }

    /**
     * Uppaal doesn't provide output so right now print strings are ignored. They are helpful in Soar to keep track of where the Soar agent is
     * @param ctx Print String outputted by the Soar agent
     * @return Null
     */
    @Override
    public Node visitPrint(SoarParser.PrintContext ctx) {
        return null;
    }

    /**
     * Gets the constant or dummy variable
     * @param ctx Constant | function call | Variable
     * @return The constant or dummy variable
     */
    private String getVariableOrTemp(SoarParser.ValueContext ctx) {
        StringBuilder variableOrTemp = new StringBuilder();
        if (ctx.variable() == null) {
            variableOrTemp.append(SoarTranslator.simplifiedString(ctx.constant().getText()));
        } else if (_conditionSideVariablesToTemps.get(ctx.variable().getText()) != null) {
            variableOrTemp.append(_conditionSideVariablesToTemps.get(ctx.variable().getText()));
        }
        return variableOrTemp.toString();
    }

    /**
     * Collects the components of the function call to be analyzed above
     * @param ctx Function call with two values and symbol for function
     * @return Node with the name of the function in "expr" property and the two values under the "firstValue" and "secondValue" properties
     */
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

    /**
     * I handled the switch statement in the Func_call. It could probably be moved to this method
     * @param ctx Name of the function
     * @return Null
     */
    @Override
    public Node visitFunc_name(SoarParser.Func_nameContext ctx) {
        return null;
    }

    /**
     * Visits the child which is a constant, variable, or function call and stores an additional component to let the higher components which one it is
     * @param ctx Constant, variable, or function call
     * @return Node with the result of visiting the child along with a property "constVarExpr" which tells you if it is a constant, variable, or function call respecitively
     */
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

    /**
     * Not needed yet since I usually just need the text. Does nothing right now
     * @param ctx Attribute component for actions
     * @return Null
     */
    @Override
    public Node visitVariable_or_sym_constant(SoarParser.Variable_or_sym_constantContext ctx) {
        return null;
    }

    /**
     * Visits the value and any optional preferences that it has
     * @param ctx Value with its preferences if it is an operator
     * @return A Node with the value and its preferences as properties to be analyzed above
     */
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

    /**
     * Collects all the unary preferences together
     * @param ctx Value make context includes value and its preferences
     * @return The collection of unary preferences separated by commas
     */
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

    /**
     * Retrieves either the dummy variable associated with this variable or the index which is attached to the end of the path
     * @param variableName Name of the variable
     * @param localVariablePathsWithID Map from variable to its path with ID
     * @return Index of the variable or its temporary value used by Uppaal
     */
    private String getIndexFromID(String variableName, Map<String, String> localVariablePathsWithID) {
        String pathWithID = localVariablePathsWithID.get(variableName);
        String index;
        if (pathWithID == null) {
            index = _conditionSideVariablesToTemps.get(variableName);
        } else {
            int indexOfLast_ = pathWithID.lastIndexOf("_");
            index = (Integer.parseInt(pathWithID.substring(indexOfLast_ + 1)) - 1) + "";
        }
        return index;
    }

    /**
     * Binary preference with a second value to which the binary preference belongs. I haven't handled commas yet which separate preferences
     * @param ctx Binary preference with second value
     * @return Node with preferences as properties to be analyzed above
     */
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

    /**
     * Uses unaryToString in UtilityForVisitors to retrieve the String equivalent of the preference symbol and adds it as property to be analyzed above
     * @param ctx Unary preference
     * @return Node with the unary preference as a property "unaryPref"
     */
    @Override
    public Node visitUnary_pref(SoarParser.Unary_prefContext ctx) {
        Node prefNode = null;
        String isWhat = UtilityForVisitors.unaryToString(ctx.getText().charAt(0));
        if (isWhat != null) {
            prefNode = textAsNode("unaryPref", isWhat);
        }
        return prefNode;
    }

    /**
     * These symbols can be unary or binary preferences. To know which, I use a global flag and the method unaryOrBinaryToString in UtilityForVisitors
     * @param ctx Unary Or Binary preference
     * @return Node with the unary or binary preference as a property "unaryBinaryPref"
     */
    @Override
    public Node visitUnary_or_binary_pref(SoarParser.Unary_or_binary_prefContext ctx) {
        Node prefNode = null;
        String isWhat = UtilityForVisitors.unaryOrBinaryToString(ctx.getText().charAt(0), _unaryOrBinaryFlag);
        if (isWhat != null) {
            prefNode = textAsNode("unaryBinaryPref", isWhat);
        }
        return prefNode;
    }

    /**
     * The preference found here is a unary preference which is retrieved and stored to be analyzed above
     * @param ctx Unary preference
     * @return A Node with the preference stored as a property "unaryPref"
     */
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

    /**
     * I just use the text so this method doesn't need to do anything
     * @param ctx Combination of letters and numbers
     * @return Null
     */
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

    /**
     * Creates a new Template and stores it in the Document
     * @param name Name of the new Template
     * @return The new Template
     */
    private Template makeTemplate(String name) {
        Template t = ourDocument.createTemplate();
        ourDocument.insert(t, _lastTemplate);
        _lastTemplate = t;
        t.setProperty("name", name);
        return t;
    }

    /**
     * Creates a new location under the provided template with the given name, ID, and with the provided properties
     * @param currentTemplate Template to which the Location is being added
     * @param name Name of the Location to be made
     * @param ID Each location needs a unique ID, this is the ID of the location
     * @param committed If true, makes the location committed
     * @param init If true, marks the Location as the initial location (limit 1 per template)
     * @return The newly created Location
     */
    private Location makeLocation(Template currentTemplate, String name, String ID, boolean committed, boolean init) {
        Location newLocation = currentTemplate.createLocation();
        currentTemplate.insert(newLocation, currentTemplate.getLast());
        if (name != null) {
            newLocation.setProperty("name", name);
        }
        newLocation.setProperty("id", "id" + ID);
        if (committed) {
            newLocation.setProperty("committed", true);
        }
        if (init) {
            newLocation.setProperty("init", true);
        }
        return newLocation;
    }

    /**
     * Creates a new Location with the given coordinates
     * @param currentTemplate Template to which the Location is being added
     * @param name Name of the Location to be made
     * @param ID Each location needs a unique ID, this is the ID of the location
     * @param committed If true, makes the location committed
     * @param init If true, marks the Location as the initial location (limit 1 per template)
     * @param x X coordinate of the Location
     * @param y Y coordinate of the Location
     * @param nameX X coordinate of the name of the Location
     * @param nameY Y coordinate of the name of the Location
     * @return The newly created Location
     */
    private Location makeLocationWithCoordinates(Template currentTemplate, String name, String ID, boolean committed, boolean init, int x, int y, Integer nameX, Integer nameY) {
        Location newLocation = makeLocation(currentTemplate, name, ID, committed, init);
        newLocation.setProperty("x", x);
        newLocation.setProperty("y", y);
        if (nameX != null) {
            Property nameProperty = newLocation.getProperty("name");
            nameProperty.setProperty("x", nameX);
            nameProperty.setProperty("y", nameY);
        }
        return newLocation;
    }

    /**
     * Creates an edge from the source to the target provided Locations with the components provided
     * @param currentTemplate Template to which the Location is being added
     * @param source Location from which the edge with extend
     * @param target Location to which the edge will be directed to
     * @param select Text for the select component of the edge. If null, there won't be any select on the edge
     * @param selectXY Coordinates for the select component of the edge. If select is null, it doesn't matter what is provided here
     * @param synchronisation Text for the synchronisation component of the edge. If null, there won't be any synchronisation on the edge
     * @param synchronisationXY Coordinates for the synchronisation component of the edge. If synchronisation is null, it doesn't matter what is provided here
     * @param guard Text for the guard component of the edge. If null, there won't be any guard on the edge
     * @param guardXY Coordinates for the guard component of the edge. If guard is null, it doesn't matter what is provided here
     * @param assignment Text for the assignmnet component of the edge. If null, there won't be any assignment on the edge
     * @param assignmentXY Coordinates for the assignment component on the edge. If assignment is null, it doesn't matter what is provided here
     * @return The newly created edge
     */
    private Edge makeEdge(Template currentTemplate, Location source, Location target, String select, Integer[] selectXY, String synchronisation, Integer[] synchronisationXY, String guard, Integer[] guardXY, String assignment, Integer[] assignmentXY) {
        Edge newEdge = currentTemplate.createEdge();
        currentTemplate.insert(newEdge, currentTemplate.getLast());
        newEdge.setSource(source);
        newEdge.setTarget(target);
        if (select != null) {
            Property s = newEdge.setProperty("select", select);
            if (selectXY != null && selectXY.length >= 2) {
                s.setProperty("x", selectXY[0]);
                s.setProperty("y", selectXY[1]);
            }
        }
        if (synchronisation != null) {
            Property s = newEdge.setProperty("synchronisation", synchronisation);
            if (synchronisationXY != null && synchronisationXY.length >= 2) {
                s.setProperty("x", synchronisationXY[0]);
                s.setProperty("y", synchronisationXY[1]);
            }
        }
        if (guard != null) {
            Property g = newEdge.setProperty("guard", guard);
            if (guardXY != null && guardXY.length >= 2) {
                g.setProperty("x", guardXY[0]);
                g.setProperty("y", guardXY[1]);
            }
        }
        if (assignment != null) {
            Property a = newEdge.setProperty("assignment", assignment);
            if (assignmentXY != null && assignmentXY.length >= 2) {
                a.setProperty("x", assignmentXY[0]);
                a.setProperty("y", assignmentXY[1]);
            }
        }
        return newEdge;
    }

    /**
     * Creates a new edge with nails at the provided coordinates.  If, for some reason, you call this method with null for the nails then it doesn't add any nails
     * @param currentTemplate Template to which the Location is being added
     * @param source Location from which the edge with extend
     * @param target Location to which the edge will be directed to
     * @param select Text for the select component of the edge. If null, there won't be any select on the edge
     * @param selectXY Coordinates for the select component of the edge. If select is null, it doesn't matter what is provided here
     * @param synchronisation Text for the synchronisation component of the edge. If null, there won't be any synchronisation on the edge
     * @param synchronisationXY Coordinates for the synchronisation component of the edge. If synchronisation is null, it doesn't matter what is provided here
     * @param guard Text for the guard component of the edge. If null, there won't be any guard on the edge
     * @param guardXY Coordinates for the guard component of the edge. If guard is null, it doesn't matter what is provided here
     * @param assignment Text for the assignmnet component of the edge. If null, there won't be any assignment on the edge
     * @param assignmentXY Coordinates for the assignment component on the edge. If assignment is null, it doesn't matter what is provided here
     * @param nailsXY Coordinates for the nails to be added. It is expected that they are given as an array with {X-coordinate-1, Y-coordinate-1, X-coordinate-2, Y-coordinate-2, etc.}
     *                If null, then no nails are added
     * @return
     */
    private Edge makeEdgeWithNails(Template currentTemplate, Location source, Location target, String select, Integer[] selectXY, String synchronisation, Integer[] synchronisationXY, String guard, Integer[] guardXY, String assignment, Integer[] assignmentXY, Integer[] nailsXY) {
        Edge ret = makeEdge(currentTemplate, source, target, select, selectXY, synchronisation, synchronisationXY, guard, guardXY, assignment, assignmentXY);
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

    /**
     * Creates the scheduler, the AV Utility template, and the AV templates
     * @return The AV template
     */
    private Element getScheduler() {
        getRunScheduler();
        getAVUtility();
        return getAttributeValueTemplate();
    }

    /**
     * Gets declaration for the helper templates that only need a few values and don't have big lists of conditions and
     * assignments like the productions
     * @param operator Identifiers that need to be added to the list
     * @param attribute Attributes that need to be added to the list
     * @param value Values that need to be added to the list
     * @return Production declaration
     */
    private String getTinyDeclaration(String[] operator, String[] attribute, String[] value) {
        StringBuilder currentTemplateDeclaration = new StringBuilder();
        _actionProductionIdentifiers = new LinkedList<>();
        _actionProductionAttributes = new LinkedList<>();
        _actionProductionValues = new LinkedList<>();
        _actionProductionFunctions = new LinkedList<>();
        _actionProductionIdentifiers.add(operator[0]);
        _actionProductionAttributes.add(attribute[0]);
        _actionProductionValues.add(value[0]);
        _actionProductionFunctions.add("0");
        int productionSize = 1;
        if (operator.length == 2) {
            _actionProductionIdentifiers.add("0");
            _actionProductionIdentifiers.add(operator[1]);
            _actionProductionAttributes.add("0");
            _actionProductionAttributes.add(attribute[1]);
            for (int i = 0; i < 2; i++) {
                _actionProductionValues.add("0");
                _actionProductionFunctions.add("0");
            }
            productionSize += 2;
        }

        addConstantToBuilder(currentTemplateDeclaration, "PRODUCTION_GLOBAL_SIZE", productionSize);
        _attributeTemps = new LinkedList<>();
        for (int i = 0; i < productionSize; i++) {
            _attributeTemps.add("0");
        }
        StringBuilder[] schedulerBuilders = getArrayBuilders();
        StringBuilder label = new StringBuilder("                                                            //Conditions");
        getArrays(schedulerBuilders, _actionProductionIdentifiers, _actionProductionAttributes, _actionProductionValues, _actionProductionFunctions);
//        int start = operator.length == 1 ? 1 : 3;
//        for (int i = start; i < _maxQuerySize; i++) {
//            for (StringBuilder nextScheduleBuilder : schedulerBuilders) {
//                nextScheduleBuilder.append(", 0");
//            }
//        }
        currentTemplateDeclaration.append(label).append("\n");
        for (StringBuilder nextScheduleBuilder : schedulerBuilders) {
            currentTemplateDeclaration.append(nextScheduleBuilder).append("};\n");
        }
        currentTemplateDeclaration.append("\n");

        getCopyProductionMethod(currentTemplateDeclaration);

        return currentTemplateDeclaration.toString();
    }

    /**
     * Creates scheduler for Uppaal. This is the mirror of Soar's execution cycle and uses a broadcast channel to synchronize the other productions
     * @return The scheduler template
     */
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

        lastLocation = addHorizontalLocation(runScheduler, lastLocation, lastLocationCoords, "Run_Retract", "Run_Rule!", "!halt &&\n!removeOperator", "productionFired = false", false);
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
//        nextAssignment = getConditionOrAssignment("1", 2, "removeOperator = true", false, "", true, null);
        goBackToProvidedLocation(runScheduler, lastLocation, proposalLocation, lastLocationCoords, "!productionFired &&\nstackRetractIndex == -1", "clearFill(required),\nclearFill(acceptable),\nclearFill(best),\nisRetracting = false,\naddToNestedCheckArray(finalOp),\ncurrentNumAttributes = 1,\nglobalIndex = 0,\nremoveOperator = true", false);
        goBackToProvidedLocation(runScheduler, lastLocation, applicationLocation, lastLocationCoords, "productionFired &&\nstackRetractIndex == -1", "isRetracting = false", true);

        return runScheduler;
    }

    /**
     * Adds new AV to the two provided StringBuilders
     * @param AVName Name of the new Attribute Value
     * @param numValues Size of the values array that the new AV has
     * @param identifier The identifier associated with the values in this new AV
     * @param attribute The attribute associated with the values in this new AV
     * @param system StringBuilder for the system declarations
     * @param instantiationsCollection StringBuilder for the instantiations of the AVs
     */
    private void addAVToBuilder(String AVName, int numValues, String identifier, String attribute, StringBuilder system, StringBuilder instantiationsCollection) {
        system.append(AVName);
        instantiationsCollection.append(AVName);
        instantiationsCollection.append(" = ");
        instantiationsCollection.append("Attribute_Value(");
        instantiationsCollection.append(numValues + ", " + identifier + ", " + attribute);
        instantiationsCollection.append(");\n");
    }

    /**
     * Creates all of the Attribute Value (AV) templates needed for the Soar agent. Uppaal can't create new memory at run time, so the maximum size of the memory must be initialized
     * all at compile time. This is accomplished through static analysis in the SymbolVisitor and passed to here where templates are created with different sized value arrays
     * @return An array with the instantiations and the system processes to be added in the global system
     */
    private String[] makeAttributeValueTemplates() {
        StringBuilder instantiationsCollection = new StringBuilder();
        StringBuilder systemProcesses = new StringBuilder(" ");
        for (UppaalAttributeValueTriad UAT : _AVCollection) {
            if (systemProcesses.length() > 1) {
                systemProcesses.append(", ");
            }
            systemProcesses.append(SoarTranslator.simplifiedString(UAT.getName()));
            addAVToBuilder(SoarTranslator.simplifiedString(UAT.getName()), UAT.getNumValues(), SoarTranslator.simplifiedString(UAT.getOperatorIndex()), UAT.getAttributeIndex(), systemProcesses, instantiationsCollection);
        }

        if (systemProcesses.length() > 1) {
            systemProcesses.append(", ");
        }
        // Both of these are required for any Soar agent model. Each state has a superstate by default and the final operator is used for decision and application stage
        addAVToBuilder("AV_final_operator", 1, "finalOp", "operator", systemProcesses, instantiationsCollection);
        systemProcesses.append(", ");
        addAVToBuilder("AV_state_superstate", 1, "_state", "superstate", systemProcesses, instantiationsCollection);

        return new String[]{instantiationsCollection.toString(), systemProcesses.toString()};
    }

    /**
     * Creates the Attribute Value (AV) template inside Uppaal used to store the values of each attribute of each identifier. They are stored in a template because you can't
     * make different sized arrays in Uppaal and collect them into one structure very easily. This keeps all the information and methods needed for the AV templates localized
     * instead of spread out in the global declarations.
     * @return The AV template
     */
    private Element getAttributeValueTemplate() {
        String startId = getCounter();
        String middleAddLocationID = getCounter();

        Template attributeValueTemplate = makeTemplate("Attribute_Value");
        attributeValueTemplate.setProperty("parameter", "const int NUM_VALUES, const int OPERATOR_ID, const int ATTRIBUTE_INDEX");
        // These are all the functions needed to store/retrieve/remove WMEs in Uppaal to mirror what Soar does
        attributeValueTemplate.setProperty("declaration",
                "int values[NUM_VALUES];\n" +
                        "int valuesIndex = 0;\n" +
                        "int containsIndex = -1;\n" +
                        "\n" +
                        // This method is used to check conditions
                        // if it is a variable
                        //if there are still more values that we haven't checked in our list of variables
                        //get the next one and continue checking the other conditions
                        //else
                        //indicate that there aren't any more values and signal to go back to the last time we picked a variable to select the next one from that list
                        // else (it is a constant)
                        //check to see if we have that value in our list of values
                        //if we do
                        //then we can continue checking other conditions
                        //else
                        //go back to the last time we picked a variable and select another one. Once we try all the combinations, the production won't be matched
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
                        "\t\t\tint currentStackIndex;\n" +
                        "\t\t\tif (stackRetractIndex <= -1) {\n" +
                        "\t\t\t\tcurrentStackIndex = stackCondition[stackConditionIndex];\n" +
                        "\t\t\t} else {\n" +
                        "\t\t\t\tcurrentStackIndex = stackRetract[stackRetractIndex];\n" +
                        "\t\t\t}\n" +
                        "\t\t\treplaceSpecificValues(lookForValue, replaceValue, currentStackIndex);\n" +
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
                        // This method removes all the values. This is used when this WME has been retracted because we need to reuse this element unlike Soar which would just create
                        // a new one
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
                        // This method removes a specific value which is explicitly called by productions to delete WMEs
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

    /**
     * Creates a little cute loop off the side of the loopLocation. Made by trial and error so change as needed
     * @param direction Right now, can handle "right" or "left" of the provided location
     * @param currentTemplate Template to add the loop to
     * @param loopLocation Location to add the loop to
     * @param guard Guard on the loop
     * @param assignment Assignment on the loop
     */
    private void makeLoop(String direction, Template currentTemplate, Location loopLocation, String guard, String assignment) {
        // Constants found by guessing and checking. Modify as needed
        int[] constants = {417, 51, 68};
        if (direction.equals("right")) {
            constants[0] = -75;
            constants[2] *= -1;
        }
        int xTextLocation = loopLocation.getX() - constants[0];
        Integer[] nails = new Integer[]{loopLocation.getX(), loopLocation.getY() + constants[1], loopLocation.getX() - constants[2], loopLocation.getY() + constants[1], loopLocation.getX() - constants[2], loopLocation.getY()};
        makeEdgeWithNails(currentTemplate, loopLocation, loopLocation, null, null, null, null, guard, new Integer[]{xTextLocation, loopLocation.getY() - 10}, assignment, new Integer[]{xTextLocation, loopLocation.getY() - 10 + getNumLines(guard, " &&")*SIZE_OF_TEXT}, nails);
    }

    /**
     * AVUtility is used to match with non AV specific things like the disjunction tests for attributes as well as helping to catch edge cases. It also handles extra restrictions
     * on conditions like being lessThan a specific value
     *
     * One important edge case is when selecting the next combination of variables to try to match in a production, you may select a value to be used as an identifier which doesn't
     * have the attribute you need to check for as well.  Before, Uppaal would stall because the AVs only match when their identifier and attribute match.  This template includes
     * a catch all edge that handles all of those cases though the guard gets really, really long
     * @return The AVUtility template
     */
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
                        "\t\tint currentStackIndex = stackCondition[stackConditionIndex];\n" +
                        "\t\treplaceSpecificValues(lookForValue, replaceValue, currentStackIndex);\n" +
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

        // One important edge case is when selecting the next combination of variables to try to match in a production, you may select a value to be used as an identifier which doesn't
        // have the attribute you need to check for as well.  Before, Uppaal would stall because the AVs only match when their identifier and attribute match.  This template includes
        // a catch all edge that handles all of those cases though the guard gets really, really long
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

    /**
     * Gets the operator corresponding to the index of the final operator
     * @return Operator that has the finalOperatorIndex as its index
     */
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

    /**
     * Create's OperatorPreferences template that is how Uppaal mimics Soar's operator selection process in the decision step
     * @return Null
     */
    private Element getOperatorPreferences() {
        Template operatorPreferencesTemplate = makeTemplate("preferenceResolutionTemplate");

        // Includes all of the methods needed to take a collection of operators and narrow down the choices to one operator
        // Note: Currently we can't handle substates and impasses. If the Soar agent hits a substate and is uploaded into Uppaal, Uppaal will hit the impasse and just stop
        // This will need an update if that capability is added
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
                        "}" + getTinyDeclaration(new String[]{"finalOp"}, new String[]{"operator"}, new String[]{"0"})
        );

        // These were added before most of the other components were added.  Therefore, they have fixed x and y values making them not very easy to move.
        // todo: make the coordinates reactive like the other methods

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
