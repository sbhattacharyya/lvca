package edu.fit.hiai.lvca.translator.soar;

import com.uppaal.model.core2.*;
import edu.fit.hiai.lvca.antlr4.SoarBaseVisitor;
import edu.fit.hiai.lvca.antlr4.SoarParser;
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
    private final String _outputFileName;
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
    private int _latestIndex;
    private Map<String, Boolean> _productionToOSupported;
    private Map<String, LinkedList<String>> _variableToAttributes;
    private Map<String, Map<String, String[]>> _attributeVariableToDisjunctionTestPerProduction;
    private Map<String, Map<String, String>> _attributeVariableToArrayNamePerProduction;
    private Map<String, String[]> _disjunctionArrayNameToArray;
    private Map<String, Boolean> _flags;
    private int _maxConditionSize = -1;

    /**
     * Creates a new UPPAALSemanticVisitor and copies all of the passed in structures to globals stored in here
     * @param outputFileName Name of the file that this Translator will generate
     * @param stringAttributeNames Set of string constants used in the Soar agent
     * @param variablesPerProductionContext Map from production name to a mapping from a variable to its path
     * @param boolAttributeNames Set of constants which are boolean values
     * @param numOperators Number of operators that will be needed by Soar
     * @param actualVariablesPerProduction Map from production name to ProductionVariables which distinguishes which variables are actual variables and which are used as identifiers later
     * @param takenValues List of numbers which are reserved by Soar as constants
     * @param uppaalOperatorCollection List of names of the all of the identifiers needed by Soar
     * @param AVCollection List of UppaalAttributeValueTriad which make it easy to enumerate all of the AV templates
     * @param variablesToPathWithID Map from production name to mapping from a variable to its path with ID
     * @param productionToOSupported Map from production name to whether or not it is O-supported
     * @param variableToAttributes Map from variable (identifier) to its list of attributes that are associated with it
     * @param attributeVariableToDisjunctionTestPerProduction Map from production name to a mapping from variable (attribute) to a String array of the values it has to match
     *                                                        when used in a disjunctive test
     */
    public UPPAALSemanticVisitor(String outputFileName, Set<String> stringAttributeNames, Map<String, Map<String, String>> variablesPerProductionContext, Set<String> boolAttributeNames, int numOperators, Map<String, ProductionVariables> actualVariablesPerProduction, HashSet<Integer> takenValues, LinkedList<String> uppaalOperatorCollection, LinkedList<UppaalAttributeValueTriad> AVCollection, Map<String, Map<String, String>> variablesToPathWithID, Map<String, Boolean> productionToOSupported, Map<String, LinkedList<String>> variableToAttributes, Map<String, Map<String, String[]>> attributeVariableToDisjunctionTestPerProduction) {
        _outputFileName = outputFileName;
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
        _latestNum = 1 + _globals.size() + _uppaalOperatorCollection.size();
        _productionToOSupported = productionToOSupported;
        _variableToAttributes = variableToAttributes;
        _attributeVariableToDisjunctionTestPerProduction = attributeVariableToDisjunctionTestPerProduction;
        _attributeVariableToArrayNamePerProduction = cleanAttributeVariableToArrayName();
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
                "broadcast chan Reset_Apply;\n" +
                "chan Continue_Run;\n" +
                "chan Require_Test;\n" +
                "bool halt = false;\n" +
                "bool isRetracting;\n" +
                "bool addOperator;\n" +
                "bool removeOperator;\n" +
                "bool productionFired;\n" +
                "const int numTemplates = " + _templateNames.size() + ";\n" +
                "int stackCondition[numTemplates];\n" +
                "int stackAction[numTemplates];\n" +
                "int stackRetract[numTemplates];\n" +
                "int stackConditionIndex = -1;\n" +
                "int stackActionIndex = -1;\n" +
                "int stackRetractIndex = -1;\n" +
                "int selectedFinalOperatorIndex;\n" +
                "const int EMPTY = -2;\n" +
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
        globalDeclaration.append("const int TOTAL_NUM_ATTRIBUTES = " +
                totalAttributeSize + ";\n" +
                "int nestedCheckArray[TOTAL_NUM_ATTRIBUTES];\n" +
                "int nestedCheckIndex = 0;\n");

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

        // Until I can think of a better way to do it, these are two switch statements that are inverses of each other
        // One you give the id and it gives you the operator associated with it, the other given the operator gives you the id

        getOperatorToIDAndBack(actualOperatorCollection, "getOperatorFromID(int id)", "id", true, globalDeclaration);

        getOperatorToIDAndBack(actualOperatorCollection, "getIDFromOperator(int operator)", "operator", false, globalDeclaration);

        // This switch is filled at the top of this method, but placed here because it isn't as important and can go much lower in the declaration
        if (noneButSwitch != null) {
            globalDeclaration.append(noneButSwitch);
        }

        ourDocument.setProperty("declaration", globalDeclaration.toString());
    }

    /**
     * Produces switch statement that is either for getOperatorFromID or getIDFromOperator
     * @param actualOperatorCollection LinkedList of operators (path with ID)
     * @param functionName Name of which function it is
     * @param ifPart The variable from the function that is being compared, you could probably also just get it from the function name
     * @param operatorFromID Flag that indicates which method it is
     * @param currentDeclaration Current declaration builder that the method is being added to
     */
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
            ourDocument.save(_outputFileName);
            System.out.println("File saved as: " + _outputFileName);
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
     * Gets the positive and inverse version of the guard provided. Utility for addVerticalLocation
     * @param startGuard Initial guard
     * @return Array of size 2 with the structure: {regularGuard, inverseGuard}
     */
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
     * @param startLocation The start location of the current template. If not null, then there is a back edge added to go back to start
     * @return The new last location is the newly created location
     */
    private Location addHorizontalLocation(Template currentTemplate, Location lastLocation, int[] lastLocationCoords, String name, String synchronization, String stackGuard, String assignment, boolean mirrored, Location startLocation) {
        // Both of these variables allow you to easily change where the text is
        // These constants should be extracted todo: extract constants
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

    /**
     * Utility method for adding an edge that goes from the provided location back to the other provided location with the given guard and assignment
     * @param currentTemplate The current template where the edge will be added
     * @param fromLocation The source of the new edge
     * @param fromLocationCoords The coordinates of the source. You can also get these with .getX() and .getY() methods
     * @param toLocation The destination of the edge
     * @param guard Text for the guard. If null, then there won't be any guard on the edge
     * @param kickBackIndex Part of the utility fro the addVerticalLocation is to change where you are kick to. This is the index of which location is being kicked back to in that case
     * @param kickBackReference Part of the utility fro the addVerticalLocation is to change where you are kick to. This is the location which is being kicked back to in that case
     * @param isRetraction Says if the production is I-supported (True) or O-supported (False)
     * @param indexToKickBackCommands Needed when kicking back on the guard side. Includes the assignment of the edge before the one you are kicking back to without saving any of
     *                                the temporary variables. This allows you to get the next value/check the last condition without overwriting the temporary variable incorrectly
     */
    private void kickBackToProvidedLocation(Template currentTemplate, Location fromLocation, int[] fromLocationCoords, Location toLocation, String guard, Integer kickBackIndex, Location kickBackReference, boolean isRetraction, Map<Integer, StringBuilder> indexToKickBackCommands) {
        Integer[] textLocation = new Integer[2];
        Integer[] nails;
        String assignment;
        // Allows for the use of this method under different conditions. It changes where the nails are if any, where the text goes and so forth
        // The location of text and nails is highly customizable and easy to change by editing the constants.  They were selected by guess and check
        if (isRetraction) {
            textLocation[0] = fromLocationCoords[0] - (370/2) - 7;
            textLocation[1] = fromLocationCoords[1] - SIZE_OF_TEXT;
            if (fromLocation.getY() == toLocation.getY()) {
                nails = null;
            } else {
                nails = new Integer[]{toLocation.getX(), fromLocation.getY()};
            }
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

    /**
     * Adds a single vertical location down from the last location and an edge that goes from the last location to the new location.
     * Compare this to addVerticalLocation which includes a for loop adding many vertical edges
     * @param currentTemplate The current template where the edge will be added
     * @param lastLocation The last location where the edge will be coming from and then going to the new location created
     * @param lastLocationCoords The coordinates of the last location. They can also be found with a .getX() and .getY() method from the location but it's a little easier with them stored this way
     * @param guard Text for the guard. If null, then there won't be any guard on the edge
     * @param assignment Text for the assignment.  If null, then there won't be any assignmnet on the edge
     * @return The new last location which is the newly created location
     */
    private Location addSingleVerticalLocation(Template currentTemplate, Location lastLocation, int[] lastLocationCoords, String guard, String assignment) {
        // The constants are highly customisable and were selected based on guessing and checking the Uppaal model. Modify as needed
        Integer[] textLocation = new Integer[]{lastLocationCoords[0] + 25, lastLocationCoords[1] + SIZE_OF_TEXT};
        int yTempCoords = lastLocationCoords[1] + 200;
        Location lastLocationTemp = makeLocationWithCoordinates(currentTemplate, null, getCounter(), true, false, lastLocationCoords[0], yTempCoords, null, null);
        makeEdge(currentTemplate, lastLocation, lastLocationTemp, null, null, null, null, guard, textLocation, assignment, new Integer[]{textLocation[0], textLocation[1] + (SIZE_OF_TEXT*getNumLines(guard, " &&"))});
        lastLocation = lastLocationTemp;
        lastLocationCoords[1] = yTempCoords;
        return lastLocation;
    }

    /**
     * Adds all of the vertical locations needed in the provided array of conditionsOrAssignments
     * @param currentTemplate The current template where the location will be added
     * @param lastLocation The last location where the edge will be coming from and then going to the new location created
     * @param lastLocationCoords The coordinates of the last location. They can also be found with a .getX() and .getY() method from the location but it's a little easier with them stored this way
     * @param guard Text for the guard. If null, then there won't be any guard on the edge
     * @param conditionsOrAssignments Array of StringBuilders with the remaining conditions or actions. The 1st element should have been added horizontally
     * @param kickBackLocation If provided, this will be where a back edge is created using kickBackToProvidedLocation
     * @param kickBackIndexes Keeps track of the indices of the which location any given location should kick back to
     * @param kickBackReferences Array of locations which is indexed by kickBackIndexes
     * @param isRetraction Says if the production is I-supported (True) or O-supported (False)
     * @param indexToKickBackCommands Map from kickBackIndex to what the assignments are for that edge
     * @return The new last location which is the last newly created location
     */
    private Location addVerticalLocation(Template currentTemplate, Location lastLocation, int[] lastLocationCoords, String guard, StringBuilder[] conditionsOrAssignments, Location kickBackLocation, int[] kickBackIndexes, Location[] kickBackReferences, boolean isRetraction, Map<Integer, StringBuilder> indexToKickBackCommands) {
        String[] guardAndInverseGuard = getGuards(guard);
        for(int i = 1; i < conditionsOrAssignments.length; i++) {
            lastLocation = addSingleVerticalLocation(currentTemplate, lastLocation, lastLocationCoords, guardAndInverseGuard[0], conditionsOrAssignments[i].toString());
            // This if statement is satisfied during conditions which need back edges
            if (guardAndInverseGuard[1] != null) {
                if (isRetraction) {
                    kickBackToProvidedLocation(currentTemplate, lastLocation, lastLocationCoords, kickBackLocation, guardAndInverseGuard[1], null, null, isRetraction, null);
                } else {
                    kickBackToProvidedLocation(currentTemplate, lastLocation, lastLocationCoords, kickBackLocation, guardAndInverseGuard[1], kickBackIndexes[i], kickBackIndexes[i] == -1 ? null : kickBackReferences[kickBackIndexes[i]], isRetraction, indexToKickBackCommands);
                    kickBackReferences[i+1] = lastLocation;
                }
            }
        }
        // This is the extra location needed to make sure that the combination of variables that are being matched haven't already been matched by the production
        if (guardAndInverseGuard[1] != null && !isRetraction && (_conditionSideVariablesToTemps.size() > 0 || _attributesToTemps.size() > 0)) {
            lastLocation = addSingleVerticalLocation(currentTemplate, lastLocation, lastLocationCoords, guardAndInverseGuard[0], "valueFunction = 0,\nattributeFunction = 0,\nglobalIdentifier = 0,\nglobalAttribute = 0,\nglobalValue = 0,\nglobalDoesContain = 0,\ncheckProductionsContain()");
            kickBackToProvidedLocation(currentTemplate, lastLocation, lastLocationCoords, kickBackLocation, guardAndInverseGuard[1], kickBackIndexes[kickBackIndexes.length - 1], kickBackIndexes[kickBackIndexes.length - 1] == -1 ? null : kickBackReferences[kickBackIndexes[kickBackIndexes.length - 1]], isRetraction, indexToKickBackCommands);
        }

        return lastLocation;
    }

    /**
     * Used to move from the last condition to the start of the assignments
     * @param currentTemplate The current template where the location will be added
     * @param lastLocation The last location where the edge will be coming from and then going to the new location created
     * @param lastLocationCoords The coordinates of the last location. They can also be found with a .getX() and .getY() method from the location but it's a little easier with them stored this way
     * @param name Name of the location to be added
     * @param guard Text for the guard. If null, then there won't be any guard on the edge
     * @param assignment Text for the assignment.  If null, then there won't be any assignmnet on the edge
     * @param mirrored If true, then the new location will be added to the right of the last location.  If false, to the left.
     * @return The new last location which is the last newly created location
     */
    private Location goToNextStage(Template currentTemplate, Location lastLocation, int[] lastLocationCoords, String name, String guard, String assignment, boolean mirrored) {
        // This variable allows you to easily change where the text is and where the location coordinates are.  They are based purely on guess and check in Uppaal
        // These constants should be extracted
        int xTempCoords = lastLocationCoords[0] + (mirrored ? -370 : 370);
        Location lastLocationTemp = makeLocationWithCoordinates(currentTemplate, name, getCounter(), true, false, xTempCoords, 0, getNameLocation(name, xTempCoords), -32 + (mirrored ? -1 * SIZE_OF_TEXT : 0));
        Integer[] nails = new Integer[]{lastLocationCoords[0] + (mirrored ? (-370/3) : (370/3)), lastLocationCoords[1] + 200, xTempCoords, lastLocationCoords[1] + 200};
        Integer[] textLocation = new Integer[]{(mirrored ? nails[2] : nails[0]) + 25, lastLocationCoords[1] + 200 - SIZE_OF_TEXT};
        makeEdgeWithNails(currentTemplate, lastLocation, lastLocationTemp, null, null, null, null, guard, textLocation, assignment, new Integer[]{textLocation[0], textLocation[1] + (getNumLines(guard, " &&")*SIZE_OF_TEXT)}, nails);
        lastLocationCoords[0] = xTempCoords;
        lastLocationCoords[1] = 0;
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
        int textLocationX = lastLocationCoords[0] + (mirrored ? -(370/2) - 7 : -370);
        Integer[] guardLocation = new Integer[]{textLocationX,  assignmentSpace - SIZE_OF_TEXT * getNumLines(guard, " &&")};
        Integer[] assignmentLocation = new Integer[]{textLocationX, assignmentSpace};

        makeEdgeWithNails(currentTemplate, lastLocation, startLocation, null, null, synchronization, new Integer[]{textLocationX, guardLocation[1] - SIZE_OF_TEXT}, guard, guardLocation, assignment, assignmentLocation, nails);
    }

    /**
     * Adds an edge back from the last assignment back to the start
     * @param currentTemplate The current template where the location will be added
     * @param lastLocation The last location where the edge will be coming from and then going to the new location created
     * @param startLocation The start location of the template
     * @param lastLocationCoords The coordinates of the last location. They can also be found with a .getX() and .getY() method from the location but it's a little easier with them stored this way
     * @param operatorAssignments List of operator assignments are all just done at once on the last edge
     * @param needsRetraction Says if the production is I-supported (True) or O-supported (False)
     * @param guard Text for the guard. If null, then there won't be any guard on the edge
     */
    private void goBackToStartFromAssignment(Template currentTemplate, Location lastLocation, Location startLocation, int[] lastLocationCoords, String operatorAssignments, boolean needsRetraction, String guard) {
        StringBuilder assignment = new StringBuilder("addOperator = false,\nremoveStackAction()");
        if (!needsRetraction) {
            assignment.append(",\ncurrentNumFiringPerCycle++");
        }
        if (operatorAssignments.length() > 0) {
            assignment.append(",\n").append(operatorAssignments);
        }
        assignment.append(",\nfillNextProduction()");
        // These variables move the text around so that it looks good. Guess and check with Uppaal. Modify as needed
        Integer[] textLocation = new Integer[]{lastLocationCoords[0] + 25, lastLocationCoords[1] - (SIZE_OF_TEXT*getNumLines(guard, " &&"))};
        Integer[] nails = new Integer[]{lastLocationCoords[0] + 370, lastLocationCoords[1], lastLocationCoords[0] + 370, -110, startLocation.getX(), -110};
        makeEdgeWithNails(currentTemplate, lastLocation, startLocation, null, null, null, null, guard, textLocation, assignment.toString(), new Integer[]{textLocation[0], textLocation[1] + (getNumLines(guard, " &&")*SIZE_OF_TEXT)}, nails);
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
     * Sets up the declaration for each production. Needs to be called after the visits to the condition and action side of the production at least.
     * @param productionName Name of the production
     * @param operatorIndexes Set of the operator indexes that are accessed in this production
     * @param conditionTempToIndex Map from temporary variables needed for this production to their index. Filled during function
     * @param attributeTempToIndex Map from temporary attribute variable needed for this production to their index. Filled during function
     * @return The production's declaration
     */
    private String getProductionDeclaration(String productionName, Set<String> operatorIndexes, Map<String, Integer> conditionTempToIndex, Map<String, Integer> attributeTempToIndex) {
        StringBuilder currentTemplateDeclaration = new StringBuilder();
        for (String dummyVariable : _conditionSideVariablesToTemps.values()) {
            currentTemplateDeclaration.append("int ").append(dummyVariable).append(";\n");
        }
        for (String dummyVariable : _attributesToTemps.values()) {
            currentTemplateDeclaration.append("int ").append(dummyVariable).append(";\n");
        }
        // This sets how many productions are allowed to match. As we allow for multiple productions matching per cycle then this will need to change depending the production
        currentTemplateDeclaration.append("const int NUMBER_OF_PRODUCTIONS = 1;\n");
        currentTemplateDeclaration.append("\n");

        int conditionTemps = _conditionSideVariablesToTemps.size();
        int attributeTemps = _attributesToTemps.size();


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
            for (String nextTemp : _conditionSideVariablesToTemps.values()) {
                conditionTempToIndex.put(nextTemp, index);
                currentTemplateDeclaration.append("\tproductions[productionIndex].savedTempAndFunction[" + index++ + "] = " + nextTemp + ";\n");
            }
            index = 0;
            for (String nextTemp : _attributesToTemps.values()) {
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
            //todo: sort this by value so that they come out in a consistent fashion
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

        if (_productionToOSupported.get(productionName)) {
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
                        currentTemplateDeclaration.append(" ||\n\t\t\t\t");
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
        } else if (operatorIndexes != null) {
            currentTemplateDeclaration.append("\nvoid checkAndClearFinalOperator() {\n");
            currentTemplateDeclaration.append("\t if(");
            StringBuilder addOperatorsToRetract = new StringBuilder();
            StringBuilder clearOperators = new StringBuilder();
            for (String nextOperatorIndex : operatorIndexes) {
                if (currentTemplateDeclaration.charAt(currentTemplateDeclaration.length() - 1) != '(') {
                    currentTemplateDeclaration.append(" ||\n\t\t");
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

        return currentTemplateDeclaration.toString();
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
     * Utility for getConditionOrAssignment to add non null values to the provided StringBuilder
     * @param variable The variable to be added which will be set equal to the nextElement
     * @param nextElement The element that the variable will be set equal to
     * @param conditionOrAssignment Holds the next condition or assignment
     * @param commaNext Flag that indicates if there will be another assignment after this one
     */
    private void addNextElement(String variable, String nextElement, StringBuilder conditionOrAssignment, boolean commaNext) {
        if (conditionOrAssignment != null) {
            conditionOrAssignment.append(variable).append(" = ").append(nextElement);
            if (commaNext) {
                conditionOrAssignment.append(",\n");
            }
        }
    }

    /**
     * Collects an array that contains all of the conditions or actions needed for the edges
     * This model was adapted from the MemoryIntensive model.
     * Todo: Update all of the methods to create these conditions and actions in the visitor pattern instead of having to loop here
     * @param productionIdentifiers List of identifiers
     * @param productionAttributes List of attributes
     * @param productionValues List of values
     * @param productionValueTemps List of temporary values
     * @param productionAttributeTemps List of temporary attributes
     * @param conditionTempToIndex Map from condition temp to its index
     * @param attributeTempToIndex Map from attribute temp to its index
     * @param isAssignment Flag that indicates if it is a condition or assignment
     * @param indexToKickBackCommands Conditions kick back to different locations. This Maps each location to the assignments needed on the kick back location
     * @return A StringBuilder array. The first row are the regular conditions or assignments. The second row is used for inverse conditions
     */
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
                if (i >= productionIdentifiers.size()) {
                    break;
                }
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

    /**
     * Sets up the return indexes for the conditions so they know which location to return to to get the next combination
     * @return Array of indexes for the kick back locations
     */
    private int[] getKickBackIndexes() {
        int[] kickBackIndexes = new int[_conditionProductionValues.size()];
        int lastNilAnything = -1;
        int index = 0;
        for (String nextValue : _conditionProductionValues) {
            kickBackIndexes[index] = lastNilAnything;
            if (nextValue.equals("nilAnything") || _conditionProductionAttributes.get(index).startsWith("noneBut")) {
                lastNilAnything = index + 1;
            }
            index++;
        }
        return kickBackIndexes;
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

        String startStateID = getCounter();

        Template currentTemplate = makeTemplate(SoarTranslator.simplifiedString(ctx.sym_constant().getText()));
        _templateNames.add(getText(currentTemplate, "name"));

        Location startLocation = makeLocationWithCoordinates(currentTemplate, "Start", startStateID, true, true, -152, 0, -200, -32);

        ctx.condition_side().accept(this);
        Node actionSide = ctx.action_side().accept(this);

        String operatorAssignments = getText(actionSide, "operatorAssignments");
        // This can probably can be done while the condition and action side of the production are being visited. I collect the different indexes used in the operatorAssignments
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

        boolean halt = getText(actionSide, "hasHalt").equals("yes");
        boolean needsRetraction = !_productionToOSupported.get(ctx.sym_constant().getText());

        Map<String, Integer> conditionTempToIndex = new HashMap<>();
        Map<String, Integer> attributeTempToIndex = new HashMap<>();
        currentTemplate.setProperty("declaration", getProductionDeclaration(ctx.sym_constant().getText(), operatorIndexes, conditionTempToIndex, attributeTempToIndex));

        int[] lastLocationCoords = new int[2];
        setLastLocationCoords(lastLocationCoords);
        Location lastLocation;

        // The main thing you want is a separation of all the conditions and actions so that the generation of the edges is easy
        // This next section here is reusing the mechanics from the MemoryIntensiveVersion
        // Todo: Update all of the methods to create these conditions and actions in the visitor pattern instead of having to loop here
        Map<Integer, StringBuilder> indexToKickBackCommands = new HashMap<>();
        StringBuilder[][] conditions = getConditionOrAssignment(_conditionProductionIdentifiers, _conditionProductionAttributes, _conditionProductionValues, _conditionProductionTemp, _attributeTemps, conditionTempToIndex, attributeTempToIndex, false, indexToKickBackCommands);
        StringBuilder[][] assignments = getConditionOrAssignment(_actionProductionIdentifiers, _actionProductionAttributes, _actionProductionValues, _actionProductionFunctions, null, conditionTempToIndex, attributeTempToIndex, true, null);
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
            // This section adds the left branch off the Start location. For retraction, it mirrors the conditions and actions on the right side
            // For non retraction, it just adds a couple edges off to the left
            // To follow which location is which, follow the methods which add different locations horizontally or vertically and look at the Names of the locations
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
        // Restores the lastLocationCoords to the start location. If you move the start location, change the constants in this method. Or better yet, hook them up together
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
        if (!halt) {
            goBackToStartFromAssignment(currentTemplate, lastLocation, startLocation, lastLocationCoords, operatorAssignments, needsRetraction, guard);
        } else {
            goBackToProvidedLocation(currentTemplate, lastLocation, startLocation, lastLocationCoords, null, "Halt!", false);
        }

        _templateIndex++;
        _maxConditionSize = Math.max(_maxConditionSize, _conditionProductionIdentifiers.size());
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

            // Again this can be reworked for this methodology instead of reusing the methodology for the MemoryIntensive model
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
     * Returns either the index if it is a number already or the method call with the index to get the number during run time of Uppaal
     * @param index Index to be checked
     * @return The index that Uppaal will use
     */
    private String getOperatorIndex(String index) {
        try {
            Integer.parseInt(index);
            return index;
        } catch(NumberFormatException e) {
            return "getIDFromOperator(" + index + ")";
        }
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
        returnString.append(getOperatorIndex(index));
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
                        operatorIndex = getOperatorIndex(operatorIndex);
                        thatValueID = getOperatorIndex(thatValueID);
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
     * Creates scheduler for Uppaal. This is the mirror of Soar's execution cycle and uses a broadcast channel to synchronize the other productions
     * @return The scheduler template
     */
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
        lastLocation = addHorizontalLocation(runScheduler, lastLocation, lastLocationCoords, "Decision", null, "!checkApplyRetract &&\n!productionFired &&\nstackRetractIndex == -1", "isRetracting = false,\nfillOthers(),\nretractOperatorsIndex = 0", false, null);
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
        makeEdgeWithNails(currentTemplate, loopLocation, loopLocation, null, null, null, new Integer[]{xTextLocation, loopLocation.getY() - 10 - (SIZE_OF_TEXT * (getNumLines(guard, " &&") + getNumLines(assignment, ",")))}, guard, new Integer[]{xTextLocation, loopLocation.getY() - 10}, assignment, new Integer[]{xTextLocation, loopLocation.getY() - 10 + getNumLines(guard, " &&")*SIZE_OF_TEXT}, nails);
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

        // One important edge case is when selecting the next combination of variables to try to match in a production, you may select a value to be used as an identifier which doesn't
        // have the attribute you need to check for as well.  Before, Uppaal would stall because the AVs only match when their identifier and attribute match.  This template includes
        // a catch all edge that handles all of those cases though the guard gets really, really long
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
        String nextAssignment = "addOperator = true,\nvalueFunction = 0,\nglobalIdentifier = finalOp,\nglobalAttribute = operator,\nglobalValue = finalOperatorIndex";
        makeEdge(operatorPreferencesTemplate, done, noName4, null, null, null, null, null, null, nextAssignment + ",\nselectedFinalOperatorIndex = finalOperatorIndex", new Integer[]{-3280, -504});
        makeEdgeWithNails(operatorPreferencesTemplate, noName4, start, null, null, "Continue_Run!", new Integer[]{-3918, -1113}, "!addOperator", new Integer[]{-3918, -1097}, null, null, new Integer[]{-3808, -1536});

        return null;
    }
}
