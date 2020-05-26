package edu.fit.hiai.lvca.translator.soar;

import edu.fit.hiai.lvca.antlr4.SoarLexer;
import edu.fit.hiai.lvca.antlr4.SoarParser;
import org.antlr.v4.gui.TestRig;
import org.antlr.v4.runtime.ANTLRFileStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.apache.commons.cli.*;

import javax.swing.*;
import java.io.File;
import java.io.IOException;
import java.util.*;
import java.util.stream.Collectors;

/**
 * Created by mstafford on 5/31/16.
 * Updated by Daniel Griessler throughout the summer of 2018
 *
 * Runs translation process.
 */

public class SoarTranslator
{
    private static String soarSourceFile = null;
    private static String outputFile = null;
    private static boolean debugFlag = false;

    /**
     * Parse arguments given:
     * -i [filename] Input file soar
     * -o [filename] Output-file-uppaal
     * -d            Parse-tree debug flag
     *
     * Translate Soar to Uppaal.
     *
     * @param args provided by user
     * @throws IOException Thrown by ANTLR if there is a problem with the soarSourceFile from getUPPAAL
     */
    public static void main(String[] args) throws IOException
    {
        parseArgs(args);

        LinkedList<UppaalAttributeValueTriad> AVCollection = getUPPAAL(soarSourceFile);

        Scanner in = new Scanner(System.in);
        System.out.println("Do you want to use the Plugin? (Yes/No)");
        String answer = in.nextLine();
        if (answer.equalsIgnoreCase("yes")) {
            Uppaal_Plugin generateQueriesHelper = new Uppaal_Plugin(AVCollection);
        }
        in.close();
    }

    /**
     * Using Apache Commons CLI.  Debug Flag uses Antlr's "TestRig" class to spawn a window that shows the parse tree.
     * @param args Provided by user
     */
    private static void parseArgs(String[] args)
    {
        Options options = new Options();

        Option outputFileOption = new Option("o", "output", true, "Output UPPAAL File");
        options.addOption(outputFileOption);

        Option inputFileOption = new Option("i", "input", true, "Input Soar File");
        options.addOption(inputFileOption);

        Option debugOption = new Option("d", "debug", false, "Debug (Show Parse Tree)");
        options.addOption(debugOption);

        CommandLineParser parser = new BasicParser();
        try
        {
            CommandLine parsedOptions = parser.parse(options, args);

            if(parsedOptions.hasOption(outputFileOption.getOpt()))
            {
                outputFile = parsedOptions.getOptionValue(outputFileOption.getOpt());
            }

            if(parsedOptions.hasOption(inputFileOption.getOpt()))
            {
                soarSourceFile = parsedOptions.getOptionValue(inputFileOption.getOpt());
            }

            if (soarSourceFile == null) soarSourceFile = getFileFromDialog("Choose Source Soar File");
            if (outputFile == null) outputFile = getFileFromDialog("Choose output UPPAAL File");

            if (parsedOptions.hasOption(debugOption.getOpt()))
            {
                TestRig.main(new String[]{"edu.fit.hiai.lvca.antlr4.Soar", "soar", "-gui", soarSourceFile});
            }

        }
        catch (ParseException e1)
        {
            new HelpFormatter().printHelp("-o OutputFile -i InputFile", options);
        }
        catch (Exception e)
        {
            e.printStackTrace();
        }
    }

    /**
     * Auxiliary function used to numerate the variables with arbitrary IDs.
     * Motivation: Soar reuses variable names between productions.  A full list of the actual variables that Soar has versus which ones it updates is needed for Uppaal to be
     * "computable at compile time"
     * @param attributesAndValuesPerProduction Maps production names to a mapping between attributes and their values stored in AugmentedSymbolTrees
     * @param takenValues Integer list of which constants are reserved and can't be used by Uppaal
     *                    Starts empty, filled during method
     * @param variablesToPathWithID Map production names to a mapping between variables and their paths with IDs as opposed to their generic paths stored in variablesPerProductionContext
     * @param variableIDToIndex Map variables to their most recent index
     *                          Starts empty, filled during method
     * @param variablesPerProductionContext Map production names to a mapping between variables and their paths
     * @param actualVariablesPerProduction Map production names to ProductionVariables which stores a list that clarifies which variables are actually created as opposed to being updated
     * @return LinkedList of variable names that includes all the variables' paths with their arbitrary IDs
     */
    private static LinkedList<String> giveVariablesIDs(Map<String, Map<String, AugmentedSymbolTree>> attributesAndValuesPerProduction, HashSet<Integer> takenValues, Map<String, Map<String, String>> variablesToPathWithID, Map<String, Integer> variableIDToIndex, Map<String, Map<String, String>> variablesPerProductionContext, Map<String, ProductionVariables> actualVariablesPerProduction) {
        LinkedList<String> variableNames = new LinkedList<>();
        //Most maps are indexed by production name.  This allows for a loop like this to easily retrieve all of the information related to each production
        for (String individualProduction : attributesAndValuesPerProduction.keySet()) {
            Map<String, String> newVariablesMap = new HashMap<>();
            variablesToPathWithID.put(individualProduction, newVariablesMap);
            Map<String, AugmentedSymbolTree> currentAttributesAndValues = attributesAndValuesPerProduction.get(individualProduction);
            Map<String, String> currentVariables = variablesPerProductionContext.get(individualProduction);
            ProductionVariables actualVariables = actualVariablesPerProduction.get(individualProduction);
            Map<String, Boolean> seenVariables = new HashMap<>();
            //Loops through each variable and adds relevant IDs using methods inside AugmentedSymbolTree
            for (String individualVariable : currentAttributesAndValues.keySet()) {
                currentAttributesAndValues.get(individualVariable).makeIDs(takenValues, newVariablesMap, variableIDToIndex, currentVariables, actualVariables, variableNames, seenVariables);
                if (currentVariables.get(individualVariable).equals("state")) {
                    newVariablesMap.put(individualVariable, "state_-1");
                }
            }
        }
        return variableNames;
    }

    /**
     * Checks which (if any) of the variables match between two productions
     * @param checkMap Mapping between variable and its AugmentedSymbolTree.  This is set of variables to be checked
     * @param attributeMap Same kind of mapping as checkMap.  These are the variables that are being matched against the checkMap variables
     * @param checkVariableDictionary List of variables that need to be checked as possible additional matches
     * @param attributeStateVariable Variable being used as the state variable.  Often "<s>" but it is not guaranteed to be
     * @param attributeVariablesMatch Maps the variables that matched up with each other.  It draws equivalences between productions since productions can reuse variable names
     * @param attributeVariableToDisjunctionTest Maps variable to array that comes from a disjunction test in the Soar agent
     * @return If the two productions match
     */
    private static boolean variablesMatch(Map<String, AugmentedSymbolTree> checkMap, Map<String, AugmentedSymbolTree> attributeMap, LinkedList<String> checkVariableDictionary, String attributeStateVariable, HashMap<String, String> attributeVariablesMatch, Map<String, String[]> attributeVariableToDisjunctionTest) {
        Map<String, SymbolTree> productionVariableComparison = new HashMap<>();
        productionVariableComparison.put(checkVariableDictionary.get(0), new SymbolTree(attributeStateVariable));
        //First checks the state variables are the same.  If they aren't there is no point in checking the other variables.  Uses methods in AugmentedSymbolTree
        if (checkMap.get(checkVariableDictionary.get(0)).matches(attributeMap.get(attributeStateVariable), productionVariableComparison, attributeVariableToDisjunctionTest)) {
            attributeVariablesMatch.put(attributeStateVariable, checkVariableDictionary.get(0));
            //If the state variables match, check all of the other variables to see if any match
            for (int i = 1; i < checkVariableDictionary.size(); i++) {
                String variableName = checkVariableDictionary.get(i);
                SymbolTree comparisonCollection = productionVariableComparison.get(variableName);
                int numMatches = 0;
                //ComparisonCollection holds a mapping between checkMap variables and constants or variables in attributeMap that they may be equal to
                for (SymbolTree possibleVariableMatch : comparisonCollection.getChildren()) {
                    if (checkMap.get(variableName).matches(attributeMap.get(possibleVariableMatch.name), productionVariableComparison, attributeVariableToDisjunctionTest)) {
                        attributeVariablesMatch.put(possibleVariableMatch.name, variableName);
                        numMatches++;
                    }
                }
                if (numMatches == 0) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }

    /**
     * After we know productions match then we need to apply the actions of those productions and update the variables
     * Again, Uppaal needs to know the full graph of memory.  If two productions match together then we need to expand the memory
     * @param attributesAndValuesPerProductionCount Maps production names to a mapping between variables and a count of their values stored in ASTCountWithValues
     * @param applyMap Maps variables to their AugmentedSymbolTree which contains their personal tree.
     * @param attributeVariablesMatch Maps the variables that match between productions since variable names don't have to be the same between productions
     * @param attributeVariableToDisjunctionTest Maps variable to array that comes from a disjunction test in the Soar agent
     * @param attributesAndValuesState ASTCountWithValues for the state of the apply production
     * @param attributesAndValuesForCheck  AugmentedSymbolTree that contains the state of the check production and which variables are being updated
     * @param checkAttributesAndValuesForCheck AugmentedSymbolTree that contains the state of the check production and which variables are being checked
     * @return If any new memory was actually copied over
     */
    private static boolean applyVariables(Map<String, ASTCountWithValues> attributesAndValuesPerProductionCount, Map<String, AugmentedSymbolTree> applyMap, HashMap<String, String> attributeVariablesMatch, Map<String, String[]> attributeVariableToDisjunctionTest, ASTCountWithValues attributesAndValuesState, AugmentedSymbolTree attributesAndValuesForCheck, AugmentedSymbolTree checkAttributesAndValuesForCheck) {
        boolean somethingChanged = false;
        for (String attributeVariable : attributeVariablesMatch.keySet()) {
            String keyApplyMap = attributeVariablesMatch.get(attributeVariable);
            //State variable is special so this if statements separates the state (in the else part) and all other variables (in the if part)
            if (applyMap.get(keyApplyMap) != null) {
                if (applyMap.get(keyApplyMap).makeCount(attributesAndValuesPerProductionCount.get(attributeVariable), false, attributeVariableToDisjunctionTest) && !somethingChanged) {
                    somethingChanged = true;
                }
            } else {
                checkAttributesAndValuesForCheck.applyStateMatches(attributesAndValuesState, attributesAndValuesForCheck, 1, new String[2], 0);
            }
        }
        return somethingChanged;
    }

    /**
     * Checks if all of the provided map's variables have empty AugmentedSymbolTrees
     * @param map Maps from variable to its AugmentedSymbolTree
     * @return If all of the variables have empty AugmentedSymbolTrees
     */
    private static boolean isEmpty(Map<String, AugmentedSymbolTree> map) {
        for (AugmentedSymbolTree AST : map.values()) {
            if (AST.getEdgeNameToEdge().size() > 0) {
                return false;
            }
        }
        return true;
    }

    /**
     * Uppaal only cares how big the arrays need to be to hold all of the values, not what the values actually are.  This generates a mapping from production to name to another mapping
     * between variables to a ASTCountWithValues that includes the number of elements as well as what they are.
     * Although Uppaal doesn't need which values are in there, we don't want to count a constant variable twice.
     * @param attributesAndValuesPerProduction Maps production names to a mapping between attributes and their values stored in AugmentedSymbolTrees
     * @param attributeVariableToDisjunctionTest Maps variable to array that comes from a disjunction test in the Soar agent
     * @return The mapping from production name to a mapping between variable and their ASTCountWithVariables
     */
    private static Map<String, Map<String, ASTCountWithValues>> getAttributesAndValuesPerProductionCount(Map<String, Map<String, AugmentedSymbolTree>> attributesAndValuesPerProduction, Map<String, Map<String, String[]>> attributeVariableToDisjunctionTest) {
        Map<String, Map<String, ASTCountWithValues>> attributesAndValuesPerProductionCount = new HashMap<>();
        for(String productionName : attributesAndValuesPerProduction.keySet()) {
            Map<String, ASTCountWithValues> currentAttributesAndValuesCount = new HashMap<>();
            attributesAndValuesPerProductionCount.put(productionName, currentAttributesAndValuesCount);
            Map<String, AugmentedSymbolTree> currentAttributesAndValues = attributesAndValuesPerProduction.get(productionName);
            for (String variable : currentAttributesAndValues.keySet()) {
                ASTCountWithValues variableCountTree = new ASTCountWithValues(variable);
                currentAttributesAndValues.get(variable).makeCount(variableCountTree, false, attributeVariableToDisjunctionTest.get(productionName));
                currentAttributesAndValuesCount.put(variable, variableCountTree);
            }
        }
        return attributesAndValuesPerProductionCount;
    }

    /**
     * The two sides of the productions were separated in the SymbolVistor to have a set of condition variables and a set of update variables.
     * If the condition variables of one production line up with the variables available in another production, then the update variables are applied to the matched productions variables
     * @param attributesAndValuesPerProduction Maps production names to a mapping between attributes and their values stored in AugmentedSymbolTrees
     * @param checkAttributesAndValuesPerProduction Maps production names to mapping between variables and their AugmentedSymbolTree which includes the conditions for that variable
     * @param updateAttributesAndValuesPerProduction Maps production names to mapping between variables and their AugmentedSymbolTree which includes the updates for that variable
     * @param variableHierarchy Maps production names to a LinkedList of variables in the order that they need to be matched. This is generated in the SymbolVisitor
     * @param attributeVariableToDisjunctionTest Maps variable to array that comes from a disjunction test in the Soar agent
     * @return The mapping from production name to a mapping between variable and their ASTCountWithVariables.
     * Generated by getAttributesAndValuesPerProductionCount and updated by this function
     */
    private static Map<String, Map<String, ASTCountWithValues>> applyCheckAndUpdate(Map<String, Map<String, AugmentedSymbolTree>> attributesAndValuesPerProduction, Map<String, Map<String, AugmentedSymbolTree>> checkAttributesAndValuesPerProduction, Map<String, Map<String, AugmentedSymbolTree>> updateAttributesAndValuesPerProduction, Map<String, LinkedList<String>> variableHierarchy, Map<String, Map<String, String[]>> attributeVariableToDisjunctionTest) {
        LinkedList<String> productionNames = new LinkedList<>(attributesAndValuesPerProduction.keySet());
        //Removes the productions that don't actually have any updates to be applied.
        //Those don't need to be checked because even if they matched then there would be no update
        for (int i = 0; i < productionNames.size(); i++) {
            if (isEmpty(updateAttributesAndValuesPerProduction.get(productionNames.get(i)))) {
                productionNames.remove(i);
                i--;
            }
        }

        Map<String, Map<String, ASTCountWithValues>> attributesAndValuesPerProductionCount = getAttributesAndValuesPerProductionCount(attributesAndValuesPerProduction, attributeVariableToDisjunctionTest);

        //If at least one pair of productions match each other, you have to check them all again since now others may match
        boolean repeat = false;
        do {
            for (String checkProductionName : productionNames) {
                for (String applyProductionName : attributesAndValuesPerProduction.keySet()) {
                    if (checkProductionName.equals(applyProductionName) || attributesAndValuesPerProduction.get(applyProductionName).size() == 0) {
                        continue;
                    }
                    HashMap<String, String> attributeVariablesMatch = new HashMap<>();
                    //Checks if the two productions match and then applies the update if they do
                    //Even if the variables match, they may not add any new memory which is why it is being assigned to repeat
                    if (variablesMatch(checkAttributesAndValuesPerProduction.get(checkProductionName), attributesAndValuesPerProduction.get(applyProductionName), variableHierarchy.get(checkProductionName), variableHierarchy.get(applyProductionName).get(0), attributeVariablesMatch, attributeVariableToDisjunctionTest.get(checkProductionName))) {
                        repeat = applyVariables(attributesAndValuesPerProductionCount.get(applyProductionName), updateAttributesAndValuesPerProduction.get(checkProductionName), attributeVariablesMatch, attributeVariableToDisjunctionTest.get(checkProductionName), attributesAndValuesPerProductionCount.get(applyProductionName).get(variableHierarchy.get(applyProductionName).get(0)), attributesAndValuesPerProduction.get(checkProductionName).get(variableHierarchy.get(checkProductionName).get(0)), checkAttributesAndValuesPerProduction.get(checkProductionName).get(variableHierarchy.get(checkProductionName).get(0)));
                    }
                }
            }
        } while (repeat);
        return attributesAndValuesPerProductionCount;
    }

    /**
     * Condenses the variable information for all the different productions into one global collection
     * @param condensedAttributesValueCount Starts empty but is filled during production.  Maps variables to their finalized ASTCountWithValues needed for Uppaal's arrays
     * @param attributeValueCountPerProduction Mapping from production name to a mapping between variable and their ASTCountWithVariables.
     * @param variablesPerProductionContext Maps production name to a mapping between variable name and their path with ID
     */
    private static Map<String, ProductionVariables> condensedAttributesAndCollect(Map<String, ASTCountWithValues> condensedAttributesValueCount, Map<String, Map<String, ASTCountWithValues>> attributeValueCountPerProduction, Map<String, Map<String, String>> variablesPerProductionContext, Map<String, ProductionVariables> actualVariablesPerProduction) {
        HashSet<String> attributes = new HashSet<>();
        Map<String, ProductionVariables> variableToAnalyzeAttributes = new HashMap<>();
        for (String productionName : attributeValueCountPerProduction.keySet()) {
            Map<String, ASTCountWithValues> currentProductionToASTCountWithValues = attributeValueCountPerProduction.get(productionName);
            Map<String, String> variablesToPath = variablesPerProductionContext.get(productionName);
            ProductionVariables currentActualVariables = actualVariablesPerProduction.get(productionName);
            for (Map.Entry<String, ASTCountWithValues> variableToASTCountWithValues : currentProductionToASTCountWithValues.entrySet()) {
                ProductionVariables analyzeAttributes = variableToAnalyzeAttributes.get(variablesToPath.get(variableToASTCountWithValues.getKey()));
                if (analyzeAttributes == null) {
                    analyzeAttributes = new ProductionVariables(variablesToPath.get(variableToASTCountWithValues.getKey()));
                    variableToAnalyzeAttributes.put(variablesToPath.get(variableToASTCountWithValues.getKey()), analyzeAttributes);
                }
                variableToASTCountWithValues.getValue().collectEdges(variablesToPath, condensedAttributesValueCount, null, attributes, null, analyzeAttributes, currentActualVariables);
            }
        }
        return variableToAnalyzeAttributes;
    }

    /**
     * An array of values is needed for attribute for each identifier.  These arrays are all different sizes depending on the attribute and its identifier
     * These are currently stored in AV (Attribute Value) templates inside Uppaal.  This method collects the information to make it easy to instantiate them in the UppalSemanticVisitor
     * @param condensedAttributesValueCount Maps variables to their finalized ASTCountWithValues needed for Uppaal's arrays
     */
    private static LinkedList<UppaalAttributeValueTriad> collectAttributeTriads(Map<String, ASTCountWithValues> condensedAttributesValueCount) {
        LinkedList<UppaalAttributeValueTriad> AVCollection = new LinkedList<>();
        for (String variableNameWithID : condensedAttributesValueCount.keySet()) {
            condensedAttributesValueCount.get(variableNameWithID).createAVCollection(AVCollection, null);
        }
        return AVCollection;
    }

    /**
     * Soar uses characters that can't be interpreted by Uppaal.  This replaces those characters in Soar with ones that Uppaal can understand
     * Similarly, Uppaal can recognize characters that aren't used in Soar. These are used to indicate special variables in Uppaal
     * @param str String that needs to be analyzed
     * @return Corrected string with replaced characters
     */
    public static String simplifiedString(String str) {
        StringBuilder newString = new StringBuilder();
        for (int i = 0; i < str.length(); i++) {
            char newChar;
            switch (str.charAt(i)) {
                case '-': newChar = '_';
                          break;
                case '*': newChar = '_';
                          break;
                case '<': newChar = '$';
                          break;
                case '>': newChar = '$';
                          break;
                default: newChar = str.charAt(i);
                         break;
            }
            if (newString.length() > 0 && newString.charAt(newString.length() - 1) != '_' && newChar == '$' || (newString.length() > 0 && newString.charAt(newString.length() - 1) == '$')) {
                newString.append('_');
            }
            if (newString.length() > 0 || newChar != '$') {
                newString.append(newChar);
            }
        }
        return newString.toString();
    }

    /**
     * Using two visitors, a symbol visitor and a semantic visitor, translate Soar to Uppaal. The Symbol visitor
     * associates soar variables, e.g. <o> <s>, with attributes in the working memory tree.  All attributes, values and
     * variables are stored.  The Semantic visitor maps Soar productions to Uppaal templates.
     * @param soarSourceFile Provided by parseArgs
     * @throws IOException ANTLR throws error in the first line of the function if something is wrong with that process
     */
    private static LinkedList<UppaalAttributeValueTriad> getUPPAAL(String soarSourceFile) throws IOException {
        System.out.println("Running Translator 1 / 3 .....");
        SoarParser soarParseTree = new SoarParser(new CommonTokenStream(new SoarLexer(new ANTLRFileStream(soarSourceFile))));
        System.out.println("Running Translator 1 / 3 complete");
        System.out.println("Running Translator 2 / 3 .....");

        //Mirrors all of the variables in SymbolVisitor.  Refer to that file for their description
        //Changes that need to be made often start with adding the variable into the SymbolVisitor, accessing it here in this list, and passing it to the UppaalSemanticVisitor
        SymbolVisitor symbolVisitor = new SymbolVisitor(soarParseTree.soar());
        Set<String> stringAttributeNames = symbolVisitor.getStringSymbols();
        Set<String> boolAttributeNames = symbolVisitor.getBooleanSymbols();
        Map<String, ProductionVariables> actualVariablesPerProduction = symbolVisitor.getActualVariablesInProduction();
        Map<String, Map<String, AugmentedSymbolTree>> attributesAndValuesPerProduction = symbolVisitor.getAttributesAndValuesPerProduction();
        Map<String, Map<String, AugmentedSymbolTree>> checkAttributesAndValuesPerProduction = symbolVisitor.getCheckAttributesAndValuesPerProduction();
        Map<String, Map<String, AugmentedSymbolTree>> updateAttributesAndValuesPerProduction = symbolVisitor.getUpdateAttributesAndValuesPerProduction();
        Map<String, LinkedList<String>> variableHierarchy = symbolVisitor.getVariableHierarchy();
        Map<String, ProductionVariables> variablesCreatedOrUpdated = symbolVisitor.getVariablesCreatedOrUpdated();
        int numOperators = symbolVisitor.getOperatorCount();
        Map<String, Boolean> productionToOSupported = symbolVisitor.getProductionToOSupported();
        Map<String, Map<String, String[]>> attributeVariableToDisjunctionTestPerProduction = symbolVisitor.getAttributeVariableToDisjunctionTest();

        Map<String, Map<String, String>> variablesPerProductionContext = symbolVisitor.getGlobalVariableDictionary();

        soarParseTree.reset();

        stringAttributeNames = stringAttributeNames
                .stream()
                .map(name -> name.replace("-", "_"))
                .collect(Collectors.toSet());

        Map<String, Map<String, ASTCountWithValues>> attributeValueCountPerProduction = applyCheckAndUpdate(attributesAndValuesPerProduction, checkAttributesAndValuesPerProduction, updateAttributesAndValuesPerProduction, variableHierarchy, attributeVariableToDisjunctionTestPerProduction);

        HashSet<Integer> takenValues = new HashSet<>();
        Map<String, Map<String, String>> variablesToPathWithID = new HashMap<>();
        Map<String, Integer> variableIDToIndex = new HashMap<>();
        LinkedList<String> uppaalOperatorCollection = giveVariablesIDs(attributesAndValuesPerProduction, takenValues, variablesToPathWithID, variableIDToIndex, variablesPerProductionContext, variablesCreatedOrUpdated);

        Map<String, ASTCountWithValues> condensedAttributesValueCount = new HashMap<>();
        Map<String, ProductionVariables> variableToAnalyzeAttributes = condensedAttributesAndCollect(condensedAttributesValueCount, attributeValueCountPerProduction, variablesToPathWithID, actualVariablesPerProduction);
        variableToAnalyzeAttributes.values().forEach(e -> e.clean());

        LinkedList<UppaalAttributeValueTriad> AVCollection = collectAttributeTriads(condensedAttributesValueCount);

        Map<String, LinkedList<String>> variableToAttributes = new HashMap<>();
        for (String variable : condensedAttributesValueCount.keySet()) {
            variableToAttributes.put(variable, condensedAttributesValueCount.get(variable).getEdges());
        }

        System.out.println("Running Translator 2 / 3 complete");
        System.out.println("Running Translator 3 / 3 .....");
        soarParseTree.soar().accept(new UPPAALSemanticVisitor(outputFile, stringAttributeNames, variablesPerProductionContext, boolAttributeNames, numOperators, actualVariablesPerProduction, takenValues, uppaalOperatorCollection, AVCollection, variablesToPathWithID, productionToOSupported, variableToAttributes, attributeVariableToDisjunctionTestPerProduction));
        System.out.println("Running Translator 3 / 3 complete");
        return AVCollection;
    }

    /**
     * If the input or output files are not given via the CLI, a typical "Open File" dialog will spawn to determine the
     * unspecified values.
     * @param title Select Soar or Uppaal file
     * @return The name of the file
     */
    private static String getFileFromDialog(String title)
    {
        JFileChooser chooser = new JFileChooser();
        chooser.setDialogTitle(title);

        int returnVal = chooser.showOpenDialog(null);

        String filename = "";

        if(returnVal == JFileChooser.APPROVE_OPTION)
        {
            filename = chooser.getCurrentDirectory().getAbsolutePath() + File.separator + chooser.getSelectedFile().getName();
            System.out.println("Using File: " + filename);
        }
        else
        {
            System.exit(0);
        }
        return filename;
    }
}
