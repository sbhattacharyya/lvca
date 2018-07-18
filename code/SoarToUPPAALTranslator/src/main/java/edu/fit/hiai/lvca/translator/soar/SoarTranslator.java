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
     * @param args
     * @throws IOException
     */
    public static void main(String[] args) throws IOException
    {
        parseArgs(args);

        getUPPAAL(soarSourceFile);
    }

    /**
     * Using Apache Commons CLI.  Debug Flag uses Antlr's "TestRig" class to spawn a window that shows the parse tree.
     * @param args
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

    private static LinkedList<String> giveVariablesIDs(Map<String, Map<String, AugmentedSymbolTree>> attributesAndValuesPerProduction, HashSet<Integer> takenValues, Map<String, Map<String, String>> variablesToPathWithID, Map<String, Integer> variableIDToIndex, Map<String, Map<String, String>> variablesPerProductionContext, Map<String, ProductionVariables> actualVariablesPerProduction) {
        LinkedList<String> variableNames = new LinkedList<>();
        for (String individualProduction : attributesAndValuesPerProduction.keySet()) {
            Map<String, String> newVariablesMap = new HashMap<>();
            variablesToPathWithID.put(individualProduction, newVariablesMap);
            Map<String, AugmentedSymbolTree> currentAttributesAndValues = attributesAndValuesPerProduction.get(individualProduction);
            Map<String, String> currentVariables = variablesPerProductionContext.get(individualProduction);
            ProductionVariables actualVariables = actualVariablesPerProduction.get(individualProduction);
            for (String individualVariable : currentAttributesAndValues.keySet()) {
                currentAttributesAndValues.get(individualVariable).makeIDs(takenValues, newVariablesMap, variableIDToIndex, currentVariables, actualVariables, variableNames);
                if (currentVariables.get(individualVariable).equals("state")) {
                    newVariablesMap.put(individualVariable, "state_-1");
                }
            }
        }
        return variableNames;
    }

    private static boolean variablesMatch(Map<String, AugmentedSymbolTree> checkMap, Map<String, AugmentedSymbolTree> attributeMap, LinkedList<String> checkVariableDictionary, String attributeStateVariable, HashMap<String, String> attributeVariablesMatch, Map<String, String[]> attributeVariableToDisjunctionTest) {
        Map<String, SymbolTree> productionVariableComparison = new HashMap<>();
        productionVariableComparison.put(checkVariableDictionary.get(0), new SymbolTree(attributeStateVariable));
        if (checkMap.get(checkVariableDictionary.get(0)).matches(attributeMap.get(attributeStateVariable), productionVariableComparison, attributeVariableToDisjunctionTest)) {
            attributeVariablesMatch.put(attributeStateVariable, checkVariableDictionary.get(0));
            for (int i = 1; i < checkVariableDictionary.size(); i++) {
                String variableName = checkVariableDictionary.get(i);
                SymbolTree comparisonCollection = productionVariableComparison.get(variableName);
                int numMatches = 0;
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

    private static boolean applyVariables(Map<String, ASTCountWithValues> attributesAndValuesPerProductionCount, Map<String, AugmentedSymbolTree> applyMap, HashMap<String, String> attributeVariablesMatch, Map<String, String[]> attributeVariableToDisjunctionTest) {
        boolean somethingChanged = false;
        for (String attributeVariable : attributeVariablesMatch.keySet()) {
            String keyApplyMap = attributeVariablesMatch.get(attributeVariable);
            if (applyMap.get(keyApplyMap) != null && applyMap.get(keyApplyMap).makeCount(attributesAndValuesPerProductionCount.get(attributeVariable), false, attributeVariableToDisjunctionTest) && !somethingChanged) {
                somethingChanged = true;
            }
        }
        return somethingChanged;
    }

    private static boolean isEmpty(Map<String, AugmentedSymbolTree> map) {
        for (AugmentedSymbolTree AST : map.values()) {
            if (AST.getEdgeNameToEdge().size() > 0) {
                return false;
            }
        }
        return true;
    }

    private static Map<String, Map<String, ASTCountWithValues>> getAttributesAndValuesPerProductionCount(Map<String, Map<String, AugmentedSymbolTree>> attributesAndValuesPerProduction, Map<String, String[]> attributeVariableToDisjunctionTest) {
        Map<String, Map<String, ASTCountWithValues>> attributesAndValuesPerProductionCount = new HashMap<>();
        for(String productionName : attributesAndValuesPerProduction.keySet()) {
            Map<String, ASTCountWithValues> currentAttributesAndValuesCount = new HashMap<>();
            attributesAndValuesPerProductionCount.put(productionName, currentAttributesAndValuesCount);
            Map<String, AugmentedSymbolTree> currentAttributesAndValues = attributesAndValuesPerProduction.get(productionName);
            for (String variable : currentAttributesAndValues.keySet()) {
                ASTCountWithValues variableCountTree = new ASTCountWithValues(variable);
                currentAttributesAndValues.get(variable).makeCount(variableCountTree, false, attributeVariableToDisjunctionTest);
                currentAttributesAndValuesCount.put(variable, variableCountTree);
            }
        }
        return attributesAndValuesPerProductionCount;
    }

    private static Map<String, Map<String, ASTCountWithValues>> applyCheckAndUpdate(Map<String, Map<String, AugmentedSymbolTree>> attributesAndValuesPerProduction, Map<String, Map<String, AugmentedSymbolTree>> checkAttributesAndValuesPerProduction, Map<String, Map<String, AugmentedSymbolTree>> updateAttributesAndValuesPerProduction, Map<String, LinkedList<String>> variableHierarchy, Map<String, String[]> attributeVariableToDisjunctionTest) {
        LinkedList<String> productionNames = new LinkedList<>(attributesAndValuesPerProduction.keySet());
        for (int i = 0; i < productionNames.size(); i++) {
            if (isEmpty(updateAttributesAndValuesPerProduction.get(productionNames.get(i)))) {
                productionNames.remove(i);
                i--;
            }
        }

        Map<String, Map<String, ASTCountWithValues>> attributesAndValuesPerProductionCount = getAttributesAndValuesPerProductionCount(attributesAndValuesPerProduction, attributeVariableToDisjunctionTest);

        boolean repeat = false;
        do {
            for (String productionName : productionNames) {
                for (String productionName2 : attributesAndValuesPerProduction.keySet()) {
                    if (productionName.equals(productionName2) || attributesAndValuesPerProduction.get(productionName2).size() == 0) {
                        continue;
                    }
                    HashMap<String, String> attributeVariablesMatch = new HashMap<>();
                    if (variablesMatch(checkAttributesAndValuesPerProduction.get(productionName), attributesAndValuesPerProduction.get(productionName2), variableHierarchy.get(productionName), variableHierarchy.get(productionName2).get(0), attributeVariablesMatch, attributeVariableToDisjunctionTest)) {
                        repeat = applyVariables(attributesAndValuesPerProductionCount.get(productionName2), updateAttributesAndValuesPerProduction.get(productionName), attributeVariablesMatch, attributeVariableToDisjunctionTest);
                    }
                }
            }
        } while (repeat);
        return attributesAndValuesPerProductionCount;
    }

    public static void condensedAttributesAndCollect(Map<String, ASTCountWithValues> condensedAttributesValueCount, Map<String, Map<String, ASTCountWithValues>> attributeValueCountPerProduction, Map<String, Map<String, String>> variablesPerProductionContext, Map<String, Integer> attributesToIDs) {
        HashSet<String> attributes = new HashSet<>();

        for (String productionName : attributeValueCountPerProduction.keySet()) {
            Map<String, ASTCountWithValues> currentProductionToASTCountWithValues = attributeValueCountPerProduction.get(productionName);
            Map<String, String> variablesToPath = variablesPerProductionContext.get(productionName);
            for (ASTCountWithValues currentASTCountWithVariables : currentProductionToASTCountWithValues.values()) {
                currentASTCountWithVariables.collectEdges(variablesToPath, condensedAttributesValueCount, null, attributes);
            }
        }

        int attributeIndex = 1;
        for (String nextAttribute : attributes) {
            attributesToIDs.put(nextAttribute, attributeIndex++);
        }
    }

    public static void collectAttributeTriads(LinkedList<UppaalAttributeValueTriad> AVCollection, Map<String, ASTCountWithValues> condensedAttributesValueCount, Map<String, Integer> attributesToIDs) {
        for (String variableNameWithID : condensedAttributesValueCount.keySet()) {
            condensedAttributesValueCount.get(variableNameWithID).createAVCollection(AVCollection, null, attributesToIDs);
        }
    }

    public static String simplifiedString(String str) {
        return str.replace("-", "_").replace("*", "_");
    }

    /**
     * Using two visitors, a symbol visitor and a semantic visitor, translate Soar to Uppaal. The Symbol visitor
     * associates soar variables, e.g. <o> <s>, with attributes in the working memory tree.  All attributes, values and
     * variables are stored.  The Semantic visitor maps Soar productions to Uppaal templates.
     * @param soarSourceFile
     * @return
     * @throws IOException
     */
    private static void getUPPAAL(String soarSourceFile) throws IOException
    {
        SoarParser soarParseTree = new SoarParser(new CommonTokenStream(new SoarLexer(new ANTLRFileStream(soarSourceFile))));

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
        int maxQuerySize = symbolVisitor.getMaxQuerySize();
        Map<String, Boolean> productionToOSupported = symbolVisitor.getProductionToOSupported();
        Map<String, String[]> attributeVariableToDisjunctionTest = symbolVisitor.getAttributeVariableToDisjunctionTest();

        Map<String, Map<String, String>> variablesPerProductionContext = symbolVisitor.getGlobalVariableDictionary();

        soarParseTree.reset();

        stringAttributeNames = stringAttributeNames
                .stream()
                .map(name -> name.replace("-", "_"))
                .collect(Collectors.toSet());

        Map<String, Map<String, ASTCountWithValues>> attributeValueCountPerProduction = applyCheckAndUpdate(attributesAndValuesPerProduction, checkAttributesAndValuesPerProduction, updateAttributesAndValuesPerProduction, variableHierarchy, attributeVariableToDisjunctionTest);

        HashSet<Integer> takenValues = new HashSet<>();
        Map<String, Map<String, String>> variablesToPathWithID = new HashMap<>();
        Map<String, Integer> variableIDToIndex = new HashMap<>();
        LinkedList<String> uppaalOperatorCollection = giveVariablesIDs(attributesAndValuesPerProduction, takenValues, variablesToPathWithID, variableIDToIndex, variablesPerProductionContext, variablesCreatedOrUpdated);

        Map<String, Integer> attributesToIDs = new HashMap<>();
        Map<String, ASTCountWithValues> condensedAttributesValueCount = new HashMap<>();
        condensedAttributesAndCollect(condensedAttributesValueCount, attributeValueCountPerProduction, variablesToPathWithID, attributesToIDs);

        LinkedList<UppaalAttributeValueTriad> AVCollection = new LinkedList<>();
        collectAttributeTriads(AVCollection, condensedAttributesValueCount, attributesToIDs);

        Map<String, Integer> variableToNumAttributes = new HashMap<>();
        for (String variable : condensedAttributesValueCount.keySet()) {
            variableToNumAttributes.put(variable, condensedAttributesValueCount.get(variable).getNumEdges());
        }

        soarParseTree.soar().accept(new UPPAALSemanticVisitor(stringAttributeNames, variablesPerProductionContext, boolAttributeNames, numOperators, actualVariablesPerProduction, takenValues, uppaalOperatorCollection, AVCollection, variablesToPathWithID, attributesToIDs, maxQuerySize, productionToOSupported, variableToNumAttributes));
    }

    /**
     * If the input or output files are not given via the CLI, a typical "Open File" dialog will spawn to determine the
     * unspecified values.
     * @param title
     * @return
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
