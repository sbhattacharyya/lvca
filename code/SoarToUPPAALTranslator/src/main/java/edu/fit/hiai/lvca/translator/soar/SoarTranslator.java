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
import java.util.ArrayList;
import java.util.Map;
import java.util.Set;
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

    private static boolean compareUpdateToCreate(SymbolTree update, SymbolTree create) {
        for (SymbolTree attributeTree : update.getChildren()) {
            if (attributeTree.name.equals("update")) {
                continue;
            }
            SymbolTree otherChildSubtree = create.getSubtreeNoError(attributeTree.name);
            if (otherChildSubtree == null) {
                return false;
            } else {
                for (SymbolTree valueTree : attributeTree.getChildren()) {
                    SymbolTree searchSourceOther = otherChildSubtree.getSubtreeNoError(valueTree.name);
                    if (searchSourceOther == null) {
                        return false;
                    }
                }
            }
        }
        return true;
    }

    private static void replaceAttributeValuesWithIndexes(SymbolTree operatorTree, SymbolVisitor sv) {
        for (int i = 0; i < operatorTree.getChildren().size(); i++) {
            SymbolTree topValue = operatorTree.getChildren().get(i);
            if (!topValue.name.equals("update") && topValue.name.charAt(0) != '[') {
                for (SymbolTree valueTree : topValue.getChildren()) {
                    sv.createAttributeValuePair(topValue.name, valueTree.name, operatorTree);
                }
                operatorTree.getChildren().remove(i);
            }
        }
    }

    private static SymbolTree checkCreateContinue(String name, SymbolTree base, boolean continueLoop[]) {
        SymbolTree checkIfExists = base.getSubtreeNoError(name);
        if (checkIfExists == null) {
            checkIfExists = new SymbolTree(name);
            base.addChild(checkIfExists);
            continueLoop[0] = true;
        }
        return checkIfExists;
    }

    private static void expandOperators(ArrayList<SymbolTree> operators, SymbolVisitor sv) {
        SymbolTree createOperators = new SymbolTree("create");
        SymbolTree updateOperators = new SymbolTree("update");
        for (SymbolTree productionTree : operators) {
            for (SymbolTree operatorTree : productionTree.getChildren()) {
                if (operatorTree.getSubtreeNoError("create") != null) {
                    createOperators.addChild(operatorTree);
                } else {
                    SymbolTree updateChild = operatorTree.getSubtreeNoError("update");
                    if (updateChild != null && updateChild.getChildren().size() != 0) {
                        updateOperators.addChild(operatorTree);
                    }
                    replaceAttributeValuesWithIndexes(operatorTree, sv);
                }
            }
        }
        boolean keepUpdating[] = new boolean[1];
        while (keepUpdating[0]) {
            keepUpdating[0] = false;
            for (SymbolTree baseUpdate : updateOperators.getChildren()) {
                for (SymbolTree baseCreate : createOperators.getChildren()) {
                    if (compareUpdateToCreate(baseUpdate, baseCreate)) {
                        SymbolTree updateBranch = baseUpdate.getSubtree("update");
                        for (SymbolTree baseValueUpdate : updateBranch.getChildren()) {
                            SymbolTree baseValueCreate = checkCreateContinue(baseValueUpdate.name, baseCreate, keepUpdating);
                            for (SymbolTree lowerValueUpdate : baseValueUpdate.getChildren()) {
                                checkCreateContinue(lowerValueUpdate.name, baseValueCreate, keepUpdating);
                            }
                        }
                    }
                }
            }
        }
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
        ArrayList<SymbolTree> operators = symbolVisitor.getOperators();
        ArrayList<ArrayList<String>> operatorsAttributesAndValues = symbolVisitor.getOperatorAttributesAndValues();
        int numOperators = symbolVisitor.getOPERATOR_ID();

        Map<String, Map<String, String>> variablesPerProductionContext = symbolVisitor.getGlobalVariableDictionary();

        soarParseTree.reset();

        stringAttributeNames = stringAttributeNames
                .stream()
                .map(name -> name.replace("-", "_"))
                .collect(Collectors.toSet());

        expandOperators(operators, symbolVisitor);

        soarParseTree.soar().accept(new UPPAALSemanticVisitor(stringAttributeNames, variablesPerProductionContext, boolAttributeNames, operators, numOperators));
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
