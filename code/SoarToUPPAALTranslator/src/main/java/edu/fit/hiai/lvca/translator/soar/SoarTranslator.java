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
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
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

        Map<String, Map<String, String>> variablesPerProductionContext = symbolVisitor.getGlobalVariableDictionary();

        soarParseTree.reset();

        stringAttributeNames = stringAttributeNames
                .stream()
                .map(name -> name.replace("-", "_"))
                .collect(Collectors.toSet());

//        UPPAALCreator uppaalCreator = new UPPAALCreator(stringAttributeNames, soarParseTree.soar(), variablesPerProductionContext, boolAttributeNames);
//        return uppaalCreator.getXML();
        soarParseTree.soar().accept(new UPPAALSemanticVisitor(stringAttributeNames, variablesPerProductionContext, boolAttributeNames, operators));
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
