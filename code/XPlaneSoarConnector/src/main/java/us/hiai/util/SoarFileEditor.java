package us.hiai.util;
import org.jsoar.kernel.Agent;
import org.jsoar.kernel.Production;
import org.jsoar.kernel.ProductionType;

import java.io.*;
import java.util.HashSet;

/**
 * Class used to edit the Soar's rules for human-assisted learning
 */
public class SoarFileEditor {
    private HashSet<String> productionNames;
    private File soarFile;

    /**
     * Notes what productions already exist in the agent
     * @param pathToSoar path to the Soar agent
     * @param runningSoarAgent pointer to the currently running Agent
     */
    public SoarFileEditor(String pathToSoar, Agent runningSoarAgent) {
        productionNames = new HashSet<>();
        for (Production nextProduction: runningSoarAgent.getProductions().getProductions(ProductionType.USER)) {
            productionNames.add(nextProduction.getName());
        }
        this.soarFile = new File(pathToSoar);
    }

    /**
     * Adds a new production ("chunk") if it doesn't already exist in the rule set and appends it to the rule set
     * @param productionAndProductionName the full production and its name to be saved
     */
    public void addProduction(String[] productionAndProductionName) {
        if (productionAndProductionName[0] != null && productionAndProductionName[1] != null && !productionNames.contains(productionAndProductionName[1])) {
            productionNames.add(productionAndProductionName[1]);
            save(productionAndProductionName[0]);
        }
    }

    /**
     * Appends the new production to the end of the Soar file
     * @param newProduction production to be added
     */
    public void save(String newProduction) {
        try {
            BufferedWriter writer =  new BufferedWriter(new FileWriter(soarFile, true));
            writer.write(newProduction);
            writer.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
