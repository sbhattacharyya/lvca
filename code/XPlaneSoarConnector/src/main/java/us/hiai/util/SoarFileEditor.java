package us.hiai.util;
import org.jsoar.kernel.Agent;
import org.jsoar.kernel.Production;
import org.jsoar.kernel.ProductionType;

import java.io.*;
import java.util.HashSet;

public class SoarFileEditor {
    private HashSet<String> productionNames;
    private File soarFile;

    public SoarFileEditor(String pathToSoar, Agent runningSoarAgent) {
        productionNames = new HashSet<>();
        for (Production nextProduction: runningSoarAgent.getProductions().getProductions(ProductionType.USER)) {
            productionNames.add(nextProduction.getName());
        }
        this.soarFile = new File(pathToSoar);
    }

    public void addProduction(String[] productionAndProductionName) {
        if (productionAndProductionName[0] != null && productionAndProductionName[1] != null && !productionNames.contains(productionAndProductionName[1])) {
            productionNames.add(productionAndProductionName[1]);
            save(productionAndProductionName[0]);
        }
    }

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
