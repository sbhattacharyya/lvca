package us.hiai;

import us.hiai.agents.DroneAgentSingleThread;

/**
 * Created by Daniel Griessler Spring 2019
 * Modification of StartAgents which starts only the DroneAgentSingleThread
 * The paths to the files are hardcoded right now but they can be accepted as arguments to the program
 */
public class StartAgentsSingleThread
{

    public static void main(String[] args) {
        DroneAgentSingleThread da = new DroneAgentSingleThread();
        String flightPlanLocation = "/home/dgriessl/X-Plane 11/Output/FMS plans/DallasOut156.fms";
        String runningDir = System.getProperty("user.dir");
        runningDir = runningDir.substring(0, runningDir.lastIndexOf('/'));
        String pathToPolygons = runningDir + "/XPlaneSoarConnector/src/main/java/us/hiai/util/populatedAreas";
        String soarFilePath = runningDir + "/SoarToUPPAALTranslator/src/main/Soar/TestXPlaneDrone.soar";
        String pathToQuadtrees = runningDir + "/XPlaneSoarConnector/src/main/java/us/hiai/util/QuadtreeStructure";
        da.start(flightPlanLocation, pathToPolygons, soarFilePath, pathToQuadtrees);
    }

}
