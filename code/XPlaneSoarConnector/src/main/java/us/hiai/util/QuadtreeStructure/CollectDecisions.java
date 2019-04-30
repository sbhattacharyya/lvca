package us.hiai.util.QuadtreeStructure;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;

import us.hiai.util.GeometryLogistics;
import us.hiai.util.WaypointNode;

/**
 * Collects together all the previous decisions to be accessed and then saves new decisions to be retrieved during the next execution
 * Testing and sampling in the beginning has very few saved decisions so a HashMap is adequate with O(N) time to retrieve a close decision when needed
 * To speed this up, a skip list quad tree can be constructed which is partially outlined in papers online.  This would allow for O(log(N)) access time and insertion
 * This is preferable for arbitrarily large sets of previous decision points that are at arbitrary locations.
 * Also, right now, new decisions are created for each point.  Only unique decisions should be stored so the save and retrieve methods can be amended to make it more space efficent for large sets
 */
public class CollectDecisions {
    private HashMap<WaypointNode, Decision> previousDecisions;
    private String pathToQuadtree;
    private int latestRuleNum;

    /**
     * Either creates a file to store new decisions if it doesn't exist, or opens the existing one and reads in the decisions into memory
     * This has to match the save method's input
     * @param pathToQuadtree path to where the saved decisions are stored/will be stored
     * @param latestRuleNum latest contingency number needed for human assisted learning of new contingencies
     */
    public CollectDecisions(String pathToQuadtree, int latestRuleNum) {
        this.latestRuleNum = latestRuleNum;
        this.pathToQuadtree = pathToQuadtree;
        previousDecisions = new HashMap<>();
        File stored = new File(pathToQuadtree + "/storedDecisions.txt");
        try {
            if (stored.createNewFile()) {
                System.out.printf("Can't find storedDecisions.txt in %s\n", pathToQuadtree);
                System.out.printf("Creating new file... %s/storedDecisions.txt\n", pathToQuadtree);

            } else {
                System.out.printf("Found storedDecisions.txt in %s\n", pathToQuadtree);
                System.out.println("Loading storedDecisions.txt....");
                Scanner reader = new Scanner(stored);
                try {
                    int size = reader.nextInt();
                    for (int i = 0; i < size; i++) {
                        double nextLat = reader.nextDouble();
                        double nextLon = reader.nextDouble();
                        String nextDecision = reader.next();
                        String nextValue = reader.next();
                        Integer realNextValue;
                        if (nextValue.equals("null")) {
                            realNextValue = null;
                        } else {
                            realNextValue = Integer.parseInt(nextValue);
                        }
                        previousDecisions.put(new WaypointNode(nextLat, nextLon), new Decision(nextDecision, realNextValue));
                    }
                } catch(NoSuchElementException ignored) {

                }
                reader.close();
                System.out.println("storedDecisions.txt Loaded");
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    /**
     * Retrieves the closest decision within the provided max distance
     * @param planeLat the current latitude of the plane
     * @param planeLon the current longitude of the plane
     * @param maxDistance the maximum distance that the point can be from the airplane
     * @return either the closest decision within maxDistance or null indicating there isn't a close enough decision
     */
    public Decision getClosestDecision(double planeLat, double planeLon, double maxDistance) {
        Decision minDecision = null;
        double minDistance = Double.MAX_VALUE;
        for (WaypointNode currentDecisionPos : previousDecisions.keySet()) {
            double distanceToDecisionPoint = GeometryLogistics.calculateDistanceToWaypoint(planeLat, planeLon, currentDecisionPos.getLatitude(), currentDecisionPos.getLongitude());
            if (distanceToDecisionPoint <= maxDistance && distanceToDecisionPoint < minDistance) {
                minDecision = previousDecisions.get(currentDecisionPos);
                minDistance = distanceToDecisionPoint;
            }
        }
        return minDecision;
    }

    /**
     * Adds a new decision to the current collection. Every time a new decision is added, the saved decision file is overwritten
     * Since the agent should only be learning once per flight, this should not be too obstructive
     * With the current small sample size, this provides no barrier. Given arbitrarily large sets of points, however, this implementation may need to be amended
     * @param point new WaypointNode where the decision was made
     * @param decision what decision was made
     * @param value the value associated with the decision or null indicating there is no value
     * @return The human-assisted learning new rule for a contingency that might not exist in the Soar agent yet and name of that rule or two null values indicating no new contingency
     */
    public String[] addDecision(WaypointNode point, String decision, Integer value) {
        previousDecisions.put(point, new Decision(decision, value));
        String newRule = null;
        String newRuleName = null;
        if (value != null && value > 1 && value < 8) {
            newRuleName = "C" + latestRuleNum + "-Start";
            // This construction is based on the construction of C2-Start and C3-Start in the current Soar agent.  Any edits there need to be reflected here.
            newRule =
                    "\nsp {drone*propose*operator*C" + latestRuleNum + "-Lost-Link-Start\n" +
                    "    \"In lightly populated area, should start a " + value + " minute timer and then turn around\"\n" +
                    "    (state <s> ^name droneFlight ^startContingency true -^contingencyComplete " + newRuleName + " ^io.input-link.flightdata <fd>)\n" +
                    "    (<fd> ^takeOver true ^populated << lightly fully >>)\n" +
                    "    -->\n" +
                    "    (<s> ^operator <o> +)\n" +
                    "    (<o> ^name " + newRuleName + "\n" +
                    "         ^timerLength " + value + ")\n" +
                    "    (write (crlf) |PROPOSE C" + latestRuleNum + "!|)\n" +
                    "}\n";
        }
        save();
        return new String[]{newRule, newRuleName};
    }

    /**
     * Saves current list of decisions into a file to be retrieved on later executions
     */
    public void save() {
        File stored = new File(pathToQuadtree + "/storedDecisions.txt");
        try {
            BufferedWriter writer =  new BufferedWriter(new FileWriter(stored));
            writer.write(previousDecisions.size() + " ");
            for (WaypointNode nextWaypoint : previousDecisions.keySet()) {
                Decision nextDecision = previousDecisions.get(nextWaypoint);
                Integer nextDecisionValue = nextDecision.value;
                String saveDecisionValue;
                if (nextDecisionValue == null) {
                    saveDecisionValue = "null ";
                } else {

                    saveDecisionValue = nextDecisionValue + " ";
                }
                String saveDecision;
                switch (nextDecision.decision) {
                    case "null":
                        saveDecision = "null";
                        break;
                    case "C2-Start":
                    case "C3-Start":
                        saveDecision = "timer";
                        break;
                    default:
                        saveDecision = nextDecision.decision;
                        break;
                }
                writer.write(nextWaypoint.getLatitude() + " " + nextWaypoint.getLongitude() + " " + saveDecision + " " + saveDecisionValue);
            }
            writer.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
