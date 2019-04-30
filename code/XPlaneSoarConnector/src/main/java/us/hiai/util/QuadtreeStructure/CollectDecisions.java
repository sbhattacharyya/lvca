package us.hiai.util.QuadtreeStructure;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;

import us.hiai.util.GeometryLogistics;
import us.hiai.util.WaypointNode;

public class CollectDecisions {
    private HashMap<WaypointNode, Decision> previousDecisions;
    private String pathToQuadtree;
    public CollectDecisions(String pathToQuadtree) {
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

    public void addDecision(WaypointNode point, String decision, Integer value) {
        previousDecisions.put(point, new Decision(decision, value));
        save();
    }

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
