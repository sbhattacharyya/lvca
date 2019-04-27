package us.hiai.util.QuadtreeStructure;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.HashSet;
import java.util.Scanner;

import us.hiai.util.GeometryLogistics;
import us.hiai.util.GraphPath.Node;
import us.hiai.util.WaypointNode;

public class CollectDecisions {
    private HashSet<Decision> previousDecisions;
    private String pathToQuadtree;
    private Node[] elements;
    public CollectDecisions(String pathToQuadtree, Node[] elements) {
        this.pathToQuadtree = pathToQuadtree;
        this.elements = elements;
        File stored = new File(pathToQuadtree + "/storedDecisions.txt");
        try {
            if (stored.createNewFile()) {
                System.out.printf("Can't find storedDecisions.txt in %s\n", pathToQuadtree);
                System.out.printf("Creating new file... %s/storedDecisions.txt\n", pathToQuadtree);

            } else {
                System.out.printf("Found storedDecisions.txt in %s\n", pathToQuadtree);
                System.out.println("Loading storedDecisions.txt....");
                Scanner reader = new Scanner(stored);
                int size = reader.nextInt();
                for (int i = 0; i < size; i++) {
                    int nextPointIndex = reader.nextInt();
                    reader.next();
                    String nextDecision = reader.next();
                    previousDecisions.add(new Decision(nextPointIndex, nextDecision));
                }
                reader.close();
                System.out.println("storedDecisions.txt Loaded");
            }

        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private WaypointNode getPosOfDecision(Decision ref) {
        return elements[ref.getPoint()].getPoint();
    }

    public String getClosestDecision(double planeLat, double planeLon, double maxDistance) {
        String minDecision = null;
        double minDistance = Double.MAX_VALUE;
        for (Decision next : previousDecisions) {
            WaypointNode currentDecisionPos = getPosOfDecision(next);
            double distanceToDecisionPoint = GeometryLogistics.calculateDistanceToWaypoint(planeLat, planeLon, currentDecisionPos.getLatitude(), currentDecisionPos.getLongitude());
            if (distanceToDecisionPoint <= maxDistance && distanceToDecisionPoint < minDistance) {
                minDecision = next.getDecision();
                minDistance = distanceToDecisionPoint;
            }
        }
        return minDecision;
    }

    public void save() {
        File stored = new File(pathToQuadtree + "/storedDecisions.txt");
        try {
            BufferedWriter writer =  new BufferedWriter(new FileWriter(stored));
            writer.write(previousDecisions.size() + " ");
            for (Decision nextDecision : previousDecisions) {
                writer.write(nextDecision.getPoint() + " " + nextDecision.decision + " ");
            }
            writer.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
