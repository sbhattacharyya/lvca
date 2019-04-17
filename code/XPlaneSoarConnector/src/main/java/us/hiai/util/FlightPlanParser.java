package us.hiai.util;

import org.antlr.v4.runtime.ANTLRFileStream;
import org.antlr.v4.runtime.CommonTokenStream;
import antlr4.FMSLexer;
import antlr4.FMSParser;

import java.io.IOException;
import java.util.LinkedList;

/** Parses provided .fms flight plan
 * Created by Daniel Griessler Spring 2019
 */
public class FlightPlanParser {
    public FlightPlan flightPlan;
    public int currentWaypoint;
    private Double currentHeading;

    public FlightPlanParser(String fmsInputFile) {
        try {
            FMSParser fmsParser = new FMSParser(new CommonTokenStream(new FMSLexer(new ANTLRFileStream(fmsInputFile))));
            flightPlan = new FMSCutter(fmsParser.fms()).fp;
            currentWaypoint = 0;
        } catch(IOException e) {
            e.printStackTrace();
        }
        currentHeading = null;
    }

    public void updateWaypoint(Double heading) {
        double EPSILON = 1;
        if (currentHeading != null && Math.abs(currentHeading - heading) > EPSILON && currentWaypoint + 1 < flightPlan.waypoints.size()) {
            currentWaypoint++;
        }
        currentHeading = heading;
    }

    public WaypointNode getCurrentWaypoint() {return flightPlan.waypoints.get(currentWaypoint);}

    public WaypointNode getHome() { return flightPlan.waypoints.get(0); }

    public void reverseWaypoints(LinkedList<WaypointNode> pathHome) {
        flightPlan = new FlightPlan(pathHome, flightPlan);
        currentWaypoint = 0;
        currentHeading = null;
    }
}
