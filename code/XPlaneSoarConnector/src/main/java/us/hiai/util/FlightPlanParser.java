package us.hiai.util;

import org.antlr.v4.runtime.ANTLRFileStream;
import org.antlr.v4.runtime.CommonTokenStream;
import antlr4.FMSLexer;
import antlr4.FMSParser;

import java.io.IOException;

/** Parses provided .fms flight plan
 * Created by Daniel Griessler Spring 2019
 */
public class FlightPlanParser {
    public FlightPlan flightPlan;
    public int currentWaypoint;
    private Double currentHeading;
    private static double EPSILON = 0.01;
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
        if (currentHeading == null) {
            currentHeading = heading;
        } else if (Math.abs(currentHeading - heading) > EPSILON && currentWaypoint + 1 < flightPlan.waypoints.size()) {
            currentWaypoint++;
        }
    }

    public WaypointNode getCurrentWaypoint() {return flightPlan.waypoints.get(currentWaypoint);}

    public WaypointNode getNextWaypoint() { return flightPlan.waypoints.get(currentWaypoint + 1); }

    public void reverseWaypoints() {
        flightPlan = new FlightPlan(flightPlan, currentWaypoint);
        currentWaypoint = 0;
        currentHeading = null;
    }
}
