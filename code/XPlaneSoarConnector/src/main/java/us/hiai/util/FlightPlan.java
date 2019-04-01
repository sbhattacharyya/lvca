package us.hiai.util;

import java.util.LinkedList;

public class FlightPlan {
    char builder;
    int versionNumber;
    int numberOfUserDefinedWaypoints;
    public LinkedList<WaypointNode> waypoints;
    FlightPlan() {
        waypoints = new LinkedList<>();
    }
    FlightPlan(LinkedList<WaypointNode> pathHome, FlightPlan copy) {
        this.builder = copy.builder;
        this.versionNumber = copy.versionNumber;
        this.numberOfUserDefinedWaypoints = copy.numberOfUserDefinedWaypoints;
        waypoints = pathHome;
    }
    public void addWaypoint(WaypointNode newWaypointNode) {
        waypoints.add(newWaypointNode);
    }
}
