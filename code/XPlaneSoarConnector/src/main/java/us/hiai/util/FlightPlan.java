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
    FlightPlan(FlightPlan copy, int lastWaypoint) {
        this.builder = copy.builder;
        this.versionNumber = copy.versionNumber;
        this.numberOfUserDefinedWaypoints = copy.numberOfUserDefinedWaypoints;
        waypoints = new LinkedList<>();
        if (lastWaypoint < copy.waypoints.size()) {
            for(int i = lastWaypoint; i >= 0; i--) {
                waypoints.add(copy.waypoints.get(i));
            }
        }
    }
    public void addWaypoint(WaypointNode newWaypointNode) {
        waypoints.add(newWaypointNode);
    }
}
