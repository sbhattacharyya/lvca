package us.hiai.util;

import java.util.concurrent.Callable;

/**
 * Used to multi-thread the calculation from the plane's location to each populated node
 */
public class PathFinderPopulated implements Callable<GraphPath.DoubInt> {
    private PackedPathFinder input;

    PathFinderPopulated(PackedPathFinder ppf){
        this.input=ppf;
    }

    /**
     * Calculates between the plane and the provided node the total distance, the distance that will pass through lightly populated polygons, and the distance that will pass through fully populated areas
     * @return a DoubInt indicating and each of the distances calculated
     */
    @Override
    public GraphPath.DoubInt call() {
        double distanceToNode = GeometryLogistics.calculateDistanceToWaypoint(input.planeLat, input.planeLon, input.gp.getElements()[input.node].getLat(), input.gp.getElements()[input.node].getLon());
        double currentBearing = GeometryLogistics.calculateBearing(input.planeLat, input.planeLon, input.gp.getElements()[input.node].getLat(), input.gp.getElements()[input.node].getLon(), false, null);
        double[] distanceIntersectsPolygon = GeometryLogistics.countDistanceIntersectsPolygon(input.planeLat, input.planeLon, currentBearing, distanceToNode, input.gp.getGpsIntersect());
        return new GraphPath.DoubInt(input.node, -1, new double[]{distanceIntersectsPolygon[0] + input.gp.getPopulatedToHome()[input.node].distanceOverPopulated[0], distanceIntersectsPolygon[1] + input.gp.getPopulatedToHome()[input.node].distanceOverPopulated[1]});
    }
}
