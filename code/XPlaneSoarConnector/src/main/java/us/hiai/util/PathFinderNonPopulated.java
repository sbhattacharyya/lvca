package us.hiai.util;

import java.util.concurrent.Callable;

/**
 * Used to multi-thread the calculation from the plane's location to each non-populated node
 */
public class PathFinderNonPopulated implements Callable<GraphPath.DoubInt> {

    private PackedPathFinder input;

    PathFinderNonPopulated(PackedPathFinder ppf){
        this.input=ppf;
    }

    /**
     * Checks to see if the path between the plane and the provided point will cross through any populated areas
     * @return Either null indicating that it passes through a populated area or the node and the distance that would be required to fly from the starting location to home using this node
     */
    @Override
    public GraphPath.DoubInt call() {
        double[] distanceAndBearing = input.gp.getDistanceAndBearing(input.planeLat, input.planeLon, input.gp.getElements()[input.node].getLat(), input.gp.getElements()[input.node].getLon());
        if (!GeometryLogistics.checkLineIntersectsPolygon(input.planeLat, input.planeLon, distanceAndBearing[1], distanceAndBearing[0], input.gp.getGpsIntersect())) {
            return new GraphPath.DoubInt(input.node, distanceAndBearing[0] + input.gp.getNonPopulatedToHome()[input.node].distance);
        }
        return null;
    }
}
