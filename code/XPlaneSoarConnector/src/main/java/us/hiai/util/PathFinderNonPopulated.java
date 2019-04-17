package us.hiai.util;

import java.util.concurrent.Callable;

public class PathFinderNonPopulated implements Callable<GraphPath.DoubInt> {

    private PackedPathFinder input;

    PathFinderNonPopulated(PackedPathFinder ppf){
        this.input=ppf;
    }

    @Override
    public GraphPath.DoubInt call() {
        double[] distanceAndBearing = input.gp.getDistanceAndBearing(input.planeLat, input.planeLon, input.gp.getElements()[input.node].getLat(), input.gp.getElements()[input.node].getLon());
        if (!GeometryLogistics.checkLineIntersectsPolygon(input.planeLat, input.planeLon, distanceAndBearing[1], distanceAndBearing[0], input.gp.getGpsIntersect())) {
            return new GraphPath.DoubInt(input.node, distanceAndBearing[0] + input.gp.getNonPopulatedToHome()[input.node].distance);
        }
        return null;
    }
}
