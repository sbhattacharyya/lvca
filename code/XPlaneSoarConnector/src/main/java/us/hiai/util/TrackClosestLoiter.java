package us.hiai.util;

import org.jetbrains.annotations.NotNull;
import us.hiai.agents.DroneAgentSingleThread;
import us.hiai.util.Data_Structures_Book.Entry;
import us.hiai.util.Data_Structures_Book.HeapAdaptablePriorityQueue;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;
import java.util.concurrent.*;

/**
 * Constantly tracks the closest non-populated point that can be used as a loiter point as needed
 */
public class TrackClosestLoiter implements Runnable {

    /**
     * Used to package information about distances
     * Again, similar to DoubInt and Pair except for the lack of a node and a different compare method
     * Really should be combined with the other structures
     */
    static class Distances implements Comparable<Distances> {
        double distanceTo;
        double[] distanceOverPolygons;
        Distances(double distanceTo, double[] distanceOverPolygons) {
            this.distanceTo = distanceTo;
            this.distanceOverPolygons = distanceOverPolygons;
        }
        private static final double EPSILON = 1;
        @Override
        public int compareTo(@NotNull Distances distances) {
            if (Math.abs(this.distanceOverPolygons[0] - distances.distanceOverPolygons[0]) < EPSILON) {
                if (Math.abs(this.distanceOverPolygons[1] - distances.distanceOverPolygons[1]) < EPSILON) {
                    return Double.compare(this.distanceTo, distances.distanceTo);
                } else if (this.distanceOverPolygons[1] < distances.distanceOverPolygons[1]) {
                    return -1;
                } else {
                    return 1;
                }
            }
            else if (this.distanceOverPolygons[0] < distances.distanceOverPolygons[0]) {
                return -1;
            } else {
                return 1;
            }
        }
    }

    private HeapAdaptablePriorityQueue<Distances, WaypointNode> loiterPoints = new HeapAdaptablePriorityQueue<>();
    private ArrayList<Entry<Distances, WaypointNode>> insertedPoints = new ArrayList<>();
    private double[] lastCalcLatAndLon;
    private DroneAgentSingleThread dast;

    /**
     * Initializes global variables needed for the threading and sets the first loiter to be the home node to start
     * @param dast pointer to the DroneAgentSingleThread needed because passing the values themselves weren't being updated as the DroneAgent was running
     */
    public TrackClosestLoiter(DroneAgentSingleThread dast) {
        this.dast = dast;
        lastCalcLatAndLon = new double[]{dast.getData().lat, dast.getData().lon};
        for(int i = 0; i < dast.getFlightWeb().getElements().length; i++) {
            WaypointNode newInput = dast.getFlightWeb().getElements()[i].getPoint();
            Entry<Distances, WaypointNode> newInsert = loiterPoints.insert(new Distances(dast.getFlightWeb().getPopulatedToHome()[i].distance, dast.getFlightWeb().getPopulatedToHome()[i].distanceOverPopulated), newInput);
            insertedPoints.add(newInsert);
        }
        updateClosestLoiter();
    }

    /**
     * Updates the closest loiter point stored in the DroneAgentSingleThread
     */
    private void updateClosestLoiter() {
        dast.getClosestLoiterPoint().getClosestLoiterPoint().setLatitude(loiterPoints.min().getValue().getLatitude());
        dast.getClosestLoiterPoint().getClosestLoiterPoint().setLongitude(loiterPoints.min().getValue().getLongitude());
    }

    /**
     * Packaged output for DistanceCalculator
     */
    static class DistancesCalculatorOutput {
        int index;
        Distances distances;
        DistancesCalculatorOutput(int index, Distances distances) {
            this.index = index;
            this.distances = distances;
        }
    }

    /**
     * Calculates the distance information between the plane and each circle-able point
     * Construction similar to PathFinderPopulated so they can probably be combined with minor modifications
     */
    static class DistancesCalculator implements Callable<DistancesCalculatorOutput> {

        double[] currentLatAndLon;
        WaypointNode inputPoint;
        GPS_Intersection myIntersect;
        int index;
        DistancesCalculator(int index, double[] currentLatAndLon, WaypointNode inputPoint, GPS_Intersection myIntersect) {
            this.index = index;
            this.currentLatAndLon = currentLatAndLon;
            this.inputPoint = inputPoint;
            this.myIntersect = myIntersect;
        }

        /**
         * Calculates between the plane and the provided node the total distance, the distance that will pass through lightly populated polygons, and the distance that will pass through fully populated areas
         * @return the distances and the node
         */
        @Override
        public DistancesCalculatorOutput call() {
            double distanceToNode = GeometryLogistics.calculateDistanceToWaypoint(currentLatAndLon[0], currentLatAndLon[1], inputPoint.getLatitude(), inputPoint.getLongitude());
            double currentBearing = GeometryLogistics.calculateBearing(currentLatAndLon[0], currentLatAndLon[1], inputPoint.getLatitude(), inputPoint.getLongitude(), false, null);
            double[] distanceOverPolygons = GeometryLogistics.countDistanceIntersectsPolygon(currentLatAndLon[0], currentLatAndLon[1], currentBearing, distanceToNode, myIntersect);
            return new DistancesCalculatorOutput(index, new Distances(distanceToNode, distanceOverPolygons));
        }
    }

    /**
     * While told to keep calculating, it continually spins up a thread pool to find the closest point to loiter around
     * The goal was to do the calculation every nautical mile but the calculation isn't fast enough as seen by the output
     */
    @Override
    public void run() {
        while(dast.getClosestLoiterPoint().isKeepCalculating()) {
            double[] currentLatAndLon = new double[]{dast.getData().lat, dast.getData().lon};
            double distanceToLastCalc = GeometryLogistics.calculateDistanceToWaypoint(currentLatAndLon[0], currentLatAndLon[1], lastCalcLatAndLon[0], lastCalcLatAndLon[1]);
            if (distanceToLastCalc >= GeometryLogistics.NM_METERS) {
                double start = System.nanoTime();
                ExecutorService executor = Executors.newFixedThreadPool(4);
                Set<Future<DistancesCalculatorOutput>> set = new HashSet<>();
                for(int i = 0; i < insertedPoints.size(); i++) {
                    Callable<DistancesCalculatorOutput> worker = new DistancesCalculator(i, currentLatAndLon, insertedPoints.get(i).getValue(), dast.getGpsIntersect());
                    Future<DistancesCalculatorOutput> future = executor.submit(worker);
                    set.add(future);
                }
                for (Future<DistancesCalculatorOutput> nextOut : set) {
                    if (!dast.getClosestLoiterPoint().isKeepCalculating()) {
                        nextOut.cancel(true);
                    } else {
                        DistancesCalculatorOutput val = null;
                        try {
                            val = nextOut.get();
                        } catch (InterruptedException | ExecutionException e) {
                            e.printStackTrace();
                        }
                        if (val != null) {
                            loiterPoints.replaceKey(insertedPoints.get(val.index), val.distances);
                        }
                    }
                }
                System.out.printf("Tracking took in seconds: %f\t\tYou flew nm from last point: %f\n", (System.nanoTime() - start) / 1e+9, GeometryLogistics.calculateDistanceToWaypoint(lastCalcLatAndLon[0], lastCalcLatAndLon[1], dast.getData().lat, dast.getData().lon) / GeometryLogistics.NM_METERS);
                lastCalcLatAndLon[0] = currentLatAndLon[0];
                lastCalcLatAndLon[1] = currentLatAndLon[1];
                updateClosestLoiter();
            }
        }
        System.out.println("Stopped tracking!");
    }
}
