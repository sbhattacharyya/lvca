package us.hiai.util;

import org.jetbrains.annotations.NotNull;
import us.hiai.util.Data_Structures_Book.Entry;
import us.hiai.util.Data_Structures_Book.HeapAdaptablePriorityQueue;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;
import java.util.concurrent.*;

/**
 * Created by Daniel Griessler Spring 2019
 *
 */
public class GraphPath {
    static class Node {
        private double lat;
        private double lon;
        int polygonIndex;
        Node(double lat, double lon, int polygonIndex) {
            this.lat = lat;
            this.lon = lon;
            this.polygonIndex = polygonIndex;
        }
        public double getLat() {
            return lat;
        }

        public double getLon() {
            return lon;
        }

        int getPolygonIndex() {
            return polygonIndex;
        }
    }

    private Node[] elements;
    private GPS_Intersection gpsIntersect;
    private DoubInt[] nonPopulatedToHome;
    private DoubInt[] populatedToHome;
    private HashSet<Integer> hasNonpopulatedPathHome;

    public Node[] getElements() {return elements;}
    GPS_Intersection getGpsIntersect() {return gpsIntersect;}
    DoubInt[] getNonPopulatedToHome() {return nonPopulatedToHome;}
    public DoubInt[] getPopulatedToHome() {return populatedToHome;}
    public HashSet<Integer> getHasNonpopulatedPathHome() {return hasNonpopulatedPathHome;}

    int[] fillElements(int currentIndex, ArrayList<ArrayList<Double>> latArray, ArrayList<ArrayList<Double>> lonArray, int polygon) {
        for (int i = 0; i < latArray.size(); i++) {
            int currentSize = lonArray.get(i).size();
            for (int j = 0; j < currentSize; j++) {
                elements[currentIndex++] = new Node(latArray.get(i).get(j), lonArray.get(i).get(j), polygon);
            }
//            polygonEnd[polygonEndIndex++] = currentIndex - 1;
            polygon++;
        }
        return new int[]{currentIndex, /*polygonEndIndex,*/ polygon};
    }

    GraphPath(double[] home, GPS_Intersection gpsIntersect, String pathToPolygons) {
        this.gpsIntersect = gpsIntersect;
        File stored = new File(pathToPolygons + "/storedGraphPath.txt");
        try {
            boolean createdNewFile = stored.createNewFile();
            BufferedWriter writer;
            Scanner reader = null;
            int size;
            if (createdNewFile) {
                System.out.printf("Can't find storedGraphPath.txt in %s\n", pathToPolygons);
                System.out.printf("Creating new file... %s/storedGraphPath.txt\n", pathToPolygons);
                size = 1;
                for (ArrayList<Double> nextList : gpsIntersect.getLatArray()) {
                    size += nextList.size();
                }
                for (ArrayList<Double> nextList : gpsIntersect.getLightlyPopulatedLatArray()) {
                    size += nextList.size();
                }
            } else {
                System.out.printf("Found storedGraphPath.txt in %s\n", pathToPolygons);
                System.out.println("Loading storedGraphPath.txt....");
                reader = new Scanner(stored);
                size = reader.nextInt();
            }
            elements = new Node[size];
            elements[0] = new Node(home[0], home[1], -1);
            int[] currentIndexAndPolygonIndex = fillElements(1, gpsIntersect.getLatArray(), gpsIntersect.getLonArray(), 0);
            fillElements(currentIndexAndPolygonIndex[0], gpsIntersect.getLightlyPopulatedLatArray(), gpsIntersect.getLightlyPopulatedLonArray(), currentIndexAndPolygonIndex[1]);


            if (createdNewFile) {
                ArrayList<ArrayList<Pair>> graph = new ArrayList<>();
                Pair[][] graphMatrix = new Pair[size][size];
                for (int i = 0; i < size; i++) {
                    graph.add(new ArrayList<>());
                }
                double totalTime = System.nanoTime();
                LinkedList<Future<PackedArgs>> futures = new LinkedList<>();
                long startIndex = 0;
                long iteration = Math.round(elements.length / 5.0);
                for (int i = 0; i < 4; i++) {
                    long sum = startIndex + iteration;
                    System.out.println(startIndex + " " + sum + " " + elements.length);
                        Future<PackedArgs> ff = Executors.newSingleThreadExecutor().submit(new edgeCreator(startIndex, sum, graph, graphMatrix, elements, gpsIntersect));
                        futures.add(ff);
                        startIndex += iteration;
                }
                System.out.println(startIndex + " " + elements.length + " " + elements.length);
                new edgeCreator(startIndex, elements.length, graph, graphMatrix, elements, gpsIntersect).call();
                System.out.printf("Main finished in %f time\n", (System.nanoTime() - totalTime) / 6e+10);
                while (futures.size() != 0) {
                    for (int i = 0; i < futures.size(); i++) {
                        if (futures.get(i).isDone()) {
                            futures.remove(i);
                            i--;
                            System.out.printf("Future %d finished in %f time\n", i, (System.nanoTime() - totalTime) / 6e+10); // have done threads start back up and help the threads that are still running dummy and perhaps more below with the dijkstra?
                        }
                    }
                    Thread.sleep(120000);
                }
                nonPopulatedToHome = dijkstra(graph, size);
                writer =  new BufferedWriter(new FileWriter(stored));
                writer.write(size + " ");

                for (DoubInt doubInt : nonPopulatedToHome) {
                    writer.write(doubInt.backNode + " " + doubInt.distance + " ");
                }

                populatedToHome = dijkstra(graphMatrix, size);

                for (DoubInt doubInt : populatedToHome) {
                    writer.write(doubInt.backNode + " " + doubInt.distance + " " + doubInt.distanceOverPopulated[0] + " " + doubInt.distanceOverPopulated[1] + " ");
                }
                writer.close();

            } else {
                nonPopulatedToHome = new DoubInt[size];
                for (int i = 0; i < size; i++) {
                    nonPopulatedToHome[i] = new DoubInt(reader.nextInt(), reader.nextDouble());
                }
                populatedToHome = new DoubInt[size];
                for (int i = 0; i < size; i++) {
                    populatedToHome[i] = new DoubInt(reader.nextInt(), reader.nextDouble(), new double[]{reader.nextDouble(), reader.nextDouble()});
                }
                reader.close();
                System.out.println("storedGraphPath.txt Loaded");

            }
            hasNonpopulatedPathHome = new HashSet<>();
            hasNonpopulatedPathHome.add(0);
            for (int i = 1; i < size; i++) {
                if (hasNonpopulatedPathHome.contains(nonPopulatedToHome[i].backNode)) {
                    hasNonpopulatedPathHome.add(i);
                }
            }

        } catch (IOException | InterruptedException e) {
            e.printStackTrace();
        }
    }

    static class PackedArgs {
        int firstIndex;
        int secondIndex;
        ArrayList<ArrayList<Pair>> myGraph;
        Pair[][] myGraphMatrix;
        Node[] myElements;
        GPS_Intersection myIntersect;
        PackedArgs(long firstIndex, long secondIndex, ArrayList<ArrayList<Pair>> myGraph, Pair[][] myGraphMatrix, Node[] myElements, GPS_Intersection myIntersect) {
            this.firstIndex = (int)firstIndex;
            this.secondIndex = (int)secondIndex;
            this.myGraph = myGraph;
            this.myGraphMatrix = myGraphMatrix;
            this.myElements = myElements;
            this.myIntersect = myIntersect;
        }
    }

    static class edgeCreator implements Callable<PackedArgs> {
        PackedArgs input;
        edgeCreator(long firstIndex, long secondIndex, ArrayList<ArrayList<Pair>> myGraph, Pair[][] myGraphMatrix, Node[] myElements, GPS_Intersection myIntersect) {
            input = new PackedArgs(firstIndex, secondIndex, myGraph, myGraphMatrix, myElements, myIntersect);
        }
        @Override
        public PackedArgs call() {
            for (int i = input.firstIndex; i < input.secondIndex; i++) {
                for (int j = i+1; j < input.myElements.length; j++) { // 46853.76019194752   155.63187714189166
                    double distanceToNode = GeometryLogistics.calculateDistanceToWaypoint(input.myElements[i].getLat(), input.myElements[i].getLon(), input.myElements[j].getLat(), input.myElements[j].getLon());
                    double currentBearing = GeometryLogistics.calculateBearing(input.myElements[i].getLat(), input.myElements[i].getLon(), input.myElements[j].getLat(), input.myElements[j].getLon(), false, null);
                    double[] distanceIntersectsPolygon = GeometryLogistics.countDistanceIntersectsPolygon(input.myElements[i].getLat(), input.myElements[i].getLon(), currentBearing, distanceToNode, input.myIntersect);
                    input.myGraphMatrix[i][j] = new Pair(j, distanceToNode, distanceIntersectsPolygon);
                    input.myGraphMatrix[j][i] = new Pair(i, distanceToNode, distanceIntersectsPolygon);
                    if (distanceIntersectsPolygon[0] < EPSILON) {
                        input.myGraph.get(i).add(new Pair(j, distanceToNode));
                        input.myGraph.get(j).add(new Pair(i, distanceToNode));
                    }
                }
            }
            return null;
        }
    }

    private static final double EPSILON = 1;
    static class Pair implements Comparable<Pair> {
        int node;
        double distance;
        double[] distanceOverEachArea;
        Pair(int node, double distance) {
            this.node = node;
            this.distance = distance;
            this.distanceOverEachArea = new double[2];
        }
        Pair(int node, double distance, double[] distanceOverEachArea) {
            this.node = node;
            this.distance = distance;
            if (distanceOverEachArea == null) {
                this.distanceOverEachArea = new double[2];
            } else {
                this.distanceOverEachArea = new double[]{distanceOverEachArea[0], distanceOverEachArea[1]};
            }
        }
        @Override
        public int compareTo(@NotNull Pair otherPair) {
            if (this.node < otherPair.node) {
                return -1;
            } else if (this.node > otherPair.node) {
                return 1;
            } else {
                if (Math.abs(this.distanceOverEachArea[0] - otherPair.distanceOverEachArea[0]) < EPSILON) {
                    if (Math.abs(this.distanceOverEachArea[1] - otherPair.distanceOverEachArea[1]) < EPSILON) {
                        return Double.compare(this.distance, otherPair.distance);
                    } else if (this.distanceOverEachArea[1] < otherPair.distanceOverEachArea[1]) {
                        return -1;
                    } else {
                        return 1;
                    }
                }
                else if (this.distanceOverEachArea[0] < otherPair.distanceOverEachArea[0]) {
                    return -1;
                } else {
                    return 1;
                }
            }
        }
    }

    private DoubInt[] dijkstra(ArrayList<ArrayList<Pair>> graph, int maxSize) {
        DoubInt[] dist = new DoubInt[graph.size()];
        dist[0] = new DoubInt(-2, 0.0);
        for (int i = 1; i < dist.length; i++) {
            dist[i] = new DoubInt(-1, Double.MAX_VALUE);
        }
        HeapAdaptablePriorityQueue<Integer,Pair> pq = new HeapAdaptablePriorityQueue<>();
        Entry<Integer, Pair> inserted = pq.insert(0, new Pair(0, 0));
        HashMap<Integer,Entry<Integer, Pair>> insertedPairs = new HashMap<>();
        insertedPairs.put(0, inserted);

        Set<Integer> settled = new HashSet<>();
        while (settled.size() != maxSize && pq.size() > 0) {
            Entry<Integer, Pair> min = pq.removeMin();
            insertedPairs.remove(min.getKey());
            int u = min.getKey();
            settled.add(u);
            double edgeDistance;
            double newDistance;
            for (int i = 0; i < graph.get(u).size(); i++) {
                Pair v = graph.get(u).get(i);
                if (!settled.contains(v.node)) {
                    edgeDistance = v.distance;
                    newDistance = dist[u].distance + edgeDistance;
                    if (newDistance < dist[v.node].distance)
                        dist[v.node].backNode = u;
                        dist[v.node].distance = newDistance;
                    if (insertedPairs.get(v.node) == null) {
                        Entry<Integer, Pair> newInsert = pq.insert(v.node, new Pair(v.node, dist[v.node].distance));
                        insertedPairs.put(v.node, newInsert);
                    } else {
                        pq.replaceValue(insertedPairs.get(v.node), new Pair(v.node, dist[v.node].distance));
                    }
                }
            }
        }
        return dist;
    }

    static class DoubInt implements Comparable<DoubInt> {
        int backNode;
        double distance;
        double[] distanceOverPopulated;
        DoubInt(int backNode, double distance) {
            this(backNode, distance, null);
        }
        DoubInt(int backNode, double distance, double[] distanceOverPopulated) {
            this.backNode = backNode;
            this.distance = distance;
            if (distanceOverPopulated == null) {
                this.distanceOverPopulated = null;
            } else {
                this.distanceOverPopulated = new double[]{distanceOverPopulated[0], distanceOverPopulated[1]};
            }
        }
        @Override
        public int compareTo(@NotNull DoubInt otherDoubInt) {
            if (distanceOverPopulated == null) {
                return Double.compare(this.distance, otherDoubInt.distance);
            }
            if (Math.abs(this.distanceOverPopulated[0] - otherDoubInt.distanceOverPopulated[0]) < EPSILON) {
                if (Math.abs(this.distanceOverPopulated[1] - otherDoubInt.distanceOverPopulated[1]) < EPSILON) {
                    return Double.compare(this.distance, otherDoubInt.distance);
                } else if (this.distanceOverPopulated[1] < otherDoubInt.distanceOverPopulated[1]) {
                    return -1;
                } else {
                    return 1;
                }
            }
            else if (this.distanceOverPopulated[0] < otherDoubInt.distanceOverPopulated[0]) {
                return -1;
            } else {
                return 1;
            }
        }
    }

    private DoubInt[] dijkstra(Pair[][] graphMatrix, int maxSize) {
        DoubInt[] dist = new DoubInt[graphMatrix.length];
        dist[0] = new DoubInt(-2, 0.0, new double[]{0.0, 0.0});
        for (int i = 1; i < dist.length; i++) {
            dist[i] = new DoubInt(-1, Double.MAX_VALUE, new double[]{Double.MAX_VALUE, Double.MAX_VALUE});
        }

        HeapAdaptablePriorityQueue<Integer,Pair> pq = new HeapAdaptablePriorityQueue<>();
        Entry<Integer, Pair> inserted = pq.insert(0, new Pair(0, 0, new double[]{0, 0}));
        HashMap<Integer,Entry<Integer, Pair>> insertedPairs = new HashMap<>();
        insertedPairs.put(0, inserted);

        Set<Integer> settled = new HashSet<>();
        while (settled.size() != maxSize) {
            Entry<Integer, Pair> min = pq.removeMin();
            int u = min.getKey();
            settled.add(u);
            double edgeDistance;
            double[] distanceOverPopulated;
            DoubInt temp = new DoubInt(-2, -1, new double[]{0.0, 0.0});
            for (int i = 0; i < graphMatrix[u].length; i++) {
                Pair v = graphMatrix[u][i];
                if (v == null) {
                    continue;
                }
                if (!settled.contains(v.node)) {
                    edgeDistance = v.distance;
                    distanceOverPopulated = v.distanceOverEachArea;
                    temp.distance = dist[u].distance + edgeDistance;
                    temp.distanceOverPopulated[0] = dist[u].distanceOverPopulated[0] + distanceOverPopulated[0];
                    temp.distanceOverPopulated[1] = dist[u].distanceOverPopulated[1] + distanceOverPopulated[1];
                    if (temp.compareTo(dist[v.node]) < 0) {
                        dist[v.node].backNode = u;
                        dist[v.node].distance = temp.distance;
                        dist[v.node].distanceOverPopulated[0] = temp.distanceOverPopulated[0];
                        dist[v.node].distanceOverPopulated[1] = temp.distanceOverPopulated[1];
                    }
                    if (insertedPairs.get(v.node) == null) {
                        Entry<Integer, Pair> newInsert = pq.insert(v.node, new Pair(v.node, dist[v.node].distance, dist[v.node].distanceOverPopulated));
                        insertedPairs.put(v.node, newInsert);
                    } else {
                        pq.replaceValue(insertedPairs.get(v.node), new Pair(v.node, dist[v.node].distance, dist[v.node].distanceOverPopulated));
                    }
                }
            }
        }
        return dist;
    }

    private LinkedList<WaypointNode> backTrace(DoubInt[] directionsHome, int startNode) {
        LinkedList<WaypointNode> path = new LinkedList<>();
        DoubInt current = directionsHome[startNode];
        path.add(new WaypointNode(elements[startNode].lat, elements[startNode].lon));
        while (current.backNode != -2) {
            if (current.backNode == -1) {
                return null;
            }
            path.add(new WaypointNode(elements[current.backNode].lat, elements[current.backNode].lon));
            current = directionsHome[current.backNode];
        }
        return path;
    }

    double[] getDistanceAndBearing(double lat1, double lon1, double lat2, double lon2) {
        double distanceToNode = GeometryLogistics.calculateDistanceToWaypoint(lat1, lon1, lat2, lon2);
        double currentBearing = GeometryLogistics.calculateBearing(lat1, lon1, lat2, lon2, false, null);
        return new double[] {distanceToNode, currentBearing};
    }

//    public LinkedList<WaypointNode> findPathHome(double planeLat, double planeLon) {
//        double startTime = System.nanoTime();
//        double minDistanceHome = Double.MAX_VALUE;
//        int nodeHome = -1;
//        LinkedList<WaypointNode> directionsHome;
//        for (Integer node : hasNonpopulatedPathHome) {
//            double[] distanceAndBearing = getDistanceAndBearing(planeLat, planeLon, elements[node].getLat(), elements[node].getLon());
//            if (!GeometryLogistics.checkLineIntersectsPolygon(planeLat, planeLon, distanceAndBearing[1], distanceAndBearing[0], gpsIntersect)) {
//                double sumDist = distanceAndBearing[0] + nonPopulatedToHome[node].distance;
//                if (sumDist < minDistanceHome) {
//                    minDistanceHome = sumDist;
//                    nodeHome = node;
//                }
//            }
//        }
//        if (nodeHome == -1) {
//            double[] minIntersects = new double[]{Double.MAX_VALUE, Double.MAX_VALUE};
//            double[] sumDistance = new double[2];
//            for (int i = 0; i < populatedToHome.length; i++) {
//                double[] distanceAndBearing = getDistanceAndBearing(planeLat, planeLon, elements[i].getLat(), elements[i].getLon());
//                double[] distanceIntersectsPolygon = GeometryLogistics.countDistanceIntersectsPolygon(planeLat, planeLon, distanceAndBearing[1], distanceAndBearing[0], gpsIntersect);
//                sumDistance[0] = distanceIntersectsPolygon[0] + populatedToHome[i].distanceOverPopulated[0];
//                sumDistance[1] = distanceIntersectsPolygon[1] + populatedToHome[i].distanceOverPopulated[1];
//                if (sumDistance[0] < minIntersects[0] || ((sumDistance[0] - minIntersects[0]) < EPSILON && sumDistance[1] < minIntersects[1])) {
//                    minIntersects[0] = sumDistance[0];
//                    minIntersects[1] = sumDistance[1];
//                    nodeHome = i;
//                }
//            }
//            assert(nodeHome != -1);
//            directionsHome = backTrace(populatedToHome, nodeHome);
//        } else {
//            directionsHome = backTrace(nonPopulatedToHome, nodeHome);
//        }
//
//        System.out.printf("Path finding took: %f\n", (System.nanoTime() - startTime) / 6e+10);
//        return directionsHome;
//    }

    public LinkedList<WaypointNode> findPathHome(double planeLat, double planeLon) {
        double startTime = System.nanoTime();
        double minDistanceHome = Double.MAX_VALUE;
        int nodeHome = -1;
        LinkedList<WaypointNode> directionsHome;

        ExecutorService executor = Executors.newFixedThreadPool(4);
        Set<Future<DoubInt>> set = new HashSet<>();
//        System.out.println("Entering find path home calculation");

        if (hasNonpopulatedPathHome.size() != 0) {
            for (Integer node : hasNonpopulatedPathHome) {
                Callable<DoubInt> worker = new PathFinderNonPopulated(new PackedPathFinder(planeLat, planeLon, this, node));
                Future<DoubInt> future = executor.submit(worker);
                set.add(future);
//                System.out.println("Nonpopulated Added thread " + node);
            }
//            int out = 0;
            for (Future<DoubInt> nextOut : set) {
                DoubInt val = null;
                try {
                    val = nextOut.get();
                } catch (InterruptedException | ExecutionException e) {
                    e.printStackTrace();
                }
                if (val != null && val.distance < minDistanceHome) {
                    minDistanceHome = val.distance;
                    nodeHome = val.backNode;
                }
//                System.out.println("NonpopulatedProcessed thread " + out++);
            }
        }
        if (nodeHome == -1) {
            double[] minIntersects = new double[]{Double.MAX_VALUE, Double.MAX_VALUE};
            for (int i = 0; i < populatedToHome.length; i++) {
                Callable<DoubInt> worker = new PathFinderPopulated(new PackedPathFinder(planeLat, planeLon, this, i));
                Future<DoubInt> future = executor.submit(worker);
                set.add(future);
//                System.out.println("Added thread " + i);
            }
//            int out = 1;
            for (Future<DoubInt> nextOut : set) {
                DoubInt val = null;
                try {
                    val = nextOut.get();
                } catch (InterruptedException | ExecutionException e) {
                    e.printStackTrace();
                }
                if (val != null && (val.distanceOverPopulated[0] < minIntersects[0] || ((val.distanceOverPopulated[0] - minIntersects[0]) < EPSILON && val.distanceOverPopulated[1] < minIntersects[1]))) {
                    minIntersects[0] = val.distanceOverPopulated[0];
                    minIntersects[1] = val.distanceOverPopulated[1];
                    nodeHome = val.backNode;
                }
//                System.out.println("Processed thread " + out++);
            }
            directionsHome = backTrace(populatedToHome, nodeHome);
        } else {
            directionsHome = backTrace(nonPopulatedToHome, nodeHome);
        }

        System.out.printf("Path finding took: %f\n", (System.nanoTime() - startTime) / 6e+10);
        System.out.flush();
        return directionsHome;
    }

}
