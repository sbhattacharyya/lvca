package us.hiai.util;

import org.jetbrains.annotations.NotNull;
import us.hiai.util.Data_Structures_Book.Entry;
import us.hiai.util.Data_Structures_Book.HeapAdaptablePriorityQueue;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;

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
    private int[] polygonEnd;
    private GPS_Intersection gpsIntersect;
    private DoubInt[] nonPopulatedToHome;
    private DoubInt[] populatedToHome;
    private HashSet<Integer> hasNonpopulatedPathHome;

    public GraphPath(double[] home, GPS_Intersection gpsIntersect, String pathToPolygons) {
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
            } else {
                System.out.printf("Found storedGraphPath.txt in %s\n", pathToPolygons);
                System.out.println("Loading storedGraphPath.txt....");
                reader = new Scanner(stored);
                size = reader.nextInt();
            }
            elements = new Node[size];
            polygonEnd = new int[gpsIntersect.getLatArray().size()];
            elements[0] = new Node(home[0], home[1], -1);
            int index = 1;
            int indexEnd = 0;
            for (int i = 0; i < gpsIntersect.getLatArray().size(); i++) {
                int currentSize = gpsIntersect.getLatArray().get(i).size();
                for (int j = 0; j < currentSize; j++) {
                    elements[index++] = new Node(gpsIntersect.getLatArray().get(i).get(j), gpsIntersect.getLonArray().get(i).get(j), i);
                }
                polygonEnd[indexEnd++] = index - 1;
            }


            if (createdNewFile) {
                ArrayList<ArrayList<Pair>> graph = new ArrayList<>();
                for (int i = 0; i < size; i++) {
                    graph.add(new ArrayList<>());
                }
                for (int i = 0; i < elements.length; i++) {
                    for (int j = 0; j < elements.length; j++) {
                        if (j == i || elements[j].getPolygonIndex() == elements[i].getPolygonIndex()) {
                            if (elements[j].getPolygonIndex() != -1)
                                j = polygonEnd[elements[j].getPolygonIndex()];
                            continue;
                        }
                        if (graph.get(i).contains(new Pair(j, -1))) {
                            // I think this is sorted so you should be able to do a binary search instead of contains check
                            addEdge(i, j, graph);
                        }
                    }
                }
                nonPopulatedToHome = dijkstra(graph, size);
                writer =  new BufferedWriter(new FileWriter(stored));
                writer.write(size + " ");

                for (int i = 0; i < nonPopulatedToHome.length; i++) {
                    writer.write(nonPopulatedToHome[i].backNode + " " + nonPopulatedToHome[i].distance + " ");
                }

//                if (distances[distances.length - 1].distance == Double.MAX_VALUE) {
                Pair[][] graphMatrix = new Pair[size][size];
                for (int i = 0; i < graph.size(); i++) {
                    boolean[] touched = new boolean[size];
                    ArrayList<Pair> currentEdges = graph.get(i);
                    for(Pair next : currentEdges) {
                        graphMatrix[i][next.node] = next;
                        touched[next.node] = true;
                    }
                    for (int j = 0; j < touched.length; j++) {
                        if (!touched[j]) {
                            graphMatrix[i][j] = null;
                        }
                    }
                }
                for (int i = 0; i < elements.length; i++) {
                    for (int j = 0; j < elements.length; j++) {
                        if (j != i && graphMatrix[i][j] == null) {
                            addPopulatedEdge(i, j, graphMatrix);
                        }
                    }
                }

                populatedToHome = dijkstra(graphMatrix, size);

                for (int i = 0; i < populatedToHome.length; i++) {
                    writer.write(populatedToHome[i].backNode + " " + populatedToHome[i].distance + " " + populatedToHome[i].distanceOverPopulated + " ");
                }
                writer.close();

            } else {
                nonPopulatedToHome = new DoubInt[size];
                for (int i = 0; i < size; i++) {
                    nonPopulatedToHome[i] = new DoubInt(reader.nextInt(), reader.nextDouble());
                }
                populatedToHome = new DoubInt[size];
                for (int i = 0; i < size; i++) {
                    populatedToHome[i] = new DoubInt(reader.nextInt(), reader.nextDouble(), reader.nextDouble());
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
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private double[] getDistanceAndBearing(double lat1, double lon1, double lat2, double lon2) {
        double distanceToNode = GeometryLogistics.calculateDistanceToWaypoint(lat1, lon1, lat2, lon2);
        double currentBearing = GeometryLogistics.calculateBearing(lat1, lon1, lat2, lon2, false, null);
        return new double[]{distanceToNode, currentBearing};
    }

    private void addEdge(int indexNode1, int indexNode2, ArrayList<ArrayList<Pair>> graph) {
        double[] distanceAndBearing = getDistanceAndBearing(elements[indexNode1].getLat(), elements[indexNode1].getLon(), elements[indexNode2].getLat(), elements[indexNode2].getLon());
        if (!GeometryLogistics.checkLineIntersectsPolygon(elements[indexNode1].getLat(), elements[indexNode1].getLon(), distanceAndBearing[1], distanceAndBearing[0], gpsIntersect)) {
            graph.get(indexNode1).add(new Pair(indexNode2, distanceAndBearing[0]));
//            graph.get(indexNode2).add(new Pair(indexNode1, distanceAndBearing[0]));
        }
    }

    private void addPopulatedEdge(int indexNode1, int indexNode2, Pair[][] graphMatrix) {
        double[] distanceAndBearing = getDistanceAndBearing(elements[indexNode1].getLat(), elements[indexNode1].getLon(), elements[indexNode2].getLat(), elements[indexNode2].getLon());
        double distanceIntersectsPolygon = GeometryLogistics.countDistanceIntersectsPolygon(elements[indexNode1].getLat(), elements[indexNode1].getLon(), distanceAndBearing[1], distanceAndBearing[0], gpsIntersect);
        graphMatrix[indexNode1][indexNode2] = new Pair(indexNode2, distanceAndBearing[0], distanceIntersectsPolygon);
        graphMatrix[indexNode2][indexNode1] = new Pair(indexNode1, distanceAndBearing[0], distanceIntersectsPolygon);
    }
    private static final double EPSILON = 1;
    static class Pair implements Comparable<Pair> {
        int node;
        double distance;
        double distanceOverPopulated;
        Pair(int node, double distance) {
            this.node = node;
            this.distance = distance;
            this.distanceOverPopulated = 0;
        }
        Pair(int node, double distance, double distanceOverPopulated) {
            this.node = node;
            this.distance = distance;
            this.distanceOverPopulated = distanceOverPopulated;
        }
        @Override
        public int compareTo(@NotNull Pair otherPair) {
            if (this.node < otherPair.node) {
                return -1;
            } else if (this.node > otherPair.node) {
                return 1;
            } else {
                if (Math.abs(this.distanceOverPopulated - otherPair.distanceOverPopulated) < EPSILON) {
                    return Double.compare(this.distance, otherPair.distance);
                }
                else if (this.distanceOverPopulated < otherPair.distanceOverPopulated) {
                    return -1;
                } else {
                    return 1;
                }
            }
        }
    }

    private DoubInt[] dijkstra(ArrayList<ArrayList<Pair>> graph, int maxSize) {
        DoubInt[] dist = new DoubInt[graph.size()];
        dist[0] = new DoubInt(0, 0.0);
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

    static class DoubInt {
        int backNode;
        double distance;
        Double distanceOverPopulated;
        DoubInt(int backNode, double distance) {
            this(backNode, distance, null);
        }
        DoubInt(int backNode, double distance, Double distanceOverPopulated) {
            this.backNode = backNode;
            this.distance = distance;
            this.distanceOverPopulated = distanceOverPopulated;
        }
    }

    private DoubInt[] dijkstra(Pair[][] graphMatrix, int maxSize) {
        DoubInt[] dist = new DoubInt[graphMatrix.length];
        dist[0] = new DoubInt(-1, 0.0, 0.0);
        for (int i = 1; i < dist.length; i++) {
            dist[i] = new DoubInt(-1, Double.MAX_VALUE, Double.MAX_VALUE);
        }

        HeapAdaptablePriorityQueue<Integer,Pair> pq = new HeapAdaptablePriorityQueue<>();
        Entry<Integer, Pair> inserted = pq.insert(0, new Pair(0, 0, 0));
        HashMap<Integer,Entry<Integer, Pair>> insertedPairs = new HashMap<>();
        insertedPairs.put(0, inserted);

        Set<Integer> settled = new HashSet<>();
        while (settled.size() != maxSize) {
            Entry<Integer, Pair> min = pq.removeMin();
            int u = min.getKey();
            settled.add(u);
            double edgeDistance;
            double newDistance;
            double distanceOverPopulated;
            double newDistanceOverPopulated;
            for (int i = 0; i < graphMatrix[u].length; i++) {
                Pair v = graphMatrix[u][i];
                if (v == null) {
                    continue;
                }
                if (!settled.contains(v.node)) {
                    edgeDistance = v.distance;
                    distanceOverPopulated = v.distanceOverPopulated;
                    newDistance = dist[u].distance + edgeDistance;
                    newDistanceOverPopulated = dist[u].distanceOverPopulated + distanceOverPopulated;
                    if (newDistanceOverPopulated < dist[v.node].distanceOverPopulated || (Math.abs(newDistanceOverPopulated - dist[v.node].distanceOverPopulated) < EPSILON && newDistance < dist[v.node].distance)) {
                        dist[v.node].backNode = u;
                        dist[v.node].distance = newDistance;
                        dist[v.node].distanceOverPopulated = newDistanceOverPopulated;
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

    public LinkedList<WaypointNode> findPathHome(double planeLat, double planeLon) {
        double minDistanceHome = Double.MAX_VALUE;
        int nodeHome = -1;
        LinkedList<WaypointNode> directionsHome = null;
        for (Integer node : hasNonpopulatedPathHome) {
            double[] distanceAndBearing = getDistanceAndBearing(planeLat, planeLon, elements[node].getLat(), elements[node].getLon());
            if (!GeometryLogistics.checkLineIntersectsPolygon(planeLat, planeLon, distanceAndBearing[1], distanceAndBearing[0], gpsIntersect)) {
                minDistanceHome = Math.min(minDistanceHome, distanceAndBearing[0] + nonPopulatedToHome[node].distance);
                nodeHome = node;
            }
        }
        if (nodeHome == -1) {
            minDistanceHome = Double.MAX_VALUE;
            for (int i = 0; i < populatedToHome.length; i++) {
                double[] distanceAndBearing = getDistanceAndBearing(planeLat, planeLon, elements[i].getLat(), elements[i].getLon());
                double distanceIntersectsPolygon = GeometryLogistics.countDistanceIntersectsPolygon(planeLat, planeLon, distanceAndBearing[1], distanceAndBearing[0], gpsIntersect);
                double sumDistance = distanceIntersectsPolygon + populatedToHome[i].distanceOverPopulated;
                if (sumDistance < minDistanceHome) {
                    directionsHome = backTrace(populatedToHome, i);
                    if (directionsHome != null) {
                        minDistanceHome = sumDistance;
                        nodeHome = i;
                    }
                }
            }
        } else {
            directionsHome = backTrace(nonPopulatedToHome, nodeHome);
        }
        assert(nodeHome != -1);


        return directionsHome;
    }

}
