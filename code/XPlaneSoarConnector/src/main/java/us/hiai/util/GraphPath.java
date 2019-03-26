package us.hiai.util;

import org.jetbrains.annotations.NotNull;

import java.util.*;

public class GraphPath {
    static class Node {
        double lat;
        double lon;
        int polygonIndex;
        public Node(double lat, double lon, int polygonIndex) {
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

        public int getPolygonIndex() {
            return polygonIndex;
        }
    }

    Node[] elements;
    int[] polygonEnd;
    GPS_Intersection gpsIntersect;

    public GraphPath(double[] plane, double[] destination, ArrayList<ArrayList<Double>> latPolygons, ArrayList<ArrayList<Double>> lonPolygons, GPS_Intersection gpsIntersect) {
        this.gpsIntersect = gpsIntersect;
        int size = 2;
        for (ArrayList<Double> nextList : latPolygons) {
            size += nextList.size();
        }
        elements = new Node[size];
        polygonEnd = new int[latPolygons.size()];
        elements[0] = new Node(plane[0], plane[1], -1);
        int index = 1;
        int indexEnd = 0;
        for (int i = 0; i < latPolygons.size(); i++) {
            size = latPolygons.get(i).size();
            for (int j = 0; j < size; j++) {
                elements[index++] = new Node(latPolygons.get(i).get(j), lonPolygons.get(i).get(j), i);
            }
            polygonEnd[indexEnd++] = index - 1;
        }
        elements[elements.length - 1] = new Node(destination[0], destination[1], -2);

        LinkedList<LinkedList<Pair>> graph = new LinkedList<>();
        for (int i = 0; i < size; i++) {
            graph.add(new LinkedList<>());
        }
        for(int i = 0; i < elements.length; i++) {
            for (int j = 0; j < elements.length; j++) {
                if (j != i && elements[j].getPolygonIndex() != elements[i].getPolygonIndex() && !graph.get(i).contains(new Pair(j, -1))) {
                    // I think this is sorted so you should be able to do a binary search instead of contains check
                    addEdge(i, j, graph);
                }
            }
        }

        double[] distances = dijkstra(graph, size);

        System.out.println("The shorted path from node :");
        for (int i = 0; i < distances.length; i++)
            System.out.printf("0 to %d is %.5f\n",  i, distances[i]);

        if (distances[distances.length - 1] == Double.MAX_VALUE) {
            Pair[][] graphMatrix = new Pair[size][size];
            for (int i = 0; i < graph.size(); i++) {
                boolean[] touched = new boolean[size];
                LinkedList<Pair> currentEdges = graph.get(i);
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

            DoubInt[] distancesAndPopulated = dijkstra(graphMatrix, size);

            System.out.println("The shorted path from node :");
            for (int i = 0; i < distances.length; i++)
                System.out.printf("0 to %d is %.5f intersecting %d populated areas\n", i, distancesAndPopulated[i].distance, distancesAndPopulated[i].numIntersections);
        }
    }

    private double[] getDistanceAndBearing(int indexNode1, int indexNode2) {
        double distanceToNode = GeometryLogistics.calculateDistanceToWaypoint(elements[indexNode1].getLat(), elements[indexNode1].getLon(), elements[indexNode2].getLat(), elements[indexNode2].getLon());
        double currentBearing = GeometryLogistics.calculateBearing(elements[indexNode1].getLat(), elements[indexNode1].getLon(), elements[indexNode2].getLat(), elements[indexNode2].getLon(), false, null);
        return new double[]{distanceToNode, currentBearing};
    }

    private void addEdge(int indexNode1, int indexNode2, LinkedList<LinkedList<Pair>> graph) {
        double[] distanceAndBearing = getDistanceAndBearing(indexNode1, indexNode2);
        if (!GeometryLogistics.checkLineIntersectsPolygon(elements[indexNode1].getLat(), elements[indexNode1].getLon(), distanceAndBearing[1], distanceAndBearing[0], gpsIntersect)) {
            graph.get(indexNode1).add(new Pair(indexNode2, distanceAndBearing[0]));
            graph.get(indexNode2).add(new Pair(indexNode1, distanceAndBearing[0]));
        }
    }

    private void addPopulatedEdge(int indexNode1, int indexNode2, Pair[][] graphMatrix) {
        double[] distanceAndBearing = getDistanceAndBearing(indexNode1, indexNode2);
        int numberOfIntersectedPolygons = GeometryLogistics.countLineIntersectsPolygon(elements[indexNode1].getLat(), elements[indexNode1].getLon(), distanceAndBearing[1], distanceAndBearing[0], gpsIntersect);
        graphMatrix[indexNode1][indexNode2] = new Pair(indexNode2, distanceAndBearing[0], numberOfIntersectedPolygons);
        graphMatrix[indexNode2][indexNode1] = new Pair(indexNode1, distanceAndBearing[0], numberOfIntersectedPolygons);
    }

    static class Pair implements Comparable<Pair> {
        int node;
        double distance;
        int populatedIntersections;
        Pair(int node, double distance) {
            this.node = node;
            this.distance = distance;
            this.populatedIntersections = 0;
        }
        Pair(int node, double distance, int populatedIntersections) {
            this.node = node;
            this.distance = distance;
            this.populatedIntersections = populatedIntersections;
        }
        @Override
        public int compareTo(@NotNull Pair otherPair) {
            if (this.node < otherPair.node) {
                return -1;
            } else if (this.node > otherPair.node) {
                return 1;
            } else {
                if (this.populatedIntersections < otherPair.populatedIntersections) {
                    return -1;
                } else if (this.populatedIntersections > otherPair.populatedIntersections) {
                    return 1;
                } else {
                    return Double.compare(this.distance, otherPair.distance);
                }
            }
        }
    }

    private double[] dijkstra(LinkedList<LinkedList<Pair>> graph, int maxSize) {
        double[] dist = new double[graph.size()];
        dist[0] = 0;
        for (int i = 1; i < dist.length; i++) {
            dist[i] = Double.MAX_VALUE;
        }
        PriorityQueue<Pair> pq = new PriorityQueue<>(maxSize);
        pq.add(new Pair(0, 0));

        Set<Integer> settled = new HashSet<>();
        while (settled.size() != maxSize) {
            int u = pq.remove().node;
            settled.add(u);
            double edgeDistance;
            double newDistance;
            for (int i = 0; i < graph.get(u).size(); i++) {
                Pair v = graph.get(u).get(i);
                if (!settled.contains(v.node)) {
                    edgeDistance = v.distance;
                    newDistance = dist[u] + edgeDistance;
                    if (newDistance < dist[v.node])
                        dist[v.node] = newDistance;
                    pq.add(new Pair(v.node, dist[v.node]));
                }
            }
        }
        return dist;
    }

    static class DoubInt {
        double distance;
        int numIntersections;
        DoubInt(double distance, int numIntersections) {
            this.distance = distance;
            this.numIntersections = numIntersections;
        }
    }

    private DoubInt[] dijkstra(Pair[][] graphMatrix, int maxSize) {
        DoubInt[] dist = new DoubInt[graphMatrix.length];
        dist[0] = new DoubInt(0, 0);
        for (int i = 1; i < dist.length; i++) {
            dist[i] = new DoubInt(Double.MAX_VALUE, 0);
        }
        PriorityQueue<Pair> pq = new PriorityQueue<>(maxSize);
        pq.add(new Pair(0, 0));

        Set<Integer> settled = new HashSet<>();
        while (settled.size() != maxSize) {
            int u = pq.remove().node;
            settled.add(u);
            double edgeDistance;
            double newDistance;
            int populated;
            int newPopulated;
            for (int i = 0; i < graphMatrix[u].length; i++) {
                Pair v = graphMatrix[u][i];
                if (!settled.contains(v.node)) {
                    edgeDistance = v.distance;
                    populated = v.populatedIntersections;
                    newDistance = dist[u].distance + edgeDistance;
                    newPopulated = dist[u].numIntersections + populated;
                    if (newPopulated < dist[v.node].numIntersections || (newPopulated == dist[v.node].numIntersections && newDistance < dist[v.node].distance)) {
                        dist[v.node].distance = newDistance;
                        dist[v.node].numIntersections = newPopulated;
                    }
                    pq.add(new Pair(v.node, dist[v.node].distance, dist[v.node].numIntersections));
                }
            }
        }
        return dist;
    }

    private void updateDistance(Set<Integer> settled, Pair v, double[] dist, int u, PriorityQueue<Pair> pq) {
        if (!settled.contains(v.node)) {
            double edgeDistance = v.distance;
            double newDistance = dist[u] + edgeDistance;
            if (newDistance < dist[v.node])
                dist[v.node] = newDistance;
            pq.add(new Pair(v.node, dist[v.node]));
        }
    }

}
