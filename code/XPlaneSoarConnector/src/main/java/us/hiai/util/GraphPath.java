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
                if (j != i && elements[j].getPolygonIndex() != elements[i].getPolygonIndex() && graph.get(i).get(j).node == -1) {
                    addEdge(i, j, graph);
                }
            }
        }

        double[] distances = dijkstra(graph, 0, size);

        System.out.println("The shorted path from node :");
        for (int i = 0; i < distances.length; i++)
            System.out.println(0 + " to " + i + " is "
                    + distances[i]);
    }

    private void addEdge(int indexNode1, int indexNode2, LinkedList<LinkedList<Pair>> graph) {
        double distanceToNode = GeometryLogistics.calculateDistanceToWaypoint(elements[indexNode1].getLat(), elements[indexNode1].getLon(), elements[indexNode2].getLat(), elements[indexNode2].getLon());
        double currentBearing = GeometryLogistics.calculateBearing(elements[indexNode1].getLat(), elements[indexNode1].getLon(), elements[indexNode2].getLat(), elements[indexNode2].getLon(), false, null);
        if (!GeometryLogistics.checkLineIntersectsPolygon(elements[indexNode1].getLat(), elements[indexNode1].getLon(), currentBearing, distanceToNode, gpsIntersect)) {
            graph.get(indexNode1).add(new Pair(indexNode2, distanceToNode));
            graph.get(indexNode2).add(new Pair(indexNode1, distanceToNode));
        }
    }

    static class Pair implements Comparable<Pair> {
        int node;
        double distance;
        Pair(int node, double distance) {
            this.node = node;
            this.distance = distance;
        }

        @Override
        public int compareTo(@NotNull Pair otherPair) {
            return Double.compare(this.distance, otherPair.distance);
        }
    }

    private double[] dijkstra(LinkedList<LinkedList<Pair>> graph, int src, int maxSize) {
        double[] dist = new double[graph.size()];
        dist[0] = 0;
        for (int i = 1; i < dist.length; i++) {
            dist[i] = Double.MAX_VALUE;
        }
        PriorityQueue<Pair> pq = new PriorityQueue<>(maxSize);
        pq.add(new Pair(src, 0));

        Set<Integer> settled = new HashSet<>();
        while (settled.size() != maxSize) {
            int u = pq.remove().node;
            settled.add(u);
            double edgeDistance = -1;
            double newDistance = -1;
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

}
