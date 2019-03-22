package us.hiai.util;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.PriorityQueue;

public class GraphPath {
//    static class Edge {
//        double weight;
//        int destination;
//        public Edge(double weight, int destination) {
//            this.weight = weight;
//            this.destination = destination;
//        }
//        public int getDestination() { return destination; }
//    }
//
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
//
//        public boolean containsEdge(int indexOfNode) {
//            boolean contains = false;
//            for(Edge nextEdge : edges) {
//                if (nextEdge.getDestination() == indexOfNode) {
//                    contains = true;
//                    break;
//                }
//            }
//            return contains;
//        }
//
//        public Edge addEdge(double distanceToNode, int indexOfNode) {
//           Edge newEdge = new Edge(distanceToNode, indexOfNode);
//           edges.add(newEdge);
//           return newEdge;
//        }
    }

    Node[] elements;
    int[] polygonEnd;
    GPS_Intersection gpsIntersect;

    public GraphPath(double[] plane, double[] destination, LinkedList<ArrayList<Double>> latPolygons, LinkedList<ArrayList<Double>> lonPolygons, GPS_Intersection gpsIntersect) {
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

        double graph[][] = new double[size][size];
        for (int i = 0; i < graph.length; i++) {
            for (int j = 0; j < graph.length; j++) {
                graph[i][j] = -1;
            }
        }
        for(int i = 0; i < elements.length; i++) {
            for (int j = 0; j < elements.length; j++) {
                if (j != i && elements[j].getPolygonIndex() != elements[i].getPolygonIndex() && graph[i][j] == -1) {
                    addEdge(i, j, graph);
                }
            }
        }


    }

    private void addEdge(int indexNode1, int indexNode2, double graph[][]) {
        double distanceToNode = GeometryLogistics.calculateDistanceToWaypoint(elements[indexNode1].getLat(), elements[indexNode1].getLon(), elements[indexNode2].getLat(), elements[indexNode2].getLon());
        double currentBearing = GeometryLogistics.calculateBearing(elements[indexNode1].getLat(), elements[indexNode1].getLon(), elements[indexNode2].getLat(), elements[indexNode2].getLon(), false, null);
        if (!GeometryLogistics.checkLineIntersectsPolygon(elements[indexNode1].getLat(), elements[indexNode1].getLon(), currentBearing, distanceToNode, gpsIntersect)) {
//            elements[indexNode1].addEdge(distanceToNode, indexNode2);
//            elements[indexNode2].addEdge(distanceToNode, indexNode1);
            graph[indexNode1][indexNode2] = distanceToNode;
            graph[indexNode2][indexNode1] = distanceToNode;
        }
    }

    static class Pair {
        int node;
        double distance;
        Pair(int node, double distance)
    }

    private void dijkstra(double graph[][], int src) {
        double dist[] = new double[graph.length];
        dist[0] = 0;
        for (int i = 1; i < dist.length; i++) {
            dist[i] = Double.MAX_VALUE;
        }
        PriorityQueue<Node>
    }

}
