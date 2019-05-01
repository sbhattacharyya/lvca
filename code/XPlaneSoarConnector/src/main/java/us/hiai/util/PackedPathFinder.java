package us.hiai.util;

/**
 * Packed arguments for the path finder
 */
class PackedPathFinder {
    double planeLat;
    double planeLon;
    GraphPath gp;
    int node;
    PackedPathFinder(double planeLat, double planeLon, GraphPath gp, int node) {
        this.planeLat = planeLat;
        this.planeLon = planeLon;
        this.gp = gp;
        this.node = node;
    }
}
