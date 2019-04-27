package us.hiai.util.QuadtreeStructure;

import us.hiai.util.WaypointNode;

class QuadtreeNode {
    WaypointNode coord;
    QuadtreeNode upSquare;
    QuadtreeNode NE;
    QuadtreeNode NW;
    QuadtreeNode SE;
    QuadtreeNode SW;
    QuadtreeNode rightSquare;
    QuadtreeNode leftSquare;
    QuadtreeNode(WaypointNode coord) {
        this.coord = coord;
    }
}
