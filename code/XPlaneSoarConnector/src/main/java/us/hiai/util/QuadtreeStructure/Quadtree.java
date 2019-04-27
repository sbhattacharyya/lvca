package us.hiai.util.QuadtreeStructure;

import us.hiai.util.WaypointNode;

import java.util.Random;

/**
 * Created by Daniel Griessler Spring 2019
 * Implementing a skip list quad tree will speed up storing and retrieving local decision points
 * Currently, previous decisions are stored in a HashSet which takes O(n) search time
 * A fully implemented skip list quad tree will have O(log(n)) insertion, deletion, and searching (see paper)
 * However, it is built on a condensed quad tree that needs to implemented
 * From there, the skip list part also needs to be implemented
 * Use these sources:
 * https://people.inf.elte.hu/fekete/algoritmusok_msc/terinfo_geom/konyvek/Computational%20Geometry%20-%20Algorithms%20and%20Applications,%203rd%20Ed.pdf
 * use quad trees to find closest point to use their decision
 * skip list quad tree
 * https://www.ics.uci.edu/~goodrich/pubs/skip-journal.pdf
 */
public class Quadtree {
    private static Random rand = new Random();
    QuadtreeNode root;
    Quadtree() {
        root = new QuadtreeNode(null);
    }

    QuadtreeNode addPoint(WaypointNode newPoint) {
        // to insert a new point into a skip quadtree

        // assign a level to the point
        int level = -1;
        double randProbability;
        double stopProbability = 1;
        do {
            randProbability = rand.nextDouble();
            level++;
            stopProbability /= 2;
        } while(randProbability < stopProbability);

        //locate the point (finds smallest interesting square containing it in all levels)


        // Perform O(1) local changes in each modified level
        return null;
    }

    void deletePoint(WaypointNode deletePoint) {

        // locate the point (finds smallest interesting square containing it in all levels)

        // Perform O(1) local changes in each modified level

    }
}
