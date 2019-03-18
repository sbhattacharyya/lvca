package us.hiai.util;
import java.util.ArrayList;
/**
 * Creates polygons on map needed for GPS testing whether in populated area or not
 * To modify: create polygons using GPS coordinates.  I used SkyVector to place GPS points on map.  Then I opened
 * the generated navlog and copied in HTML into a test file.  There is one line in the html that includes the text with
 * all of the coordinates.  Use parse to separate and print all of the instructions.  They can be easily copy pasted into here.
 *
 * The calculation itself is courtesy of Eric Leschinski who answered a question on stack overflow found at: https://stackoverflow.com/questions/4287780/detecting-whether-a-gps-coordinate-falls-within-a-polygon-on-a-map
 * Other modifications: Daniel Griessler Spring 2019
 */
public class GPS_Intersection
{
    public static double PI = 3.14159265;
    public static double TWOPI = 2*PI;
    ArrayList<ArrayList<String>> polygons;
    ArrayList<ArrayList<Double>> lat_array;
    ArrayList<ArrayList<Double>> long_array;

    public GPS_Intersection() {
        polygons = new ArrayList<>();

        ArrayList<String> polygon_1_lat_long_pairs = new ArrayList<>();

        // around Lancaster
        polygon_1_lat_long_pairs.add("32.51317, -96.8315");
        polygon_1_lat_long_pairs.add("32.44384, -96.87");
        polygon_1_lat_long_pairs.add("32.4365, -96.908");
        polygon_1_lat_long_pairs.add("32.41084, -96.8815");
        polygon_1_lat_long_pairs.add("32.36734, -96.88233");
        polygon_1_lat_long_pairs.add("32.36584, -96.81233");
        polygon_1_lat_long_pairs.add("32.51184, -96.741");
        polygon_1_lat_long_pairs.add("32.52917, -96.71366");
        polygon_1_lat_long_pairs.add("32.56517, -96.75416");
        polygon_1_lat_long_pairs.add("32.66284, -96.7365");
        polygon_1_lat_long_pairs.add("32.73717, -96.7715");
        polygon_1_lat_long_pairs.add("32.7995, -96.83866");
        polygon_1_lat_long_pairs.add("32.80217, -96.907");
        polygon_1_lat_long_pairs.add("32.75034, -96.93233");
        polygon_1_lat_long_pairs.add("32.593, -96.97666");
        polygon_1_lat_long_pairs.add("32.4695, -97.03016");
        polygon_1_lat_long_pairs.add("32.474, -96.9735");
        polygon_1_lat_long_pairs.add("32.54867, -96.95783");
        polygon_1_lat_long_pairs.add("32.57217, -96.9155");
        polygon_1_lat_long_pairs.add("32.57167, -96.88166");
        polygon_1_lat_long_pairs.add("32.55284, -96.88");
        polygon_1_lat_long_pairs.add("32.54734, -96.90116");
        polygon_1_lat_long_pairs.add("32.50367, -96.8905");

        polygons.add(polygon_1_lat_long_pairs);

        ArrayList<String> polygon_2_lat_long_pairs = new ArrayList<>();

        // surrounding Dallas
        polygon_2_lat_long_pairs.add("32.80917, -96.90633");
        polygon_2_lat_long_pairs.add("32.792, -96.9275");
        polygon_2_lat_long_pairs.add("32.78484, -96.96916");
        polygon_2_lat_long_pairs.add("32.79984, -97.00233");
        polygon_2_lat_long_pairs.add("32.79167, -97.01416");
        polygon_2_lat_long_pairs.add("32.77317, -97.0065");
        polygon_2_lat_long_pairs.add("32.76634, -96.946");
        polygon_2_lat_long_pairs.add("32.73734, -96.94566");
        polygon_2_lat_long_pairs.add("32.7345, -96.9675");
        polygon_2_lat_long_pairs.add("32.7125, -96.97866");
        polygon_2_lat_long_pairs.add("32.68134, -96.981");
        polygon_2_lat_long_pairs.add("32.67184, -96.965");
        polygon_2_lat_long_pairs.add("32.63684, -97.02516");
        polygon_2_lat_long_pairs.add("32.629, -97.064");
        polygon_2_lat_long_pairs.add("32.5955, -97.07816");
        polygon_2_lat_long_pairs.add("32.56134, -97.09316");
        polygon_2_lat_long_pairs.add("32.55934, -97.10766");
        polygon_2_lat_long_pairs.add("32.54617, -97.1025");
        polygon_2_lat_long_pairs.add("32.53734, -97.12233");
        polygon_2_lat_long_pairs.add("32.54967, -97.13483");
        polygon_2_lat_long_pairs.add("32.5445, -97.15116");
        polygon_2_lat_long_pairs.add("32.54584, -97.19433");
        polygon_2_lat_long_pairs.add("32.54217, -97.20966");
        polygon_2_lat_long_pairs.add("32.533, -97.20716");
        polygon_2_lat_long_pairs.add("32.51367, -97.2525");
        polygon_2_lat_long_pairs.add("32.4915, -97.24916");
        polygon_2_lat_long_pairs.add("32.4845, -97.3195");
        polygon_2_lat_long_pairs.add("32.50367, -97.3255");
        polygon_2_lat_long_pairs.add("32.50567, -97.29133");
        polygon_2_lat_long_pairs.add("32.52567, -97.30266");
        polygon_2_lat_long_pairs.add("32.52134, -97.33966");
        polygon_2_lat_long_pairs.add("32.54, -97.36916");
        polygon_2_lat_long_pairs.add("32.559, -97.36983");
        polygon_2_lat_long_pairs.add("32.55084, -97.38883");
        polygon_2_lat_long_pairs.add("32.53484, -97.39266");
        polygon_2_lat_long_pairs.add("32.5275, -97.418");
        polygon_2_lat_long_pairs.add("32.55067, -97.44283");
        polygon_2_lat_long_pairs.add("32.5725, -97.42366");
        polygon_2_lat_long_pairs.add("32.58884, -97.37216");
        polygon_2_lat_long_pairs.add("32.61984, -97.414");
        polygon_2_lat_long_pairs.add("32.6435, -97.421");
        polygon_2_lat_long_pairs.add("32.65867, -97.48483");
        polygon_2_lat_long_pairs.add("32.68967, -97.46366");
        polygon_2_lat_long_pairs.add("32.7135, -97.47516");
        polygon_2_lat_long_pairs.add("32.71467, -97.53833");
        polygon_2_lat_long_pairs.add("32.7285, -97.54");
        polygon_2_lat_long_pairs.add("32.74567, -97.48733");
        polygon_2_lat_long_pairs.add("32.7965, -97.46683");
        polygon_2_lat_long_pairs.add("32.82017, -97.5425");
        polygon_2_lat_long_pairs.add("32.86917, -97.569");
        polygon_2_lat_long_pairs.add("32.89034, -97.55066");
        polygon_2_lat_long_pairs.add("32.9405, -97.6235");
        polygon_2_lat_long_pairs.add("32.99617, -97.61916");
        polygon_2_lat_long_pairs.add("33.00284, -97.49966");
        polygon_2_lat_long_pairs.add("32.9135, -97.48983");
        polygon_2_lat_long_pairs.add("32.91534, -97.43");
        polygon_2_lat_long_pairs.add("32.921, -97.39283");
        polygon_2_lat_long_pairs.add("32.9635, -97.3625");
        polygon_2_lat_long_pairs.add("32.95384, -97.30833");
        polygon_2_lat_long_pairs.add("33.00984, -97.27116");
        polygon_2_lat_long_pairs.add("33.0245, -97.21933");
        polygon_2_lat_long_pairs.add("33.05634, -97.188");
        polygon_2_lat_long_pairs.add("33.12767, -97.22233");
        polygon_2_lat_long_pairs.add("33.1535, -97.14833");
        polygon_2_lat_long_pairs.add("33.22734, -97.18716");
        polygon_2_lat_long_pairs.add("33.23167, -97.23883");
        polygon_2_lat_long_pairs.add("33.277, -97.26633");
        polygon_2_lat_long_pairs.add("33.294, -97.21233");
        polygon_2_lat_long_pairs.add("33.26384, -97.1775");
        polygon_2_lat_long_pairs.add("33.271, -97.08366");
        polygon_2_lat_long_pairs.add("33.31634, -96.98466");
        polygon_2_lat_long_pairs.add("33.29167, -96.96433");
        polygon_2_lat_long_pairs.add("33.25184, -96.9495");
        polygon_2_lat_long_pairs.add("33.23417, -96.89083");
        polygon_2_lat_long_pairs.add("33.182, -96.821");
        polygon_2_lat_long_pairs.add("33.22834, -96.751");
        polygon_2_lat_long_pairs.add("33.2305, -96.6875");
        polygon_2_lat_long_pairs.add("33.28067, -96.68");
        polygon_2_lat_long_pairs.add("33.27917, -96.63");
        polygon_2_lat_long_pairs.add("33.21267, -96.58333");
        polygon_2_lat_long_pairs.add("33.1935, -96.5275");
        polygon_2_lat_long_pairs.add("33.14834, -96.52683");
        polygon_2_lat_long_pairs.add("33.12834, -96.55533");
        polygon_2_lat_long_pairs.add("33.03934, -96.53033");
        polygon_2_lat_long_pairs.add("33.03467, -96.47783");
        polygon_2_lat_long_pairs.add("33.01467, -96.47383");
        polygon_2_lat_long_pairs.add("32.94667, -96.51266");
        polygon_2_lat_long_pairs.add("32.91884, -96.49516");
        polygon_2_lat_long_pairs.add("32.87717, -96.5125");
        polygon_2_lat_long_pairs.add("32.83717, -96.536");
        polygon_2_lat_long_pairs.add("32.8055, -96.51416");
        polygon_2_lat_long_pairs.add("32.74434, -96.51566");
        polygon_2_lat_long_pairs.add("32.73267, -96.54583");
        polygon_2_lat_long_pairs.add("32.75284, -96.566");
        polygon_2_lat_long_pairs.add("32.7325, -96.58016");
        polygon_2_lat_long_pairs.add("32.70067, -96.5475");
        polygon_2_lat_long_pairs.add("32.639, -96.51016");
        polygon_2_lat_long_pairs.add("32.6305, -96.54633");
        polygon_2_lat_long_pairs.add("32.67534, -96.632");
        polygon_2_lat_long_pairs.add("32.67067, -96.66633");
        polygon_2_lat_long_pairs.add("32.731, -96.7255");
        polygon_2_lat_long_pairs.add("32.73017, -96.7635");
        polygon_2_lat_long_pairs.add("32.77967, -96.81383");
        polygon_2_lat_long_pairs.add("32.80567, -96.86766");


        polygons.add(polygon_2_lat_long_pairs);


        ArrayList<String> polygon_3_lat_long_pairs = new ArrayList<>();

        // small building next to "Italy" text on map
        polygon_3_lat_long_pairs.add("32.20967, -96.87383");
        polygon_3_lat_long_pairs.add("32.17517, -96.85833");
        polygon_3_lat_long_pairs.add("32.15934, -96.8775");
        polygon_3_lat_long_pairs.add("32.18967, -96.9105");

        polygons.add(polygon_3_lat_long_pairs);

        ArrayList<String> polygon_4_lat_long_pairs = new ArrayList<>();

        // small building next to "Blooming Grove" text on map
        polygon_4_lat_long_pairs.add("32.1055, -96.72266");
        polygon_4_lat_long_pairs.add("32.09317, -96.73366");
        polygon_4_lat_long_pairs.add("32.078, -96.71783");
        polygon_4_lat_long_pairs.add("32.09084, -96.69816");

        polygons.add(polygon_4_lat_long_pairs);

        lat_array = new ArrayList<>(polygons.size());
        long_array = new ArrayList<>(polygons.size());

        for (int i = 0; i < polygons.size(); i++) {
            ArrayList<Double> nextLat = new ArrayList<>();
            ArrayList<Double> nextLong = new ArrayList<>();
            for (String s : polygons.get(i)) {
                nextLat.add(Double.parseDouble(s.split(",")[0]));
                nextLong.add(Double.parseDouble(s.split(",")[1]));
            }
            lat_array.add(nextLat);
            long_array.add(nextLong);
        }

    }


    public void printIfIsContained(double testLat, double testLong) {
        boolean isContained = coordIsContained(testLat, testLong);
        System.out.println(isContained);
    }

    public boolean coordIsContained(double testLat, double testLong) {
        boolean isContained = false;
        for (int i = 0; i < polygons.size(); i++) {
            if (coordinate_is_inside_polygon(testLat, testLong, lat_array.get(i), long_array.get(i))) {
                isContained = true;
                break;
            }
        }
        return isContained;
    }

    // uncomment for testing

    /*
    public static void main(String[] args) {
        GPS_Intersection gi = new GPS_Intersection();
        gi.printIfIsContained(32 + 40.19/60, -1*(97 + 02.98/60));

    }
    */

    public static boolean coordinate_is_inside_polygon(
            double latitude, double longitude,
            ArrayList<Double> lat_array, ArrayList<Double> long_array)
    {
        int i;
        double angle=0;
        double point1_lat;
        double point1_long;
        double point2_lat;
        double point2_long;
        int n = lat_array.size();

        for (i=0;i<n;i++) {
            point1_lat = lat_array.get(i) - latitude;
            point1_long = long_array.get(i) - longitude;
            point2_lat = lat_array.get((i+1)%n) - latitude;
            //you should have paid more attention in high school geometry.
            point2_long = long_array.get((i+1)%n) - longitude;
            angle += Angle2D(point1_lat,point1_long,point2_lat,point2_long);
        }

        if (Math.abs(angle) < PI)
            return false;
        else
            return true;
    }

    public static double Angle2D(double y1, double x1, double y2, double x2)
    {
        double dtheta,theta1,theta2;

        theta1 = Math.atan2(y1,x1);
        theta2 = Math.atan2(y2,x2);
        dtheta = theta2 - theta1;
        while (dtheta > PI)
            dtheta -= TWOPI;
        while (dtheta < -PI)
            dtheta += TWOPI;

        return(dtheta);
    }

}