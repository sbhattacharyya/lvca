package us.hiai.util;

import java.math.BigDecimal;
import java.util.HashSet;
import java.util.LinkedList;

/**
 * Created by Daniel Griessler Spring 2019
 * This contains static methods for calculating bearing, destination, distance etc.
 * Source of several calculations: https://www.movable-type.co.uk/scripts/latlong.html
 */
public class GeometryLogistics {
    private static final double convertToRadians = Math.PI / 180;
    private static final int EARTH_RADIUS = 6371000;
    public static final int NM_METERS = 1852;
    public static final double INCREMENT = 18.52;

    /**
     * Calculate the bearing that should be flown the first gps coordinate to get to the second gps coordinate
     * If circling the current waypoint and the plane is on the imaginary circle surrounding the waypoint, then modify the bearing so that the plane flies tangent to the circle
     * @param firstLat latitude of the starting gps coordinate
     * @param firstLon longitude of the starting gps coordinate
     * @param secondLat latitude of the target gps coordinate
     * @param secondLon longitude of the target gps coordinate
     * @param circleCurrentWYPT set to true if the plane should circle the provided point
     * @param distance calculated distance between the two provided gps coordinates
     * @return the bearing to fly in range 0 to 360 where 360 will loop back to 0
     */
    public static double calculateBearing(double firstLat, double firstLon, double secondLat, double secondLon, boolean circleCurrentWYPT, Double distance) {
        double lat1 = firstLat * convertToRadians;
        double lat2 = secondLat * convertToRadians;
        double longDif = (secondLon - firstLon) * convertToRadians;
        double y = Math.sin(longDif) * Math.cos(lat2);
        double x = Math.cos(lat1)*Math.sin(lat2) - Math.sin(lat1)*Math.cos(lat2)*Math.cos(longDif);
        // convert radian returned by atan2 to degrees
        double bearing = (Math.atan2(y, x) / convertToRadians) + 360;
        if (circleCurrentWYPT)
            if (distance > NM_METERS)
                bearing += Math.asin(1852 / (2 * distance));
            else
                bearing += 90;
        return bearing % 360;
    }

    /**
     * Calculates the distance between the two provided gps coordinates.
     * @param firstLat latitude of the starting gps coordinate
     * @param firstLon longitude of the starting gps coordinate
     * @param secondLat latitude of the target gps coordinate
     * @param secondLon longitude of the target gps coordinate
     * @return distance in meters between the two gps coordinates
     */
    public static double calculateDistanceToWaypoint(double firstLat, double firstLon, double secondLat, double secondLon) {
        double lat1 = firstLat * convertToRadians;
        double lat2 = secondLat * convertToRadians;
        double latDif = ((firstLat - secondLat) * convertToRadians) / 2;
        double longDif = ((firstLon - secondLon) * convertToRadians) / 2;
        double a = Math.sin(latDif) * Math.sin(latDif) + Math.cos(lat1) * Math.cos(lat2) * Math.sin(longDif) * Math.sin(longDif);
        double c = 2 * Math.atan2(Math.sqrt(a), Math.sqrt(1-a));
        // earth's radius = 6371000 m
        return EARTH_RADIUS * c;
    }

    /**
     * Checks if there is a point starting from the current gps coordinate to the provided maximum distance in front of it that will be in a populated area
     * Note: this requires sampling of points. The sampling rate is set by INCREMENT. Increasing that will make the calculation more accurate but take longer. Decreasing that will make the calculation faster but less accurate
     * @param currentLat the current latitude
     * @param currentLong the current longitude
     * @param currentBearing the current bearing of the aircraft
     * @param maxDistance the farthest point to sample starting from the current point
     * @param gpsIntersect reference to a GPS_Intersection which includes information about what areas are populated
     * @return if the plane is projected to be in a populated area starting from where it is to the max distance provided
     */
    static boolean checkLineIntersectsPolygon(double currentLat, double currentLong, double currentBearing, double maxDistance, GPS_Intersection gpsIntersect) {
        double currentDistance = maxDistance;
        double[] destination;
        while (currentDistance > 0) {
            destination = calculateDestination(currentLat, currentLong, currentBearing, currentDistance);
            if(gpsIntersect.coordIsContained(destination[0], destination[1])) {
                return true;
            }
            currentDistance -= INCREMENT;
        }
        if (currentDistance < 0) {
            return gpsIntersect.coordIsContained(currentLat, currentLong);
        }
        return false;
    }

    /**
     * Returns a distance that the plane would fly through each type of polygon (lightly populated and fully populated) starting at the given point to the max distance provided
     * @param currentLat the current latitude
     * @param currentLong the current longitude
     * @param currentBearing the current bearing of the aircraft
     * @param maxDistance the farthest point to sample starting from the current point
     * @param gpsIntersect reference to a GPS_Intersection which includes information about what areas are populated
     * @return array with the distance that the plane will intersect fully populated and lightly populated areas
     */
    static double[] countDistanceIntersectsPolygon(double currentLat, double currentLong, double currentBearing, double maxDistance, GPS_Intersection gpsIntersect) {
        double currentDistance = maxDistance;
        double[] destination;
        double[] distanceIntersected = new double[2];
        int[] runningIntersections = new int[2];
        while (currentDistance > 0) {
            destination = calculateDestination(currentLat, currentLong, currentBearing, currentDistance);
            int[] intersectIndex = gpsIntersect.indexOfContainedCoord(destination[0], destination[1]);
            if (intersectIndex[0] != -1) {
                runningIntersections[intersectIndex[1]]++;
            } else  {
                runningIntersections[1] += runningIntersections[0];
                for (int i = 0; i < runningIntersections.length; i++) {
                    if (runningIntersections[i] != 0) {
                        distanceIntersected[i] += INCREMENT * runningIntersections[i];
                        runningIntersections[i] = 0;
                    }
                }
            }
            currentDistance -= INCREMENT;
        }
        int[] intersectIndex = gpsIntersect.indexOfContainedCoord(currentLat, currentLong);
        if (intersectIndex[0] != -1) {
            runningIntersections[intersectIndex[1]]++;
        }
        runningIntersections[1] += runningIntersections[0];
        for (int i = 0; i < runningIntersections.length; i++) {
            if (runningIntersections[i] != 0)
                distanceIntersected[i] += INCREMENT * runningIntersections[i];
        }
        return distanceIntersected;
    }

    /**
     * Checks if there is a point starting from the current gps coordinate to the provided maximum distance in front of it that will be in a populated area
     * Note: this requires sampling of points. The sampling rate is set by INCREMENT. Increasing that will make the calculation more accurate but take longer. Decreasing that will make the calculation faster but less accurate
     * @param currentLat the current latitude
     * @param currentLong the current longitude
     * @param currentBearing the current bearing of the aircraft
     * @param maxDistance the farthest point to sample starting from the current point
     * @param gpsIntersect reference to a GPS_Intersection which includes information about what areas are populated
     * @return the worst kind of area that was intersected (if fully is encountered, it immediately returns. if lightly is encountered, it will continue to sample) or null if no area was intersected
     */
    private static String checkLineIntersectsPopulated(double currentLat, double currentLong, double currentBearing, double maxDistance, GPS_Intersection gpsIntersect) {
        double currentDistance = maxDistance;
        double[] destination;
        String result = "null";
        while (currentDistance > 0) {
            destination = calculateDestination(currentLat, currentLong, currentBearing, currentDistance);
            int isContained = gpsIntersect.indexOfContainedCoord(destination[0], destination[1])[1];
            switch (isContained) {
                case 0:
                    return "fully";
                case 1:
                    result = "lightly";
                    break;
            }
            currentDistance -= INCREMENT;
        }
        return result;
    }

    /**
     * Projects ahead of the provided gps coordinate along the provided bearing for one minute and reports the highest level of populated intersection found
     * @param currentLat the current latitude
     * @param currentLong the current longitude
     * @param currentBearing the current bearing of the aircraft
     * @param groundSpeed current speed of the aircraft
     * @param gpsIntersect reference to a GPS_Intersection which includes information about what areas are populated
     * @return
     */
    public static String willBeInPopulated (double currentLat, double currentLong, double currentBearing, double groundSpeed, GPS_Intersection gpsIntersect) {
        int time = 60;
        double maxDistance = calculateDistance(groundSpeed, time);

        return checkLineIntersectsPopulated(currentLat, currentLong, currentBearing, maxDistance, gpsIntersect);
    }

    /**
     * Simple calculation of total distance = spped / time.
     * @param groundSpeed current speed
     * @param time total time
     * @return total distance in meters
     */
    public static double calculateDistance(double groundSpeed, double time) {
        // distance is calculated by speed / time which is returned in nautical miles.  To convert to m, then multiply by 1852
        return (groundSpeed / time) * 1852;
    }

    /**
     * Calculates the new gps coordinate given the starting gps coordinate, bearing, and distance
     * @param currentLat the current latitude
     * @param currentLong the current longitude
     * @param currentBearing the current bearing of the aircraft
     * @param distance distance in meters that the plane will cover
     * @return the point that the aircraft will be at by flying the provided bearing for the provided distance
     */
    private static double[] calculateDestination(double currentLat, double currentLong, double currentBearing, double distance) {
        double radCurrentLat = currentLat * convertToRadians;
        double radCurrentBearing = currentBearing * convertToRadians;
        double radCurrentLong = currentLong * convertToRadians;
        double lat = Math.asin(Math.sin(radCurrentLat) * Math.cos(distance / EARTH_RADIUS) + Math.cos(radCurrentLat) * Math.sin(distance / EARTH_RADIUS) * Math.cos(radCurrentBearing));
        double lon = radCurrentLong + Math.atan2(Math.sin(radCurrentBearing) * Math.sin(distance / EARTH_RADIUS) * Math.cos(radCurrentLat), Math.cos(distance / EARTH_RADIUS) - Math.sin(radCurrentLat) * Math.sin(lat));
        return new double[]{lat / convertToRadians, (((lon / convertToRadians) + 540) % 360) - 180};
    }
}
