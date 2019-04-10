package us.hiai.util;

import java.math.BigDecimal;
import java.util.HashSet;
import java.util.LinkedList;

/**
 * Created by Daniel Griessler Spring 2019
 * This contains static methods for calculating bearing, destination, distance etc.
 */
public class GeometryLogistics {
    private static final double convertToRadians = Math.PI / 180;
    private static final int EARTH_RADIUS = 6371000;
    public static final int NM_METERS = 1852;
    public static final double INCREMENT = 18.52;

    public static double calculateBearing(double planeLat, double planeLong, double otherLat, double otherLon, boolean circleCurrentWYPT, Double distance) {
        double lat1 = planeLat * convertToRadians;
        double lat2 = otherLat * convertToRadians;
        double longDif = (otherLon - planeLong) * convertToRadians;
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

    public static double calculateDistanceToWaypoint(double planeLat, double planeLong, double otherLat, double otherLon) {
        double lat1 = planeLat * convertToRadians;
        double lat2 = otherLat * convertToRadians;
        double latDif = ((planeLat - otherLat) * convertToRadians) / 2;
        double longDif = ((planeLong - otherLon) * convertToRadians) / 2;
        double a = Math.sin(latDif) * Math.sin(latDif) + Math.cos(lat1) * Math.cos(lat2) * Math.sin(longDif) * Math.sin(longDif);
        double c = 2 * Math.atan2(Math.sqrt(a), Math.sqrt(1-a));
        // earth's radius = 6371000 m
        return EARTH_RADIUS * c;
    }

    public static boolean checkLineIntersectsPolygon(double currentLat, double currentLong, double currentBearing, double maxDistance, GPS_Intersection gpsIntersect) {
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

    public static double[] countDistanceIntersectsPolygon(double currentLat, double currentLong, double currentBearing, double maxDistance, GPS_Intersection gpsIntersect) {
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

    static String checkLineIntersectsPopulated(double currentLat, double currentLong, double currentBearing, double maxDistance, GPS_Intersection gpsIntersect) {
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

    public static String willBeInPopulated (double currentLat, double currentLong, double currentBearing, double groundSpeed, GPS_Intersection gpsIntersect) {
        int time = 60;
        double maxDistance = calculateDistance(groundSpeed, time);

        return checkLineIntersectsPopulated(currentLat, currentLong, currentBearing, maxDistance, gpsIntersect);
    }

    public static double calculateDistance(double groundSpeed, double time) {
        // distance is calculated by speed / time which is returned in nautical miles.  To convert to m, then multiply by 1852
        return (groundSpeed / time) * 1852;
    }

    public static double[] calculateDestination (double currentLat, double currentLong, double currentBearing, double distance) {
        double radCurrentLat = currentLat * convertToRadians;
        double radCurrentBearing = currentBearing * convertToRadians;
        double radCurrentLong = currentLong * convertToRadians;
        double lat = Math.asin(Math.sin(radCurrentLat) * Math.cos(distance / EARTH_RADIUS) + Math.cos(radCurrentLat) * Math.sin(distance / EARTH_RADIUS) * Math.cos(radCurrentBearing));
        double lon = radCurrentLong + Math.atan2(Math.sin(radCurrentBearing) * Math.sin(distance / EARTH_RADIUS) * Math.cos(radCurrentLat), Math.cos(distance / EARTH_RADIUS) - Math.sin(radCurrentLat) * Math.sin(lat));
        return new double[]{lat / convertToRadians, (((lon / convertToRadians) + 540) % 360) - 180};
    }
}
