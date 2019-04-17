package us.hiai.util;

/**
 * Wrapper class for doubly linked list of waypoints from .fms file
 */
public class WaypointNode {
    private float latitude;
    private float longitude;

    WaypointNode() {}
    public WaypointNode(double latitude, double longitude) {
        this.latitude = (float)latitude;
        this.longitude = (float)longitude;
    }

    public void setLatitude(float latitude) {
        this.latitude = latitude;
    }

    public void setLongitude(float longitude) {
        this.longitude = longitude;
    }

    @Override
    public String toString() {
        return latitude + " " + longitude;
    }

    public float getLatitude() {
        return latitude;
    }

    public float getLongitude() {
        return longitude;
    }
}
