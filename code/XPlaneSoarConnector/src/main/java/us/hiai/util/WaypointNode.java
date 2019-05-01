package us.hiai.util;

/**
 * Created Spring 2019 by Daniel Griessler
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

    @Override
    public boolean equals(Object o) {
        if (o == this) {
            return true;
        }
        if (!(o instanceof WaypointNode)) {
            return false;
        }
        WaypointNode otherWaypointNode = (WaypointNode)o;
        return Math.abs(this.latitude - otherWaypointNode.latitude) < 0.01 && Math.abs(this.longitude - otherWaypointNode.longitude) < 0.01;
    }

    @Override
    public int hashCode() {
        final int h1 = Float.floatToIntBits(latitude);
        final int h2 = Float.floatToIntBits(longitude);
        return h1 ^ ((h2 >>> 16) | (h2 << 16));
    }
}
