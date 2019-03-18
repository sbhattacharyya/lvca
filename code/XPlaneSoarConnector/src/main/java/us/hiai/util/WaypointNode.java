package us.hiai.util;

/**
 * Wrapper class for doubly linked list of waypoints from .fms file
 */
public class WaypointNode {
    private Integer type;
    private String destination;
    private float altitude;
    private float latitude;
    private float longitude;

    WaypointNode(String destination) {
        this.destination = destination;
    }

    public void setType(Integer type) {
        this.type = type;
    }

    public void setDestination(String destination) {
        this.destination = destination;
    }

    public void setAltitude(float altitude) {
        this.altitude = altitude;
    }

    public void setLatitude(float latitude) {
        this.latitude = latitude;
    }

    public void setLongitude(float longitude) {
        this.longitude = longitude;
    }

    @Override
    public String toString() {
        return type + " " + destination + " " + altitude + " " + latitude + " " + longitude;
    }

    public Integer getType() {
        return type;
    }

    public String getDestination() {
        return destination;
    }

    public float getAltitude() {
        return altitude;
    }

    public float getLatitude() {
        return latitude;
    }

    public float getLongitude() {
        return longitude;
    }
}
