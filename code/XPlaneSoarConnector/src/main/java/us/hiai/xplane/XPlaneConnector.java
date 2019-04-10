package us.hiai.xplane;

import gov.nasa.xpc.WaypointOp;
import gov.nasa.xpc.XPlaneConnect;
import us.hiai.data.FlightData;
import us.hiai.util.GPS_Intersection;

import java.io.IOException;
import java.net.SocketException;
import java.net.UnknownHostException;
import java.util.Arrays;

public class XPlaneConnector
{
    private static XPlaneConnect xpc = getConnection();

    private enum ControlSurface
    {
        LAT_STICK(0, "Latitudinal Stick (Roll)"),
        LONG_STICK(1, "Longitudinal Stick (Pitch)"),
        RUDDER(2, "Rudder Pedals (Yaw)"),
        THROTTLE(3, "Throttle"),
        GEAR(4, "Landing Gear"),
        FLAPS(5, "Flaps");

        final int index;
        final String description;

        ControlSurface(int i, String desc)
        {
            this.index = i;
            this.description = desc;
        }
    }

    public static XPlaneConnect getConnection()
    {
        if (xpc == null)
        {
            try
            {
                xpc = new XPlaneConnect();
            }
            catch (SocketException e)
            {
                e.printStackTrace();
                System.exit(1);
            }
        }
        return xpc;
    }

    private static XPlaneConnect refresh()
    {
        try
        {
            xpc = new XPlaneConnect();
        }
        catch (SocketException e)
        {
            e.printStackTrace();
        }
        return xpc;
    }

    // ------------------ GET INFO ------------------------

    public float currentAirspeed()
    {
        return getValueFromSim("sim/flightmodel/position/indicated_airspeed2");
    }

    public float currentAltitude()
    {
        return getValueFromSim("sim/cockpit2/gauges/indicators/altitude_ft_pilot");
    }

    public float currentHeading()
    {
        return getValueFromSim("sim/flightmodel/position/true_psi");
    }

    public float currentRollAngle()
    {
        return getValueFromSim("sim/flightmodel/position/true_phi");
    }

    public float currentPitch()
    {
        return getValueFromSim("sim/flightmodel/position/true_theta");
    }

    // ------------------ CONTROL AIRPLANE -------------------

    private static void changeControlSurfacePositions(ControlSurface controlSurface, float value)
    {
        try
        {
            float[] positions = xpc.getCTRL(0);
            positions[controlSurface.index] = value;
            xpc.sendCTRL(positions);
        }
        catch (IOException e)
        {
            failConcisely(e, controlSurface.description);
        }
    }

    public void setWheelBrake(boolean isBraking)
    {
        setValueOnSim("sim/flightmodel/controls/parkbrake", isBraking ? 1 : 0);
    }

    public void setRoll(float ratio)
    {
        changeControlSurfacePositions(ControlSurface.LONG_STICK, ratio);
    }

    public void setPitch(float ratio)
    {
        changeControlSurfacePositions(ControlSurface.LAT_STICK, ratio);
    }

    public void setThrottle(float positiveRatio)
    {
        changeControlSurfacePositions(ControlSurface.THROTTLE, positiveRatio);
    }

    public void setGear(boolean deployed)
    {
        changeControlSurfacePositions(ControlSurface.GEAR, deployed ? 1 : 0);
    }

    public void setYaw(float ratio)
    {
        changeControlSurfacePositions(ControlSurface.RUDDER, ratio);
    }

    public void setFlaps(float positiveRatio)
    {
        changeControlSurfacePositions(ControlSurface.FLAPS, positiveRatio);
    }

    public static void setAutopilotHeading(float heading) {
        setValueOnSim("sim/cockpit/autopilot/heading", heading);
    }



    // ------------------------------------------------------------

    private float[][] getValuesFromSim(String[] strs)
    {
        try
        {
            return xpc.getDREFs(strs);
        }
        catch (IOException e)
        {
            e.printStackTrace();
        }
        return new float[1][1];
    }

    private float getValueFromSim(String str)
    {
        try
        {
            return xpc.getDREF(str)[0];
        }
        catch (IOException | IndexOutOfBoundsException | NegativeArraySizeException e)
        {
            failConcisely(e, "DREF: "+str);
        }
        return 0.0f;
    }

    private static void failConcisely(Exception e, String extra)
    {
        System.err.println(e.toString() + " " + extra);
    }

    public static void setValueOnSim(String s, float val)
    {
        try
        {
            xpc.sendDREF(s, val);
        }
        catch (IOException e)
        {
            e.printStackTrace();
        }
    }

    private void setValueOnSim(String s, float[] val)
    {
        try
        {
            xpc.sendDREF(s, val);
        }
        catch (IOException e)
        {
            e.printStackTrace();
        }
    }

    private void setValuesOnSim(String[] strings, float[][] vals)
    {
        try
        {
            xpc.sendDREFs(strings, vals);
        }
        catch (IOException e)
        {
            e.printStackTrace();
        }
    }

    private static boolean enginesOK = true;
    private static boolean airBrakesON = false;
    private static boolean wheelBrakesON = false;
    private static boolean reverseON = false;
    private static int isPopulated = 0;

    public static synchronized FlightData getFlightData(GPS_Intersection gpsIntersect)
    {
        float[][] values;
        float[] oilPressurePerEngine;
        float oilPressureGreenLo;
        float currentTime;
        float autopilotHeading;
        float expectedGPSCourse;
        float groundSpeed;
        try {
            values = xpc.getDREFs(new String[]{
                    "sim/flightmodel/position/indicated_airspeed",          // 0
                    "sim/cockpit2/gauges/indicators/altitude_ft_pilot",     // 1
                    "sim/flightmodel/position/latitude",                    // 2
                    "sim/flightmodel/position/longitude",                   // 3
                    "sim/operation/failures/rel_engfai0",                   // 4
                    "sim/operation/failures/rel_engfai1",                   // 5
                    "sim/operation/failures/rel_engfai2",                   // 6
                    "sim/operation/failures/rel_engfai3",                   // 7
                    "sim/operation/failures/rel_engfai4",                   // 8
                    "sim/operation/failures/rel_engfai5",                   // 9
                    "sim/operation/failures/rel_engfai6",                   // 10
                    "sim/operation/failures/rel_engfai7",                   // 11
                    "sim/cockpit2/controls/speedbrake_ratio",               // 12
                    "sim/flightmodel/controls/parkbrake",                   // 13
                    "sim/flightmodel/engine/ENGN_oil_press_psi",            // 14
                    "sim/aircraft/limits/green_lo_oilP",                    // 15
                    "sim/time/local_time_sec",                              // 16
                    "sim/cockpit/autopilot/heading",                        // 17
                    "sim/cockpit/radios/gps2_course_degtm2",                // 18
                    "sim/flightmodel/position/groundspeed"                 // 19

            });
            float[][] engineStats = new float[][]{values[4], values[5], values[6], values[7], values[8], values[9], values[10], values[11]};
            airBrakesON = values[12][0] == 1.0f;
            wheelBrakesON = values[13][0] == 1.0f;
            reverseON = values[13][0] != 0.0f;
            enginesOK = Arrays.deepEquals(engineStats, new float[][]{{0.0f}, {0.0f}, {0.0f}, {0.0f}, {0.0f}, {0.0f}, {0.0f}, {0.0f}});
            oilPressurePerEngine = values[14];
            oilPressureGreenLo = values[15][0];
            currentTime = values[16][0];
            isPopulated = gpsIntersect.indexOfContainedCoord(values[2][0], values[3][0])[1] + 1;
            autopilotHeading = values[17][0];
            //sim/cockpit/radios/gps2_course_degtm2 = course to next gps coord
            expectedGPSCourse = values[18][0];
            groundSpeed = values[19][0];
            //sim/cockpit2/radios/indicators/gps_relative_heading_AHARS_deg_pilot = current course on GPS. Round up and that is what is displayed
        }
        catch (Throwable e)
        {
            System.err.println(e.getMessage());
            xpc = XPlaneConnector.refresh();
            return new FlightData(0, 0, 0, 0, enginesOK, wheelBrakesON, airBrakesON, reverseON, new float[]{0}, 0, 0, isPopulated, 0, 0, 0);
        }

//        if ( values.length < 4)
//        {
//            System.err.println("Somehow, values.length < 4");
//        }
        return new FlightData((int) values[0][0], (int) values[1][0], values[2][0], values[3][0], enginesOK, wheelBrakesON, airBrakesON, reverseON, oilPressurePerEngine, (double) oilPressureGreenLo, (double) currentTime, isPopulated, autopilotHeading, expectedGPSCourse, groundSpeed);
    }
}
