package us.hiai.xplane;

import gov.nasa.xpc.XPlaneConnect;
import us.hiai.data.FlightData;

import java.io.IOException;
import java.net.SocketException;
import java.util.Arrays;
import java.util.concurrent.atomic.AtomicReference;

public class XPlaneConnector
{
    private AtomicReference<XPlaneConnect> xpc = null;
    private static XPlaneConnector instance = null;

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

    public static XPlaneConnector getInstance()
    {
        if (instance == null)
        {
            instance = new XPlaneConnector();
        }
        return instance;
    }

    private XPlaneConnector()
    {
        try
        {
            xpc = new AtomicReference<>(new XPlaneConnect());
        }
        catch (SocketException e)
        {
            e.printStackTrace();
        }
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

    private void changeControlSurfacePositions(ControlSurface controlSurface, float value)
    {
        try
        {
            float[] positions = xpc.get().getCTRL(0);
            positions[controlSurface.index] = value;
            xpc.get().sendCTRL(positions);
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

    // ------------------------------------------------------------

    private float[][] getValuesFromSim(String[] strs)
    {
        try
        {
            return xpc.get().getDREFs(strs);
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
            return xpc.get().getDREF(str)[0];
        }
        catch (IOException | IndexOutOfBoundsException | NegativeArraySizeException e)
        {
            failConcisely(e, "DREF: "+str);
        }
        return 0.0f;
    }

    private void failConcisely(Exception e, String extra)
    {
        System.err.println(e.toString() + " " + extra);
    }

    private void setValueOnSim(String s, float val)
    {
        try
        {
            xpc.get().sendDREF(s, val);
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
            xpc.get().sendDREF(s, val);
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
            xpc.get().sendDREFs(strings, vals);
        }
        catch (IOException e)
        {
            e.printStackTrace();
        }
    }

    public static FlightData getFlightData()
    {
        XPlaneConnect xpc = XPlaneConnector.getInstance().xpc.get();

        float[][] values;
        float[][] engineStats;
        float[][] controlSurfaces;
        float[] reversers;
        float[] wheelBrakes;

        boolean enginesOK = true;

        boolean airBrakesON = false;
        boolean wheelBrakesON = false;
        boolean reverseON = false;

        try {

            values = xpc.getDREFs(new String[]{
                    "sim/flightmodel/position/indicated_airspeed",
                    "sim/cockpit2/gauges/indicators/altitude_ft_pilot",
                    "sim/flightmodel/position/latitude",
                    "sim/flightmodel/position/longitude"
            });

            engineStats = xpc.getDREFs(new String []{
                    "sim/operation/failures/rel_engfai0",
                    "sim/operation/failures/rel_engfai1",
                    "sim/operation/failures/rel_engfai2",
                    "sim/operation/failures/rel_engfai3",
                    "sim/operation/failures/rel_engfai4",
                    "sim/operation/failures/rel_engfai5",
                    "sim/operation/failures/rel_engfai6",
                    "sim/operation/failures/rel_engfai7"
            });

            controlSurfaces = xpc.getDREFs(new String[]{
                    "sim/cockpit2/controls/speedbrake_ratio"
            });

            wheelBrakes = xpc.getDREF("sim/flightmodel/controls/parkbrake");
            reversers = xpc.getDREF("sim/cockpit/warnings/annunciators/reverse");

            airBrakesON = controlSurfaces[0][0] == 1.0f;
            wheelBrakesON = wheelBrakes[0] == 1.0f;
            reverseON = reversers[0] != 0.0f;
            enginesOK = Arrays.deepEquals(engineStats, new float[][]{{0.0f}, {0.0f}, {0.0f}, {0.0f}, {0.0f}, {0.0f}, {0.0f}, {0.0f}});
        }
        catch (Throwable e) {
            values = new float[1][4];
            values[0][0] = (float) (Math.random() * 1000);
            values[0][1] = 1000f;
            values[0][2] = 28.1027500f;
            values[0][3] = -80.6452500f;
        }

        if ( values.length < 4)
        {
            values = new float[4][1];
            values[0][0] = (float) (Math.random() * 1000);
            values[1][0] = 1000f;
            values[2][0] = 28.1027500f;
            values[3][0] = -80.6452500f;
        }


        return new FlightData((int) values[0][0], (int) values[1][0], values[2][0], values[3][0], enginesOK, wheelBrakesON, airBrakesON, reverseON);
    }
}
