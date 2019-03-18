package us.hiai.agents;

import org.jsoar.kernel.*;
import org.jsoar.kernel.events.OutputEvent;
import org.jsoar.kernel.io.InputBuilder;
import org.jsoar.kernel.io.InputWme;
import org.jsoar.kernel.memory.Wme;
import org.jsoar.kernel.symbols.Symbol;
import org.jsoar.kernel.symbols.SymbolFactory;
import org.jsoar.util.adaptables.Adaptables;
import org.jsoar.util.commands.SoarCommands;
import us.hiai.data.FlightData;
import us.hiai.util.FlightPlanParser;
import us.hiai.util.GPS_Intersection;
import us.hiai.util.WaypointNode;
import us.hiai.xplane.XPlaneConnector;

import java.io.*;
import java.util.Iterator;
import java.util.Scanner;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import static us.hiai.xplane.XPlaneConnector.*;

public class DroneAgentSingleThread
{

    private static final int EARTH_RADIUS = 6371000;
    public static final int NM_METERS = 1852;
    private SymbolFactory syms;
    private InputBuilder builder;
    private DecisionCycle decisionCycle;
    private boolean takeOver = false;
    private Agent sagt;
    private GPS_Intersection gpsIntersect;
    private FlightPlanParser fpp;
    private double currentBearing = -1;
    private static final double convertToRadians = Math.PI / 180;
    private FlightData data;
    private boolean circleCurrentWYPT;

    public void start()
    {
        String flightPlanInputFile = "/home/dgries/X-Plane 11/Output/FMS plans/DallasOut156.fms";
        fpp = new FlightPlanParser(flightPlanInputFile);

        gpsIntersect = new GPS_Intersection();
        sagt = new Agent();
        sagt.setName("DroneSingle");
        sagt.getPrinter().pushWriter(new OutputStreamWriter(System.out));
        String pathToSoar = "/home/dgries/Desktop/Daniel_Griessler_Internship_Files/Translator_Source_Code/lvca/code/SoarToUPPAALTranslator/src/main/Soar/TestXPlaneDrone.soar".replace("/", File.separator);
        try {
            SoarCommands.source(sagt.getInterpreter(), pathToSoar);
            System.out.printf("%d Productions Loaded!\n", sagt.getProductions().getProductionCount());
        } catch (SoarException e) {
            e.printStackTrace();
        }
        sagt.initialize();
        decisionCycle = Adaptables.adapt(sagt, DecisionCycle.class);
        builder = InputBuilder.create(sagt.getInputOutput());
        Symbol blank = null;
        double defaultDouble = 0.0;
        builder.push("flightdata").markWme("fd").
                add("airspeed", defaultDouble).markWme("as").
                add("lat", defaultDouble).markWme("lat").
                add("lon", defaultDouble).markWme("lon").
                add("altitude", defaultDouble).markWme("alt").
                add("allEnginesOK", true).markWme("engOK").
                add("wheelbrakesON", false).markWme("wBrakes").
                add("airbrakesON", false).markWme("aBrakes").
                add("reversersON", false).markWme("reverse").
                add("oilPressureEngine1", defaultDouble).markWme("op1").
                add("oilPressureEngine2", defaultDouble).markWme("op2").
                add("oilPressureEngine3", defaultDouble).markWme("op3").
                add("oilPressureEngine4", defaultDouble).markWme("op4").
                add("oilPressureEngine5", defaultDouble).markWme("op5").
                add("oilPressureEngine6", defaultDouble).markWme("op6").
                add("oilPressureEngine7", defaultDouble).markWme("op7").
                add("oilPressureEngine8", defaultDouble).markWme("op8").
                add("oilPressureGreenLo", defaultDouble).markWme("oGrLo").
                add("currentTime", defaultDouble).markWme("cT").
                add("populated", false).markWme("pop").
                add("autopilotHeading", defaultDouble).markWme("autoHead").
                add("takeOver", takeOver).markWme("tOver").
                add("removeCommand", blank).markWme("rC").
                add("willBeInPopulatedArea", false).markWme("wPA").
                add("startTimer", false).markWme("sT");

        sagt.getEvents().addListener(OutputEvent.class, soarEvent -> {
            System.out.println("OUT EVENT");
            OutputEvent out = (OutputEvent) soarEvent;
            Symbol command = null;
            String dref = null;
            Symbol setValue = null;
            Iterator<Wme> children = out.getWmes();
            while (children.hasNext()) {
                Wme temp = children.next();
                System.out.println(temp);
                String attribute = temp.getAttribute().asString().getValue();
                Symbol value = temp.getValue();
                switch (attribute) {
                    case "command":
                        command = value;
                        break;
                    case "dref":
                        dref = value.asString().getValue();
                        break;
                    case "setValue":
                        setValue = value;
                        break;
                    default:
                        break;
                }
            }
            System.out.println("DONE OUT EVENT");
            if (command != null) {
                InputWme removeCommandWME = builder.getWme("rC");
                removeCommandWME.update(command);
            }
            if (dref != null && setValue != null) {
                switch(dref) {
                    case "sim/cockpit/autopilot/autopilot_mode":
                        setValueOnSim(dref, (float)setValue.asInteger().getValue());
                        // ADD SEND DREF TO MAKE SURE NAVIGATION IS BY GPS
                        break;
                    case "null" :
                        String setValueString = setValue.asString().getValue();
                        if (setValueString.equals("reverse"))
                            returnToHome();
                        else if (setValueString.equals("calculateWillBeInPopulatedArea")) {
                            builder.getWme("wPA").update(syms.createString(Boolean.toString(willBeInPopulated(data.lat, data.lon, currentBearing, data.groundSpeed, 60))));
                            builder.getWme("sT").update(syms.createString(Boolean.toString(true)));
                        }
                        break;
                    default:
                        break;
                }
            }
        });

        syms = sagt.getSymbols();
        Future ff = Executors.newSingleThreadExecutor().submit(this::flipFlag);
        pushFlightData();
        sagt.dispose();
        ff.cancel(true);
    }

    private void flipFlag() {
        Scanner in = new Scanner(System.in);
        while (in.hasNextLine()) {
            String nextLine = in.nextLine();
            if (nextLine.equals("l")) {
                takeOver = !takeOver;
            } else if (nextLine.equals("q")) {
                break;
            }
        }
    }

    private double calculateBearing(double planeLat, double planeLong) {
        double distance = calculateDistanceToCurrentWaypoint(planeLat, planeLong);
        double lat1 = planeLat * convertToRadians;
        double lat2 = fpp.getCurrentWaypoint().getLatitude() * convertToRadians;
        double longDif = (fpp.getCurrentWaypoint().getLongitude() - planeLong) * convertToRadians;
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

    private double calculateDistanceToCurrentWaypoint(double planeLat, double planeLong) {
        double lat1 = planeLat * convertToRadians;
        double lat2 = fpp.getCurrentWaypoint().getLatitude() * convertToRadians;
        double latDif = ((planeLat - fpp.getCurrentWaypoint().getLatitude()) * convertToRadians) / 2;
        double longDif = ((planeLong - fpp.getCurrentWaypoint().getLongitude()) * convertToRadians) / 2;
        double a = Math.sin(latDif) * Math.sin(latDif) + Math.cos(lat1) * Math.cos(lat2) * Math.sin(longDif) * Math.sin(longDif);
        double c = 2 * Math.atan2(Math.sqrt(a), Math.sqrt(1-a));
        // earth's radius = 6371000 m
        double distance = EARTH_RADIUS * c;
        // 1852 meters = 1 nautical mile
        if (distance < NM_METERS && fpp.currentWaypoint < fpp.flightPlan.waypoints.size() - 1) {
                fpp.currentWaypoint++;
                if (fpp.currentWaypoint == fpp.flightPlan.waypoints.size() - 1)
                    circleCurrentWYPT = true;
        }
        return distance;
    }

    private boolean willBeInPopulated (double currentLat, double currentLong, double currentBearing, double groundSpeed, double time) {
        double maxDistance = calculateDistance(groundSpeed, time);
        double currentDistance = maxDistance;
        double[] destination;
        int iterations = 100;
        for (int i = 0; i < iterations; i++) {
            destination = calculateDestination(currentLat, currentLong, currentBearing, currentDistance);
            if(gpsIntersect.coordIsContained(destination[0], destination[1])) {
                return true;
            }
            currentDistance -= maxDistance / iterations;
        }
        return false;
    }

    private double calculateDistance(double groundSpeed, double time) {
        // distance is calculated by speed / time which is returned in nautical miles.  To convert to m, then multiply by 1852
        return (groundSpeed / time) * 1852;
    }

    private double[] calculateDestination (double currentLat, double currentLong, double currentBearing, double distance) {
        double radCurrentLat = currentLat * convertToRadians;
        double radCurrentBearing = currentBearing * convertToRadians;
        double radCurrentLong = currentLong * convertToRadians;
        double lat = Math.asin(Math.sin(radCurrentLat) * Math.cos(distance / EARTH_RADIUS) + Math.cos(radCurrentLat) * Math.sin(distance / EARTH_RADIUS) * Math.cos(radCurrentBearing));
        double lon = radCurrentLong + Math.atan2(Math.sin(radCurrentBearing) * Math.sin(distance / EARTH_RADIUS) * Math.cos(radCurrentLat), Math.cos(distance / EARTH_RADIUS) - Math.sin(radCurrentLat) * Math.sin(lat));
        return new double[]{lat / convertToRadians, (((lon / convertToRadians) + 540) % 360) - 180};
    }

    private void returnToHome() {
        // change flightPlan back to private in FlightPlanParser
        fpp.reverseWaypoints();
        currentBearing = 0;
        if (fpp.currentWaypoint == fpp.flightPlan.waypoints.size() - 1)
            circleCurrentWYPT = true;
    }

    private void pushFlightData()
    {
        while (!decisionCycle.isHalted()) {
            data = getFlightData(gpsIntersect);

            if (data.lat != 0 || data.lon != 0) {
//                for (int i = 0; i < data.oilPressurePerEngine.length; i++) {
//                    System.out.printf("\t\tOilPressure%d: %f", i + 1, data.oilPressurePerEngine[i]);
//                }
//                System.out.println("\t\tOilGreenLo: " + data.oilPressureGreenLo + "\t\tCurrentTime: " + data.currentTime + "\t\tCurrentSpeed: " + data.airspeed + "\t\tIsPopulated: " + data.isPopulated);
//                System.out.print("\t\tIsPopulated: " + data.isPopulated + "\t\tautopilotHeading: " + data.autopilotHeading +
//                        "\t\ttakeOver: " + takeOver + "\t\texpectedGPSCourse: " + data.expectedGPSCourse + "\t\tcurrentWayPoint" + fpp.getCurrentWaypoint().toString());
                System.out.print("\t\tpopulated: " + data.isPopulated +"\t\ttakeOver: " + takeOver +"\t\tlat: " + data.lat + "\t\tlon: " + data.lon + "\t\tcurrentBearing: " + currentBearing);
                System.out.print("\t\tcurrentWayPoint: " + fpp.getCurrentWaypoint().toString());
                for (WaypointNode waypoint : fpp.flightPlan.waypoints) {
                    System.out.print("\t\t" + waypoint.toString());
                }
                System.out.println(); // 370, 1.9

                InputWme bl = builder.getWme("as");
                bl.update(syms.createInteger(data.airspeed));
                InputWme lat = builder.getWme("lat");
                lat.update(syms.createDouble(data.lat));
                InputWme lon = builder.getWme("lon");
                lon.update(syms.createDouble(data.lon));
                InputWme p = builder.getWme("alt");
                p.update(syms.createInteger(data.altitude));
                InputWme e = builder.getWme("engOK");
                e.update(syms.createString(Boolean.toString(data.allEningesOK)));
                InputWme wb = builder.getWme("wBrakes");
                wb.update(syms.createString(Boolean.toString(data.wheelBrakesON)));
                InputWme ab = builder.getWme("aBrakes");
                ab.update(syms.createString(Boolean.toString(data.airBrakesON)));
                InputWme re = builder.getWme("reverse");
                re.update(syms.createString(Boolean.toString(data.reversersON)));

                for (int i = 0; i < data.oilPressurePerEngine.length; i++) {
                    InputWme op = builder.getWme("op" + (i + 1));
                    op.update(syms.createDouble(data.oilPressurePerEngine[i]));
                }
                InputWme oilGreenLo = builder.getWme("oGrLo");
                oilGreenLo.update(syms.createDouble(data.oilPressureGreenLo));
                InputWme currentTime = builder.getWme("cT");
                currentTime.update(syms.createDouble(data.currentTime));
                InputWme populated = builder.getWme("pop");
                boolean pop = data.isPopulated == 1;
                populated.update(syms.createString(Boolean.toString(pop)));
                InputWme autopilotHeading = builder.getWme("autoHead");
                autopilotHeading.update(syms.createDouble(data.autopilotHeading));
                InputWme soarControl = builder.getWme("tOver");
                soarControl.update(syms.createString(Boolean.toString(takeOver)));

                if (currentBearing != -1) {
                    currentBearing = calculateBearing(data.lat, data.lon);
                    XPlaneConnector.setAutopilotHeading((float)currentBearing);
                } else {
                    fpp.updateWaypoint(data.expectedGPSCourse);
                }

                sagt.runFor(1, RunType.DECISIONS);

                try {
                    Thread.sleep(500);
                } catch (InterruptedException er) {}
            }
        }
    }

    private void printWme(Wme wme)
    {
        System.out.println(wme);
        Iterator<Wme> children = wme.getChildren();
        while (children.hasNext())
        {
            Wme child = children.next();
            printWme(child);
        }
    }
}