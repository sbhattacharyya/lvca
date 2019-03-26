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
import us.hiai.util.GeometryLogistics;
import us.hiai.util.WaypointNode;
import us.hiai.xplane.XPlaneConnector;

import java.io.*;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Scanner;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import static us.hiai.xplane.XPlaneConnector.*;

public class DroneAgentSingleThread
{
    private SymbolFactory syms;
    private InputBuilder builder;
    private DecisionCycle decisionCycle;
    private boolean takeOver = false;
    private Agent sagt;
    private GPS_Intersection gpsIntersect;
    private FlightPlanParser fpp;
    private double currentBearing = -1;
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
                        gpsIntersect.shortestPath(new double[]{data.lat, data.lon}, new double[]{fpp.getHome().getLatitude(), fpp.getHome().getLongitude()});
                        // ADD SEND DREF TO MAKE SURE NAVIGATION IS BY GPS
                        break;
                    case "null" :
                        String setValueString = setValue.asString().getValue();
                        if (setValueString.equals("reverse"))
                            returnToHome();
                        else if (setValueString.equals("calculateWillBeInPopulatedArea")) {
                            builder.getWme("wPA").update(syms.createString(Boolean.toString(GeometryLogistics.willBeInPopulated(data.lat, data.lon, currentBearing, data.groundSpeed, gpsIntersect))));
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

    private void returnToHome() {
        // change flightPlan back to private in FlightPlanParser
        fpp.reverseWaypoints();
        currentBearing = 0;
        if (fpp.currentWaypoint == fpp.flightPlan.waypoints.size() - 1)
            circleCurrentWYPT = true;
    }

    private void findPath(double planeLat, double planeLon, double currentBearing) {
        LinkedList<double[]> pathToHome = new LinkedList<>();
        pathToHome.add(new double[]{planeLat, planeLon});
        WaypointNode home = fpp.getHome();

        double distanceToHome = GeometryLogistics.calculateDistanceToWaypoint(planeLat, planeLon, home.getLatitude(), home.getLongitude());
        HashSet<Integer> intersectedPolygonIndexes = new HashSet<>();
        for (double i = 0; i < distanceToHome; i = i + 1.0 / distanceToHome) {
            double[] destinationPoint = GeometryLogistics.calculateDestination(planeLat, planeLon, currentBearing, i);
            int intersectedIndex = gpsIntersect.indexOfContainedCoord(destinationPoint[0], destinationPoint[1]);
            if (intersectedIndex != -1) {
                intersectedPolygonIndexes.add(intersectedIndex);
            }
        }

        if (intersectedPolygonIndexes.size() != 0) {

        }

        pathToHome.add(new double[]{home.getLatitude(), home.getLongitude()});
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
                    double distance = GeometryLogistics.calculateDistanceToWaypoint(data.lat, data.lon, fpp.getCurrentWaypoint().getLatitude(), fpp.getCurrentWaypoint().getLongitude());
                    if (distance < GeometryLogistics.NM_METERS && fpp.currentWaypoint < fpp.flightPlan.waypoints.size() - 1) {
                        fpp.currentWaypoint++;
                        if (fpp.currentWaypoint == fpp.flightPlan.waypoints.size() - 1)
                            circleCurrentWYPT = true;
                    }
                    currentBearing = GeometryLogistics.calculateBearing(data.lat, data.lon, fpp.getCurrentWaypoint().getLatitude(), fpp.getCurrentWaypoint().getLongitude(), circleCurrentWYPT, distance);
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