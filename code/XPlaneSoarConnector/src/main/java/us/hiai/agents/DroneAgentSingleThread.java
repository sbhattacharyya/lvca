package us.hiai.agents;

import freemarker.cache.ConcurrentCacheStorage;
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
import us.hiai.util.*;
import us.hiai.util.QuadtreeStructure.CollectDecisions;
import us.hiai.util.QuadtreeStructure.Decision;
import us.hiai.xplane.XPlaneConnector;

import java.io.*;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Scanner;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import static us.hiai.xplane.XPlaneConnector.*;

/**
 * Created by Daniel Griessler Spring 2019
 */
public class DroneAgentSingleThread
{
    private SymbolFactory syms;
    private InputBuilder builder;
    private DecisionCycle decisionCycle;
    private boolean takeOver = false;
    private Agent sagt;
    private GPS_Intersection gpsIntersect;
    private GraphPath flightWeb;
    private FlightPlanParser fpp;
    private double currentBearing = -1;
    private FlightData data;
    private LoiterInput closestLoiterPoint;
    private double startAlt;
    private CollectDecisions previousDecisions;

    public GraphPath getFlightWeb() {
        return flightWeb;
    }

    public FlightData getData() {
        return data;
    }

    public LoiterInput getClosestLoiterPoint() {
        return closestLoiterPoint;
    }

    public GPS_Intersection getGpsIntersect() {
        return gpsIntersect;
    }

    public static class LoiterInput {
        WaypointNode closestLoiterPoint;
        boolean keepCalculating;
        LoiterInput(WaypointNode closestLoiterPoint) {
            this.closestLoiterPoint = closestLoiterPoint;
            keepCalculating = true;
        }
        public WaypointNode getClosestLoiterPoint() {return closestLoiterPoint;}
        public boolean isKeepCalculating() { return keepCalculating;}

    }

    public void start()
    {
        String flightPlanInputFile = "/home/dgriessl/X-Plane 11/Output/FMS plans/DallasOut156.fms";
        fpp = new FlightPlanParser(flightPlanInputFile);
        gpsIntersect = new GPS_Intersection("/home/dgriessl/IdeaProjects/lvca/code/XPlaneSoarConnector/src/main/java/us/hiai/util/populatedAreas");
        flightWeb = gpsIntersect.shortestPath(fpp.getCurrentWaypoint());
        closestLoiterPoint = new LoiterInput(fpp.getCurrentWaypoint());
        data = new FlightData(0, 0, fpp.getCurrentWaypoint().getLatitude(), fpp.getCurrentWaypoint().getLongitude(), false, false, false, false, new float[]{0}, 0, 0, 0, 0, 0, 0);
        startAlt = XPlaneConnector.getValueFromSim("sim/cockpit2/gauges/indicators/altitude_ft_pilot");
        //previousDecisions = new CollectDecisions("/home/dgriessl/IdeaProjects/lvca/code/XPlaneSoarConnector/src/main/java/us/hiai/util/QuadtreeStructure", flightWeb.getElements());

        sagt = new Agent();
        sagt.setName("DroneSingle");
        sagt.getPrinter().pushWriter(new OutputStreamWriter(System.out));
        String pathToSoar = "/home/dgriessl/IdeaProjects/lvca/code/SoarToUPPAALTranslator/src/main/Soar/TestXPlaneDrone.soar".replace("/", File.separator);
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
                add("populated", "null").markWme("pop").
                add("autopilotHeading", defaultDouble).markWme("autoHead").
                add("takeOver", takeOver).markWme("tOver").
                add("removeCommand", blank).markWme("rC").
                add("willBeInPopulatedArea", "null").markWme("wPA").
                add("startTimer", false).markWme("sT");

        sagt.getEvents().addListener(OutputEvent.class, soarEvent -> {
            System.out.println("OUT EVENT");
            OutputEvent out = (OutputEvent) soarEvent;
            Symbol command = null;
            String dref = null;
            Symbol setValue = null;
            String name = null;
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
                    case "name":
                        name = value.asString().getValue();
                        break;
                    default:
                        break;
                }
            }
            System.out.println("DONE OUT EVENT");
            if (dref != null && setValue != null && name != null) {
                InputWme removeCommandWME;
                switch(name) {
                    case "setAIOn":
                        setValueOnSim(dref, (float)setValue.asInteger().getValue());
                        currentBearing = 0;
                        removeCommandWME = builder.getWme("rC");
                        removeCommandWME.update(command);
                        // ADD SEND DREF TO MAKE SURE NAVIGATION IS BY GPS
                        // There doesn't appear to be one, so make sure this is on.
                        break;
                    case "reverseWaypoints" :
                        closestLoiterPoint.keepCalculating = false;
                        LinkedList<WaypointNode> loiter = new LinkedList<>();
                        loiter.add(closestLoiterPoint.closestLoiterPoint);
                        fpp.reverseWaypoints(loiter);
                        ExecutorService executor = Executors.newFixedThreadPool(1);
                        executor.submit(new FindHome(new FindHomeInput(command, new double[]{data.lat, data.lon}, flightWeb, fpp, builder)));
                        break;
                    case "timerChecker":
                        builder.getWme("wPA").update(syms.createString(GeometryLogistics.willBeInPopulated(data.lat, data.lon, currentBearing, data.groundSpeed, gpsIntersect)));
                        builder.getWme("sT").update(syms.createString(Boolean.toString(true)));
                        removeCommandWME = builder.getWme("rC");
                        removeCommandWME.update(command);
                        break;
                    case "returnToAltitudeFloor":
                        long setAltitude = setValue.asInteger().getValue();
                        setValueOnSim("sim/cockpit/autopilot/altitude", ((Long)setAltitude).floatValue());
                        // autopilot state = 18 for vs control
                        // sim/cockpit/autopilot/vertical_velocity = x hundreds of feet per minute
                        returnToAltitudeFloor(command, setAltitude);
                        break;
                    default:
                        break;
                }
            }
        });

        syms = sagt.getSymbols();
        Future ff = Executors.newSingleThreadExecutor().submit(this::flipFlag);
        Future ff1 = Executors.newSingleThreadExecutor().submit(new TrackClosestLoiter(this));
        pushFlightData();
        sagt.dispose();
        ff.cancel(true);
        closestLoiterPoint.keepCalculating = false;
        try {
            ff1.get();
        } catch(InterruptedException | ExecutionException e) {
            e.printStackTrace();
        }
        ff1.cancel(true);
    }

    private void returnToAltitudeFloor(Symbol command, long setAltitude) {
        setValueOnSim("sim/cockpit/autopilot/autopilot_state", 18);
        double currentAlt = data.altitude;
        double totalTimeToDescend = (500-currentAlt) / -2500.0;
        double coefA = 2500.0 / totalTimeToDescend;
        double zeroTime = System.nanoTime() / 6e+10;
        Executors.newSingleThreadExecutor().submit(new VSUpdator(coefA, zeroTime, this, command, setAltitude));
    }

    static class VSUpdator implements Runnable {
        double coefA;
        double zeroTime;
        DroneAgentSingleThread dst;
        Symbol command;
        long setAltitude;
        VSUpdator(double coefA, double zeroTime, DroneAgentSingleThread dst, Symbol command, long setAltitude) {
            this.coefA = coefA;
            this.zeroTime = zeroTime;
            this.dst = dst;
            this.command = command;
            this.setAltitude = setAltitude;
        }
        @Override
        public void run() {
            while (Math.abs(dst.data.altitude - setAltitude + dst.startAlt) > 1) {
                // attempt to do linear descent.  Not working correctly
//                double currentTime = System.nanoTime() / 6e+10;
//                float val = (float)(Math.round((2*coefA*(currentTime - zeroTime) - 5000) / 100) * 100);
//                if (val > 0) {
//                    break;
//                }
//                System.out.println("zeroTime: " + zeroTime + " currentTime: " + currentTime + "with coefA: " + coefA +" calculated run val: " + val);

                // currently constant descent.  Should make it more speedy by fixing the linear descent
                float val = -500;
                setValueOnSim("sim/cockpit/autopilot/vertical_velocity", val);
                try {
                    Thread.sleep(1000);
                } catch (InterruptedException e) {
                    e.printStackTrace();
                }
            }
            System.out.println("Final alt: " + dst.data.altitude);
            setValueOnSim("sim/cockpit/autopilot/vertical_velocity", 0);
            setValueOnSim("sim/cockpit/autopilot/autopilot_state", 16386);
            InputWme removeCommandWME = dst.builder.getWme("rC");
            removeCommandWME.update(command);
        }
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

    static class FindHomeInput {
        Symbol command;
        double[] latAndLon;
        GraphPath flightWeb;
        FlightPlanParser fpp;
        InputBuilder builder;
        FindHomeInput(Symbol command, double[] latAndLon, GraphPath flightWeb, FlightPlanParser fpp, InputBuilder builder) {
            this.command = command;
            this.latAndLon = latAndLon;
            this.flightWeb = flightWeb;
            this.fpp = fpp;
            this.builder = builder;
        }

    }

    static class FindHome implements Runnable {

        FindHomeInput fhi;
        FindHome(FindHomeInput fhi) {
            this.fhi = fhi;
        }
        @Override
        public void run() {
            LinkedList<WaypointNode> pathHome = fhi.flightWeb.findPathHome(fhi.latAndLon[0], fhi.latAndLon[1]);
            fhi.fpp.reverseWaypoints(pathHome);
            InputWme removeCommandWME = fhi.builder.getWme("rC");
            removeCommandWME.update(fhi.command);
        }
    }

    private void pushFlightData()
    {
        while (!decisionCycle.isHalted()) {
            System.out.println("Rules size: " + sagt.getProductions().getProductionCount());
            if (sagt.getProductions().getProductions(ProductionType.CHUNK).size() > 0) {
                System.out.println("CHUNKS: ");
                for (Production nextChunk : sagt.getProductions().getProductions(ProductionType.CHUNK)) {
                    System.out.println(nextChunk.toString());
                }
            }

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
                System.out.print("\t\tclosestLoiter: " + closestLoiterPoint.closestLoiterPoint.toString());
                System.out.println(); // 370, 1.9

                InputWme bl = builder.getWme("as");
                bl.update(syms.createInteger(data.airspeed));
                InputWme lat = builder.getWme("lat");
                lat.update(syms.createDouble(data.lat));
                InputWme lon = builder.getWme("lon"); //32.897167 -97.03767
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
                String pop;
                switch (data.isPopulated) {
                    case 1:
                        pop = "fully";
                        break;
                    case 2:
                        pop = "lightly";
                        break;
                    default:
                        pop = "null";
                }
                populated.update(syms.createString(pop));
                InputWme autopilotHeading = builder.getWme("autoHead");
                autopilotHeading.update(syms.createDouble(data.autopilotHeading));
                InputWme soarControl = builder.getWme("tOver");
                soarControl.update(syms.createString(Boolean.toString(takeOver)));

                if (currentBearing != -1) {
                    double distance = GeometryLogistics.calculateDistanceToWaypoint(data.lat, data.lon, fpp.getCurrentWaypoint().getLatitude(), fpp.getCurrentWaypoint().getLongitude());
                    if (fpp.currentWaypoint < fpp.flightPlan.waypoints.size() - 1 && distance < GeometryLogistics.NM_METERS / 2.0) {
                        fpp.currentWaypoint++;
                    }
                    boolean circleCurrentWYPT;
                    if (fpp.currentWaypoint == fpp.flightPlan.waypoints.size() - 1)
                        circleCurrentWYPT = true;
                    else
                        circleCurrentWYPT = false;
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