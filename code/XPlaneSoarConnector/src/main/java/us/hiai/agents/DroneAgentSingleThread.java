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
import us.hiai.util.*;
import us.hiai.util.QuadtreeStructure.CollectDecisions;
import us.hiai.util.QuadtreeStructure.Decision;
import us.hiai.xplane.XPlaneConnector;

import java.io.*;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Scanner;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import static us.hiai.xplane.XPlaneConnector.*;

/**
 * This is a single threaded Drone Controller for simulated flight with XPlane interacting with a Soar agent.
 * This Drone Controller is activated at the beginning of the flight plan before the plane has reached the first waypoint.
 * From there, the Drone Controller plays the middle man pulling drefs from XPlane, pushing input into Soar, executing Soar, and catching output from Soar.
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
    private Decision selectedPreviousDecision;
    private SoarFileEditor sfe;

    /**
     * Provides a pointer to the Graph Path.
     * The Graph Path stores data on getting the shortest path home
     * @return pointer to the Graph Path
     */
    public GraphPath getFlightWeb() {
        return flightWeb;
    }

    /**
     * Provides a pointer to the data from the latest pull from XPlane
     * @return a pointer to the latest FlightData
     */
    public FlightData getData() {
        return data;
    }

    /**
     * Provides a pointer to the structure containing the closest non-populated node that can be circled while loitering
     * @return a pointer to the LoiterInput
     */
    public LoiterInput getClosestLoiterPoint() {
        return closestLoiterPoint;
    }

    /**
     * Provides a pointer to the structure used to store information about populated areas
     * @return a pointer to the GPS_Intersection
     */
    public GPS_Intersection getGpsIntersect() {
        return gpsIntersect;
    }

    /**
     * Stores the closest node that can be circled when the plane would like to loiter
     * Contains a boolean value that is accessed by a multi-threaded program doing the calculation for the next closest point.
     */
    public static class LoiterInput {
        WaypointNode closestLoiterPoint;
        boolean keepCalculating;

        /**
         * Creates a new loiter point. This is frequently updated by the TrackClosestLoiter object as it is continually looking for a closer point to circle around
         * As long as keepCalculating is true, the TrackClosestLoiter object will continue to update the closest loiter point by performing calculation
         * @param closestLoiterPoint Starter loiter point, usually the first waypoint in the flight plan or "home"
         */
        LoiterInput(WaypointNode closestLoiterPoint) {
            this.closestLoiterPoint = closestLoiterPoint;
            keepCalculating = true;
        }
        public WaypointNode getClosestLoiterPoint() {return closestLoiterPoint;}
        public boolean isKeepCalculating() { return keepCalculating;}

    }

    /**
     * Starts the execution of the program. This is not in a constructor because as a method it can be queued into a multi-threaded program and started along with the other defined Soar controllers
     * @param flightPlanInput Path to the flight plan, a .fms file that XPlane will use for this flight
     * @param pathToPolygons Path to a folder needed for storage and retrieval in reference to the populated polygons
     * @param soarFilePath Path to the Soar file that will be executed
     * @param pathToQuadtrees Path to a folder needed for storage and retrieval in reference to the Soar's agent previous decisions
     */
    public void start(String flightPlanInput, String pathToPolygons, String soarFilePath, String pathToQuadtrees)
    {
        fpp = new FlightPlanParser(flightPlanInput);
        gpsIntersect = new GPS_Intersection(pathToPolygons);
        flightWeb = gpsIntersect.shortestPath(new WaypointNode(fpp.getCurrentWaypoint().getLatitude(), fpp.getCurrentWaypoint().getLongitude()));
        closestLoiterPoint = new LoiterInput(new WaypointNode(fpp.getCurrentWaypoint().getLatitude(), fpp.getCurrentWaypoint().getLongitude()));
        data = new FlightData(0, 0, fpp.getCurrentWaypoint().getLatitude(), fpp.getCurrentWaypoint().getLongitude(), false, false, false, false, new float[]{0}, 0, 0, 0, 0, 0, 0);
        startAlt = XPlaneConnector.getValueFromSim("sim/cockpit2/gauges/indicators/altitude_ft_pilot");

        sagt = new Agent();
        sagt.setName("DroneSingle");
        sagt.getPrinter().pushWriter(new OutputStreamWriter(System.out));
        String pathToSoar = soarFilePath.replace("/", File.separator);
        try {
            SoarCommands.source(sagt.getInterpreter(), pathToSoar);
            System.out.printf("%d Productions Loaded!\n", sagt.getProductions().getProductionCount());
        } catch (SoarException e) {
            e.printStackTrace();
        }
        // This is used for the human supervised learning
        int latestNum = 6;
        for (Production nextProduction : sagt.getProductions().getProductions(ProductionType.USER)) {
            String[] productionName = nextProduction.getName().split("drone[*]propose[*]operator[*]C");
            if (productionName.length > 1) {
                int index = Integer.parseInt(productionName[1].substring(0, productionName[1].indexOf('-')));
                if (index >= latestNum) {
                    latestNum = index + 1;
                }
            }
        }
        previousDecisions = new CollectDecisions(pathToQuadtrees, latestNum);
        sfe = new SoarFileEditor(pathToSoar, sagt);

        sagt.initialize();
        decisionCycle = Adaptables.adapt(sagt, DecisionCycle.class);
        builder = InputBuilder.create(sagt.getInputOutput());
        Symbol blank = null;
        double defaultDouble = 0.0;
        // input into Soar
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
                add("startTimer", false).markWme("sT").
                add("previousDecisionCommand", "null").markWme("pd_com").
                add("previousDecisionValue", 0).markWme("pd_val");

        // listens for activity on Soar's output link.
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
                // additional commands added in the Soar agent can be caught by adding a case
                InputWme removeCommandWME;
                switch(name) {
                    // turns on the autopilot to match the heading set in XPlane
                    // also signals to calculate the required heading and continually push it to XPlane
                    case "setAIOn":
                        setValueOnSim(dref, (float)setValue.asInteger().getValue());
                        currentBearing = 0;
                        removeCommandWME = builder.getWme("rC");
                        removeCommandWME.update(command);
                        // ADD SEND DREF TO MAKE SURE NAVIGATION IS BY GPS
                        // There doesn't appear to be one, so make sure this is on.
                        break;
                    // Calculates the shortest path back to home using logic in GraphPath
                    // This is started on its thread. While waiting for that to finish, the plane will fly to the latest loiter point
                    case "reverseWaypoints" :
                        closestLoiterPoint.keepCalculating = false;
                        LinkedList<WaypointNode> loiter = new LinkedList<>();
                        loiter.add(closestLoiterPoint.closestLoiterPoint);
                        fpp.reverseWaypoints(loiter);
                        ExecutorService executor = Executors.newFixedThreadPool(1);
                        executor.submit(new FindHome(new FindHomeInput(command, new double[]{data.lat, data.lon}, flightWeb, fpp, builder)));
                        break;
                    // Calculates given the latest bearing and ground speed will the plane be in a populated area or not
                    case "timerChecker":
                        builder.getWme("wPA").update(syms.createString(GeometryLogistics.willBeInPopulated(data.lat, data.lon, currentBearing, data.groundSpeed, gpsIntersect)));
                        builder.getWme("sT").update(syms.createString(Boolean.toString(true)));
                        removeCommandWME = builder.getWme("rC");
                        removeCommandWME.update(command);
                        break;
                    // Executes a constant descent to the provided altitude by changing the vertical speed of the aircraft
                    case "returnToAltitudeFloor":
                        long setAltitude = setValue.asInteger().getValue();
                        setValueOnSim("sim/cockpit/autopilot/altitude", ((Long)setAltitude).floatValue());
                        // autopilot state = 18 for vs control
                        // sim/cockpit/autopilot/vertical_velocity = x hundreds of feet per minute
                        returnToAltitudeFloor(command, setAltitude);
                        break;
                    // Searches around the current position of the aircraft for a previous decision that was made to speed up learning in "learned" areas
                    case "searchDecisions":
                        selectedPreviousDecision = previousDecisions.getClosestDecision(data.lat, data.lon, GeometryLogistics.calculateDistance(data.groundSpeed, 60));
                        System.out.println("TOTAL DISTANCE: " + GeometryLogistics.calculateDistance(data.groundSpeed, 60));
                        if (selectedPreviousDecision == null) {
                            builder.getWme("pd_com").update(syms.createString("null"));
                        } else {
                            builder.getWme("pd_com").update(syms.createString(selectedPreviousDecision.getDecision()));
                            Integer decisionValue = selectedPreviousDecision.getValue();
                            if (decisionValue != null) {
                                builder.getWme("pd_val").update(syms.createInteger(selectedPreviousDecision.getValue()));
                            }
                        }
                        removeCommandWME = builder.getWme("rC");
                        removeCommandWME.update(command);
                        break;
                    // Updates stored previous decisions with the decision made during the execution of this flight
                    case "saveDecision":
                        int timerLength = (int)setValue.asInteger().getValue();
                        WaypointNode decisionPoint = new WaypointNode(data.lat, data.lon);
                        if (selectedPreviousDecision != null) {
                            dref = selectedPreviousDecision.getDecision();
                        }
                        sfe.addProduction(previousDecisions.addDecision(decisionPoint, dref, timerLength));
                        removeCommandWME = builder.getWme("rC");
                        removeCommandWME.update(command);
                        break;
                    default:
                        break;
                }
            }
        });
//        sagt.getTrace().setWatchLevel(5);
//        sagt.getTrace().setEnabled(Trace.Category.BACKTRACING, true);

        // tells Soar to learn chunks
        try {
            sagt.getInterpreter().eval("learn -e");
        } catch (SoarException e) {
            e.printStackTrace();
        }

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

    /**
     * Uses another thread to descend to the provided altitude
     * @param command Pointer to the command on the output link that will be marked for removal once the descent is complete
     * @param setAltitude Altitude to descend to, it does assume that you are above that altitude
     */
    private void returnToAltitudeFloor(Symbol command, long setAltitude) {
        setValueOnSim("sim/cockpit/autopilot/autopilot_state", 18);
        // these calculations were part of an attempt to descend linearly, this wasn't working so these don't do anything right now
        double currentAlt = data.altitude;
        double totalTimeToDescend = (500-currentAlt) / -2500.0;
        double coefA = 2500.0 / totalTimeToDescend;
        double zeroTime = System.nanoTime() / 6e+10;
        Executors.newSingleThreadExecutor().submit(new VSUpdator(coefA, zeroTime, this, command, setAltitude));
    }

    /**
     * Executes the descent and indicates success when it has descended to the provided altitude
     */
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

    /**
     * Used to listen for an 'l' on the terminal which indicates that the Soar agent should take over control of the aircraft since the human has "lost connection"
     */
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

    /**
     * All the input required to find the shortest path home while maintaining control of the aircraft
     */
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

    /**
     * Contructs a new flight plan that is the shortest path back home while minimizing flight through populated areas
     */
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

    /**
     * Main loop.  This continues to run until the Soar agent has halted
     * The main steps: get flight data from XPlane, update input into Soar, run Soar for a decision cycle, repeat
     */
    private void pushFlightData()
    {
        while (!decisionCycle.isHalted()) {
            // varying debug information
//            try {
//                sagt.getInterpreter().eval("matches drone*propose*usePreviousDecision");
//            } catch (SoarException e) {
//                e.printStackTrace();
//            }
//            for (ProductionType pt : ProductionType.values()) {
//                System.out.println("Rules size: " + pt.name() + " "+ sagt.getProductions().getProductions(pt).size());
//            }
//            System.out.println("NUM CHUNKS: " + sagt.getProductions().getProductions(ProductionType.CHUNK).size());
//            if (sagt.getProductions().getProductions(ProductionType.CHUNK).size() > 0) {
//                System.out.println("CHUNKS: ");
//                for (Production nextChunk : sagt.getProductions().getProductions(ProductionType.CHUNK)) {
//                    nextChunk.print(sagt.getPrinter(), true);
//                }
//            }


            data = getFlightData(gpsIntersect);

            if (data.lat != 0 || data.lon != 0) {
                // more debug information
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

                // When in control of the aircraft, continually calculates the required bearing to fly
                // Will circle the last waypoint in the flight plan
                if (currentBearing != -1) {
                    double distance = GeometryLogistics.calculateDistanceToWaypoint(data.lat, data.lon, fpp.getCurrentWaypoint().getLatitude(), fpp.getCurrentWaypoint().getLongitude());
                    if (fpp.currentWaypoint < fpp.flightPlan.waypoints.size() - 1 && distance < GeometryLogistics.NM_METERS / 2.0) {
                        fpp.currentWaypoint++;
                    }
                    boolean circleCurrentWYPT = fpp.currentWaypoint == fpp.flightPlan.waypoints.size() - 1;
                    currentBearing = GeometryLogistics.calculateBearing(data.lat, data.lon, fpp.getCurrentWaypoint().getLatitude(), fpp.getCurrentWaypoint().getLongitude(), circleCurrentWYPT, distance);
                    XPlaneConnector.setAutopilotHeading((float)currentBearing);
                } else {
                    fpp.updateWaypoint(data.expectedGPSCourse);
                }

                sagt.runFor(1, RunType.DECISIONS);

                try {
                    Thread.sleep(500);
                } catch (InterruptedException ignored) {}
            }
        }
    }
}