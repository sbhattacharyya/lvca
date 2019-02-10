//package us.hiai.agents;
//
//import gov.nasa.xpc.XPlaneConnect;
//import org.jsoar.kernel.*;
//import org.jsoar.kernel.io.InputBuilder;
//import org.jsoar.kernel.io.InputWme;
//import org.jsoar.kernel.memory.Wme;
//import org.jsoar.kernel.parser.ParserException;
//import org.jsoar.kernel.rhs.ReordererException;
//import org.jsoar.kernel.symbols.SymbolFactory;
//import org.jsoar.util.adaptables.Adaptables;
//import org.jsoar.util.events.SoarEvent;
//import org.jsoar.util.events.SoarEventListener;
//import us.hiai.StartAgents;
//import us.hiai.data.FlightData;
//
//import java.io.FileNotFoundException;
//import java.io.IOException;
//import java.io.OutputStreamWriter;
//import java.util.*;
//
//
///**
// * Soar agent used to test soar-java interface
// */
//public class SoarAgent
//{
//    private final SymbolFactory syms;
//    Agent sagt = null;
//    InputBuilder builder;
//    double batteryLevel = 0.0;
//    double heading = 0.0;
//    double pitch = 0.0;
//    DecisionCycle decisionCycle;
//    private static XPlaneConnect xplaneConnector = null;
//
//
//    public SoarAgent()
//    {
//        sagt = new Agent();
//
//        // uncomment below to see the trace of SOAR execution.
//        // It is usually lots of text, but it is often useful
//
//        //sagt.getTrace().enableAll();
//
//        decisionCycle = Adaptables.adapt(sagt, DecisionCycle.class);
//
//        sagt.setName("ReinforcementLearningAgent");
//        sagt.getPrinter().pushWriter(new OutputStreamWriter(System.out));
//        sagt.initialize();
//        sagt.getEvents().addListener(FlightData.class, new SoarEventListener()
//        {
//            @Override
//            public void onEvent(SoarEvent soarEvent)
//            {
//                FlightData data = (FlightData) soarEvent;
//                //System.out.println("Got an event:" + data);
//
//                InputWme bl = builder.getWme("as");
//                bl.update(syms.createInteger(data.airspeed));
//                InputWme lat = builder.getWme("lat");
//                lat.update(syms.createDouble(data.lat));
//                InputWme lon = builder.getWme("lon");
//                lon.update(syms.createDouble(data.lon));
//                InputWme p = builder.getWme("alt");
//                p.update(syms.createInteger(data.altitude));
//
///*                uncomment if you want to see the productions that matched
//
//                MatchSet matchSet = sagt.getMatchSet();
//
//                if ( matchSet.getEntries().size() > 1)
//                {
//                    System.out.println("Found matching productions!!");
//                    for (MatchSetEntry mse : matchSet.getEntries())
//                    {
//                        System.out.println("Production:" + mse.getProduction());
//                    }
//                }
//*/
//                sagt.runFor(1L, RunType.DECISIONS);
//
//            }
//        });
//
//        builder = InputBuilder.create(sagt.getInputOutput());
//        builder.push("flightdata").markWme("fd").
//                add("airspeed", batteryLevel).markWme("as").
//                add("lat", heading).markWme("lat").
//                add("lon", heading).markWme("lon").
//                add("altitude", pitch).markWme("alt");
//
//
//        syms = sagt.getSymbols();
//
//        printWme(builder.getWme("fd"));
//
//
///*      uncomment this to load a set of rules from a resource text file
//        try
//        {
//            SoarCommands.source(sagt.getInterpreter(), "./src/main/resources/SimpleRules.txt");
//            System.out.println("There are now " + sagt.getProductions().getProductionCount() + " productions loaded");
//        }
//        catch (SoarException e)
//        {
//            e.printStackTrace();
//        }
//*/
//
//        /*
//        load up some rules to test input/output from java program
//         */
//        try
//        {
//            sagt.getProductions().loadProduction("proposeInitialize (state <s> ^type state -^name ) --> (<s> ^operator <o> +)(<o> ^name initialize)");
//            sagt.getProductions().loadProduction("applyInitialize (state <s>  ^operator <o>)(<o> ^name initialize) --> (<s> ^name takeoff ^last-action nothing ^wait-counter 0)");
//
//            sagt.getProductions().loadProduction("proposeRotate (state <s> ^name takeoff ^io.input-link.flightdata <fd> ^last-action <> callrotate) (<fd> ^airspeed > 10) --> (<s> ^operator <o> +)(<o> ^name callrotate)");
//            sagt.getProductions().loadProduction("callrotate (state <s> ^name takeoff ^operator <o> ^last-action <l>) (<o> ^name callrotate)  --> (<s> ^last-action <l> -)(<s> ^last-action callrotate) (write (crlf) | ROTATE!! |)");
//
//            sagt.getProductions().loadProduction("proposewait (state <s> ^name takeoff ^wait-counter <w>) --> (<s> ^operator <o> + <)(<o> ^name wait)");
//            sagt.getProductions().loadProduction("applywait (state <s> ^name takeoff ^operator <o> ^wait-counter <w>) (<o> ^name wait) --> (<s> ^wait-counter (+ <w> 1))(<s> ^wait-counter <w> -)");
//
//            sagt.getProductions().loadProduction("proposeClearRotate (state <s> ^name takeoff ^last-action callrotate ^io.input-link.flightdata <fd>) (<fd> ^airspeed = 0) --> (<s> ^operator <o> +)(<o> ^name clearrotate)");
//            sagt.getProductions().loadProduction("clearrotate (state <s> ^name takeoff ^operator <o> ^last-action <l>) (<o> ^name clearrotate)  --> (<s> ^last-action <l> -)(<s> ^last-action nothing)");
//
//            System.out.println("There are now " + sagt.getProductions().getProductionCount() + " productions loaded");
//        }
//        catch (ReordererException e)
//        {
//            e.printStackTrace();
//        }
//        catch (ParserException e)
//        {
//            e.printStackTrace();
//
//            System.exit(-1);  // quit and fix the rule
//        }
//
//
//    }
//
//    public static void main(String[] args)
//    {
//        SoarAgent sa = new SoarAgent();
//
//        try
//        {
//                xplaneConnector = StartAgents.getXPlaneConnector();
//
//
//                final Timer t = new Timer();
//
//
//            TimerTask tt = new TimerTask()
//            {
//
//                @Override
//                public void run()
//                {
//                    FlightData next = getFlightData();
//                    sa.sagt.getEvents().fireEvent(next);
//                }
//            };
//
//            t.scheduleAtFixedRate(tt, 0, 50);
//        }
//        catch (Throwable e)
//        {
//            e.printStackTrace();
//        }
//
//    }
//
//    private static FlightData getFlightData() {
//        float[][] values;
//        try {
//
//            values = xplaneConnector.getDREFs(new String[]{
//                    "sim/cockpit2/gauges/indicators/airspeed_kts_pilot",
//                    "sim/cockpit2/gauges/indicators/altitude_ft_pilot",
//                    "sim/flightmodel/position/latitude",
//                    "sim/flightmodel/position/longitude"
//            });
//        }
//        catch (Throwable e) {
//            values = new float[1][4];
//            values[0][0] = (float) (Math.random() * 1000);
//            values[0][1] = 1000f;
//            values[0][2] = 28.1027500f;
//            values[0][3] = -80.6452500f;
//        }
//
//        if ( values.length < 4)
//        {
//            values = new float[4][1];
//            values[0][0] = (float) (Math.random() * 1000);
//            values[1][0] = 1000f;
//            values[2][0] = 28.1027500f;
//            values[3][0] = -80.6452500f;
//        }
//        return new FlightData((int) values[0][0], (int) values[1][0], values[2][0], values[3][0], true, false, false, false);
//    }
//
//    public void printWme(Wme wme)
//    {
//        System.out.println(wme);
//        Iterator<Wme> children = wme.getChildren();
//        while (children.hasNext())
//        {
//            Wme child = children.next();
//            printWme(child);
//        }
//    }
//
//
//    /*
//            sagt.getProductions().loadProduction("test1 (state <s> ^superstate nil) --> (<s> ^foo 1)");
//            sagt.getProductions().loadProduction("test2 (state <s> ^superstate nil ^foo 1) --> (<s> ^foo 2) (write (crlf) |found foo|)");
//            sagt.getProductions().loadProduction("fdtest (state <s> ^foo 2 ^io.input-link.flightdata <fd>)  --> (<s> ^foo 3) (write (crlf) |found flight data|)");
//            sagt.getProductions().loadProduction("fdtest2 (state <s> ^foo 3 ^io.input-link.flightdata <fd>)(<fd> ^airspeed > 50 )  --> (<s> ^foo 4) (write (crlf) |AS > 50wg | )");
//            sagt.getProductions().loadProduction("fdtest3 (state <s> ^foo 4)  --> (<s> ^foo 5 ^operator <op>)(<op> ^name checklist) (write (crlf) |create checklist op |)");
//            sagt.getProductions().loadProduction("fdtest4 (state <s> ^operator <op>)(<op> ^name checklist)  --> (<s> ^condition <c> ^operator <op>)(<c> ^name cond1)(<op> ^name nextstep) (write (crlf) |perform checklist, set cond1 and go to nextstep |)");
//            sagt.getProductions().loadProduction("fdtest5 (state <s> ^operator <op> ^condition <c>)(<c> ^name cond1)  --> (write (crlf) |in cond1 found  |<op> |   |  <c>)");
//*/
//
//}
