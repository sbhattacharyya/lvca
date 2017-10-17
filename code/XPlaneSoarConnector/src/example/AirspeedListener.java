//package us.hiai.agents;
//
//import org.jsoar.kernel.*;
//import org.jsoar.kernel.events.BeforeDecisionCycleEvent;
//import org.jsoar.kernel.events.InputEvent;
//import org.jsoar.kernel.events.RunLoopEvent;
//import org.jsoar.kernel.io.InputOutput;
//import org.jsoar.kernel.io.InputWme;
//import org.jsoar.kernel.io.InputWmes;
//import org.jsoar.kernel.io.quick.DefaultQMemory;
//import org.jsoar.kernel.io.quick.QMemory;
//import org.jsoar.kernel.io.quick.SoarQMemoryAdapter;
//import org.jsoar.kernel.symbols.Identifier;
//import org.jsoar.kernel.symbols.Symbol;
//import org.jsoar.kernel.symbols.SymbolFactory;
//import org.jsoar.util.commands.SoarCommands;
//import org.jsoar.util.events.SoarEvent;
//import org.jsoar.util.events.SoarEventListener;
//import us.hiai.data.FlightData;
//
//import java.io.IOException;
//import java.util.Timer;
//import java.util.TimerTask;
//import java.util.concurrent.Executors;
//import java.util.concurrent.ScheduledExecutorService;
//import java.util.concurrent.TimeUnit;
//
///**
// * Created by icislab on 10/3/2016.
// */
//public class AirspeedListener extends XPlaneAgent
//{
//    QMemory memory;
//    SoarQMemoryAdapter adapter;
//
//
//    @Override
//    protected String name()
//    {
//        return "AirspeedListener";
//    }
//
//    public boolean runOnStartup()
//    {
//        return false;
//    }
//
//    @Override
//    public void start()
//    {
//        try
//        {
//            SoarCommands.source(getAgent().getInterpreter(), "C:\\Users\\icislab\\IdeaProjects\\XPlaneSoarConnector\\src\\main\\soar\\agents\\airspeed_listener.soar");
//            memory = DefaultQMemory.create();
//            memory.setInteger("flightdata.airspeed", 0);
//            memory.setInteger("flightdata.altitude", 0);
//            memory.setDouble("flightdata.lat", 28.1027500 );
//            memory.setDouble("flightdata.lon", -80.6452500 );
//            adapter = SoarQMemoryAdapter.attach(getAgent(), memory);
//            ScheduledExecutorService executor = Executors.newSingleThreadScheduledExecutor();
//            executor.scheduleAtFixedRate(this::pushAirspeed, 100, 20, TimeUnit.MILLISECONDS);
//
//            getAgent().getEvents().addListener(InputEvent.class, new AirspeedEventListener());
//        }
//        catch (SoarException e)
//        {
//            e.printStackTrace();
//        }
//    }
//
//    private void pushAirspeed()
//    {
//        float[][] values;
//        try {
//
//            values = getXPlaneConnector().getDREFs(new String[]{
//                    "sim/cockpit2/gauges/indicators/airspeed_kts_pilot",
//                    "sim/cockpit2/gauges/indicators/altitude_ft_pilot",
//                    "sim/flightmodel/position/latitude",
//                    "sim/flightmodel/position/longitude"
//            });
//        }
//        catch (Throwable e)
//        {
//            System.err.println(e.getMessage());
//           values = new float[1][4];
////            values[0][0] = (float)(Math.random()*1000);
////            values[0][1] = 1000f;
////            values[0][2] = 28.1027500f;
////            values[0][3] = -80.6452500f;
//        }
//
//        try
//        {
//
////            int speed = (int)values[0][0];
//
//            memory.setInteger("flightdata.airspeed", (int)(values[0][0]));
//            memory.setInteger("flightdata.altiude", (int)(values[1][0]));
//            memory.setDouble("flightdata.lat", (double)(values[2][0]));
//            memory.setDouble("flightdata.lon", (double)(values[3][0]));
//
//            long memspeed = memory.getInteger("flightdata.airspeed");
//            long memalt = memory.getInteger("flightdata.altitude");
//            double memlat = memory.getDouble("flightdata.lat");
//            double memlon = memory.getDouble("flightdata.lon");
//
//            System.out.println("Airspeed is: " +  memspeed);
//
//            getAgent().getEvents().fireEvent(new FlightData((int)memspeed, (int)memalt, memlat, memlon));
//        }
//        catch (Throwable e)
//        {
//            e.printStackTrace();
//        }
//    }
//
//    private class AirspeedEventListener implements SoarEventListener
//    {
//        @Override
//        public void onEvent(SoarEvent soarEvent)
//        {
//            try {
//                // uncomment if you want to see the productions that matched
//                MatchSet matchSet = getAgent().getMatchSet();
//
//                if (matchSet.getEntries().size() > 1) {
//                    System.out.println("Found matching productions!!");
//                    for (MatchSetEntry mse : matchSet.getEntries()) {
//                        System.out.println("Production:" + mse.getProduction());
//                    }
//                }
//
//                getAgent().runFor(1L, RunType.DECISIONS);
//            }
//            catch (Throwable t)
//            {
//                 t.printStackTrace();
//            }
//        }
//    }
//}
//