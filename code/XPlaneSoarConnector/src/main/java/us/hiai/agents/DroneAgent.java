package us.hiai.agents;

import kotlin.ranges.IntRange;
import org.jsoar.kernel.*;
import org.jsoar.kernel.events.OutputEvent;
import org.jsoar.kernel.io.InputBuilder;
import org.jsoar.kernel.io.InputOutput;
import org.jsoar.kernel.io.InputWme;
import org.jsoar.kernel.io.OutputChange;
import org.jsoar.kernel.io.quick.DefaultQMemory;
import org.jsoar.kernel.io.quick.QMemory;
import org.jsoar.kernel.io.quick.SoarQMemoryAdapter;
import org.jsoar.kernel.memory.Wme;
import org.jsoar.kernel.symbols.SymbolFactory;
import org.jsoar.util.adaptables.Adaptables;
import org.jsoar.util.commands.SoarCommands;
import org.jsoar.util.events.SoarEvent;
import org.jsoar.util.events.SoarEventListener;
import us.hiai.agents.XPlaneAgent;
import us.hiai.data.FlightData;
import us.hiai.xplane.XPlaneConnector;

import javax.sound.sampled.*;
import java.io.*;
import java.util.Iterator;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;

import static us.hiai.xplane.XPlaneConnector.getFlightData;

/**
 * Created by icislab on 10/19/2016.
 */
public class DroneAgent extends XPlaneAgent
{

    private SymbolFactory syms;
    Agent sagt = getAgent();
    InputBuilder builder;
    double batteryLevel = 0.0;
    double heading = 0.0;
    double pitch = 0.0;
    boolean allEnginesOK = true;
    DecisionCycle decisionCycle;
    private boolean wheelBrakesON;
    private boolean airBrakesON;
    private boolean reversersON;
    private java.lang.String realTime;
    private PipedReader filterOutput;

    @Override
    public java.lang.String name() {
        return "DroneAgent";
    }

    @Override
    public boolean runOnStartup() {
        return true;
    }

    @Override
    public void start()
    {

        sagt = getAgent();

        // uncomment below to see the trace of SOAR execution.
        // It is usually lots of text, but it is often useful

//        sagt.getTrace().enableAll();

        decisionCycle = Adaptables.adapt(sagt, DecisionCycle.class);

        PipedWriter agentWriter = new PipedWriter();
        filterOutput = new PipedReader();

        try
        {
            agentWriter.connect(filterOutput);
        }
        catch (IOException ignored) {}

        sagt.setName("Drone");
        sagt.getPrinter().pushWriter(new OutputStreamWriter(System.out));
        sagt.initialize();

        builder = InputBuilder.create(sagt.getInputOutput());
        builder.push("flightdata").markWme("fd").
                add("airspeed", batteryLevel).markWme("as").
                add("lat", heading).markWme("lat").
                add("lon", heading).markWme("lon").
                add("altitude", pitch).markWme("alt").
                add("allEnginesOK", allEnginesOK).markWme("engOK").
                add("wheelbrakesON", wheelBrakesON).markWme("wBrakes").
                add("airbrakesON", airBrakesON).markWme("aBrakes").
                add("reversersON", reversersON).markWme("reverse").
                add("oilPressureEngine1", batteryLevel).markWme("op1").
                add("oilPressureEngine2", batteryLevel).markWme("op2").
                add("oilPressureEngine3", batteryLevel).markWme("op3").
                add("oilPressureEngine4", batteryLevel).markWme("op4").
                add("oilPressureEngine5", batteryLevel).markWme("op5").
                add("oilPressureEngine6", batteryLevel).markWme("op6").
                add("oilPressureEngine7", batteryLevel).markWme("op7").
                add("oilPressureEngine8", batteryLevel).markWme("op8").
                add("oilPressureGreenLo", batteryLevel).markWme("oGrLo").
                add("currentTime", batteryLevel).markWme("cT");


        syms = sagt.getSymbols();

//        printWme(builder.getWme("fd"));

        try
        {
            String pathToSoar = "/home/dgries/Desktop/Daniel_Griessler_Internship_Files/Translator_Source_Code/lvca/code/SoarToUPPAALTranslator/src/main/Soar/TestXPlaneDrone.soar".replace("/", File.separator);
            SoarCommands.source(sagt.getInterpreter(), pathToSoar);
            System.out.println("There are now " + sagt.getProductions().getProductionCount() + " productions loaded");
        }
        catch (SoarException e) {
            e.printStackTrace();
        }

        Executors.newSingleThreadExecutor().submit(this::pushFlightData);
    }

    private void pushFlightData()
    {
        while (!decisionCycle.isHalted()) {
            FlightData data = getFlightData();

            for (int i = 0; i < data.oilPressurePerEngine.length; i++) {
                System.out.printf("\t\tOilPressure%d: %f", i + 1, data.oilPressurePerEngine[i]);
            }
            System.out.println("\t\tOilGreenLo: " + data.oilPressureGreenLo + "\t\tCurrentTime: " + data.currentTime + "\t\tCurrentSpeed: " + data.airspeed);

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


            // uncomment if you want to see the productions that matched

            MatchSet matchSet = sagt.getMatchSet();

            if (matchSet.getEntries().size() > 1) {
                System.out.println("Found matching productions!!");
                for (MatchSetEntry mse : matchSet.getEntries()) {
                    System.out.println("Production:" + mse.getProduction());
                }
            }

            sagt.runFor(1, RunType.DECISIONS);

            try {
                Thread.sleep(500);
            } catch (InterruptedException er) {}
        }
        sagt.dispose();
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