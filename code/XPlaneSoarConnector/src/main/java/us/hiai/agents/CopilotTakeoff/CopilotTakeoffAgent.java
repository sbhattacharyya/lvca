package us.hiai.agents.CopilotTakeoff;

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

import javax.sound.sampled.*;
import java.io.*;
import java.util.Iterator;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

import static us.hiai.xplane.XPlaneConnector.getFlightData;

/**
 * Created by icislab on 10/19/2016.
 */
public class CopilotTakeoffAgent extends XPlaneAgent
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
        return "Copilot_Takeoff";
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
            //Executors.newSingleThreadExecutor().submit(() -> filterSpeech(filterOutput));
        }
        catch (IOException ignored) {}

        sagt.setName("ReinforcementLearningAgent");
        sagt.getPrinter().pushWriter(new OutputStreamWriter(System.out));
//        sagt.getPrinter().pushWriter(agentWriter);
        sagt.initialize();
//        sagt.getEvents().addListener(FlightData.class, new CopilotEventListener(syms, builder, sagt, 100));

        builder = InputBuilder.create(sagt.getInputOutput());
        builder.push("flightdata").markWme("fd").
                add("airspeed", batteryLevel).markWme("as").
                add("lat", heading).markWme("lat").
                add("lon", heading).markWme("lon").
                add("altitude", pitch).markWme("alt").
                add("allEnginesOK", allEnginesOK).markWme("engOK").
                add("wheelbrakesON", wheelBrakesON).markWme("wBrakes").
                add("airbrakesON", airBrakesON).markWme("aBrakes").
                add("reversersON", reversersON).markWme("reverse");


        syms = sagt.getSymbols();

//        printWme(builder.getWme("fd"));

        try
        {
            String pathToSoar = "src/main/soar/agents/CopilotTakeoff.soar".replace("/", File.separator);
            SoarCommands.source(sagt.getInterpreter(), pathToSoar);
            System.out.println("There are now " + sagt.getProductions().getProductionCount() + " productions loaded");
        }
        catch (SoarException e) {
            e.printStackTrace();
        }

        sagt.getEvents().addListener(OutputEvent.class,
                soarEvent ->
                {
                    // Contains details of the OutputEvent
                    Executors.newSingleThreadExecutor().execute(() ->
                            {
                                // Start new thread
                                CopilotTakeoffAgent.this.speakWmes((OutputEvent) soarEvent);  // Say all WMEs with the "spoken" attribute
                            });
                });


        Executors.newSingleThreadScheduledExecutor().scheduleAtFixedRate(pushFlightData(), 0, 150, TimeUnit.MILLISECONDS);
    }

    private void speakWmes(OutputEvent soarEvent)
    {
        Iterator<Wme> wmes = soarEvent.getWmes();
        while (wmes.hasNext())
        {
            Wme nextWME = wmes.next();
            if (nextWME.getAttribute().asString().getValue().equals("spoken"))
            {
                String txt = nextWME.getValue().asString().getValue();
                speakText(txt);

                QMemory memory = DefaultQMemory.create();
                SoarQMemoryAdapter adapter = SoarQMemoryAdapter.attach(sagt, memory);
                memory.setString("io.output-link.spoken", "");
            }
        }
    }

    private Runnable pushFlightData()
    {
        return () ->
        {
            FlightData data = getFlightData();

            System.out.println("\t\t\t\tSpeed: "+data.airspeed);


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


            // uncomment if you want to see the productions that matched

            MatchSet matchSet = sagt.getMatchSet();

            if ( matchSet.getEntries().size() > 1)
            {
                System.out.println("Found matching productions!!");
                for (MatchSetEntry mse : matchSet.getEntries())
                {
                    System.out.println("Production:" + mse.getProduction());
                }
            }

            sagt.runFor(1, RunType.DECISIONS);
        };
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