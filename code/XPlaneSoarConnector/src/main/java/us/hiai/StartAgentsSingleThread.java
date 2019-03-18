package us.hiai;

import us.hiai.agents.DroneAgentSingleThread;

/**
 *
 * Created by mstafford on 10/3/2016.
 */
public class StartAgentsSingleThread
{

    public static void main(String[] args) {
        DroneAgentSingleThread da = new DroneAgentSingleThread();
        da.start();
    }

}
