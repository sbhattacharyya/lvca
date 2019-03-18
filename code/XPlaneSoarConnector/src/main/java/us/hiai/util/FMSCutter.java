package us.hiai.util;

import antlr4.FMSBaseVisitor;
import antlr4.FMSParser;

/**
 * Extracts waypoints and returns a doubly linked list of waypoints or sentinel waypoint
 * Created by Daniel Griessler Sprint 2019
 */
public class FMSCutter extends FMSBaseVisitor<FlightPlan> {

    FlightPlan fp = new FlightPlan();

    FMSCutter(FMSParser.FmsContext ctx) {
        ctx.accept(this);
    }

    @Override public FlightPlan visitBuilder(FMSParser.BuilderContext ctx) {
        fp.builder = ctx.getText().charAt(0);
        return null;
    }

    @Override public FlightPlan visitVersion(FMSParser.VersionContext ctx) {
        fp.versionNumber = Integer.parseInt(ctx.Int_constant().getText());
        return null;
    }

    @Override public FlightPlan visitNumber_of_non_user_defined_waypoints(FMSParser.Number_of_non_user_defined_waypointsContext ctx) {
        fp.numberOfUserDefinedWaypoints = Integer.parseInt(ctx.Int_constant().getText());
        return null;
    }

    @Override public FlightPlan visitWaypoint(FMSParser.WaypointContext ctx) {
        if (ctx.Sym_constant() != null) {
            fp.addWaypoint(new WaypointNode(ctx.Sym_constant().getText()));
            ctx.type().accept(this);
            ctx.altitude().accept(this);
            ctx.latitude().accept(this);
            ctx.longitude().accept(this);
        }
        return null;
    }

    @Override public FlightPlan visitType(FMSParser.TypeContext ctx) {
        fp.waypoints.getLast().setType(Integer.parseInt(ctx.Int_constant().getText()));
        return null;
    }

    @Override public FlightPlan visitAltitude(FMSParser.AltitudeContext ctx) {
        float altitude;
        if (ctx.Int_constant() != null) {
            altitude = Float.parseFloat(ctx.Int_constant().getText());
        } else {
            altitude = Float.parseFloat(ctx.Float_constant().getText());
        }
        fp.waypoints.getLast().setAltitude(altitude);
        return null;
    }

    @Override public FlightPlan visitLatitude(FMSParser.LatitudeContext ctx) {
        fp.waypoints.getLast().setLatitude(Float.parseFloat(ctx.Float_constant().getText()));
        return null;
    }

    @Override public FlightPlan visitLongitude(FMSParser.LongitudeContext ctx) {
        fp.waypoints.getLast().setLongitude(Float.parseFloat(ctx.Float_constant().getText()));
        return null;
    }
}
