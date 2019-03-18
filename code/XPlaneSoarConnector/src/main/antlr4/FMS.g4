grammar FMS;

@header {
package antlr4;
}


fms : header waypoint* ;

// Grammar of Flight Plan in X-Plane
// Based on https://flightplandatabase.com/dev/specification
header : builder version Int_constant number_of_non_user_defined_waypoints ;
builder : 'I' | 'A' ;
version : Int_constant 'version' ;
number_of_non_user_defined_waypoints : Int_constant ;

waypoint: type (Sym_constant | '-'+) altitude latitude longitude ;
type: Int_constant;
altitude : Int_constant | Float_constant ;
latitude : Float_constant ;
longitude : Float_constant ;

// Types of constants
Sym_constant : [a-zA-Z] [a-zA-Z0-9-_]* ;
Int_constant : [0-9]+ ;
Float_constant : '-'? [0-9]+ '.' [0-9]+ ;
WS : [ \t\n\r]+ -> skip;