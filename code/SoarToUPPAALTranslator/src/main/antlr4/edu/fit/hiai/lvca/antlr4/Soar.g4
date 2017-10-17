grammar Soar;

soar: soar_production+ ;

// Grammar of Soar productions
soar_production : ('sp'|'gp') '{' sym_constant Documentation? flags? condition_side '-->' action_side '}' ;
Documentation : '"""' ~["]* '"""' ;
flags : ':' ('o-support' | 'i-support' | 'chunk' | 'default' | 'template' ) ;

// Grammar for Condition Side
condition_side : state_imp_cond cond* ;
state_imp_cond : '(' (STATE | 'impasse') id_test? attr_value_tests+ ')' ;
cond : positive_cond | ( ('-') positive_cond ) ;
positive_cond : conds_for_one_id | ('{' cond+ '}') ;
conds_for_one_id : '(' (STATE | 'impasse')? id_test attr_value_tests+ ')';
id_test : test ;
attr_value_tests : '-'? '^' attr_test ('.' attr_test)* value_test* ;
attr_test : test ;
value_test : ( test '+'? ) | ( conds_for_one_id '+'? ) ;

test : conjunctive_test | simple_test | multi_value_test ;
conjunctive_test : '{' simple_test+ '}' ;
simple_test : disjunction_test | relational_test ;
multi_value_test : '[' Int_constant+ ']' ;
disjunction_test : '<<' constant+ '>>' ;
relational_test : relation? single_test ;
relation : '<>' | '<' | '>' | '<=' | '>=' | '==' | '<=>' | '=';
single_test : variable | constant ;
variable : '<' sym_constant '>' ;
constant : sym_constant | Int_constant | Float_constant | Print_string ;

// Grammar for Action Side
action_side : (action  | func_call | print)* ;
action : ( '(' variable attr_value_make+ ')' );
print : ( '(' 'write ' ( Print_string | variable | '(crlf)')+ ')' )+ ;
Print_string : '|' ~[|]* '|' ;
func_call : '(' func_name value* ')' ;
func_name : sym_constant | '+' | '-' | '*' | '/' ;
value : constant | func_call | variable ;
attr_value_make : '^' variable_or_sym_constant ( '.' variable_or_sym_constant )* value_make ;
variable_or_sym_constant : variable | sym_constant ;
value_make : value pref_specifier* ;
pref_specifier : ( unary_pref ','? ) | ( unary_or_binary_pref ','? ) | unary_or_binary_pref value ','? ;
unary_pref : '+' | '-' | '!' | '~' | '@' ;
unary_or_binary_pref : '>' | '=' | '<' | '&' ;

sym_constant: Sym_constant | STATE ;

// Types of constants
STATE: 'state' ;
Sym_constant : [a-zA-Z] [a-zA-Z0-9-_*]* ;
Int_constant : [0-9]+ ;
Float_constant : [0-9]+ '.' [0-9]+ ;
WS : [ \t\r\n]+ -> skip ;
COMMENT : '#' ~[\r\n]* -> skip ;