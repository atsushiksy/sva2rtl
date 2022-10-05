%{
/***************************************************************************
 *
 *  Verilog Parser (prep-file for btyacc)
 *
 *  Author: Atsushi Kasuya
 *
 *
 *   Copyright (C) 2011 Atsushi Kasuya
 *
 *  Coding note:
 *    This source is parsed by several perl script along with other .data 
 *      files to conform the compiler code
 *    
 *    #INCLUDE is handled by gen_parser.pl. But this must be a non-nested file
 *    #BEGIN <name>  to #END is extracted as syntax file under syntax 
 *      directory, and eventually used in spec/language.spec
 *    This file is parsed by parse_yacc.pl and the following files are
 *      created:
 *        SystemVerilog.y.prep   :  anotated version of this file
 *                                  used to create final .y (yacc input)
 *        SV_token_table.h : Token definition file in part of .y file
 *                             included in this file
 *        SystemVerilog_keyword_table.h : Keyword data table used by lex
 *        SystemVerilog_opertor_lex.h : Lex match code included in .l.pp 
 *    
 *
 *
 *
 *************************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "systemverilog_node.h"
#include "symtab.h"

/* external, internal variable declarations here */
extern int error_flag ;
extern int debug_line_num ;
extern char *input_file_name ;

extern int compile_pass ;
extern int ise_flag ;

extern systemverilog_node *root_node ;

int parsing_assertion = 0 ;

%}

%union {
  systemverilog_node *sv_node ;
}

%token <sv_node> Identifier 
%token <sv_node> Property_Name
%token <sv_node> Sys_identifier   /* $something */
%token <sv_node> Real_number     /* real */
%token <sv_node> Decimal_number   /* number */
%token <sv_node> Hex_number       /* verilog format hex */
%token <sv_node> Octal_number     /* verilog format octal */
%token <sv_node> Binary_number    /* verilog format binary */
%token <sv_node> Unbased_unsized_literal   /*  '0 '1 '[xzXZ] */
%token <sv_node> Unsigned_number   /* unsigned decimal*/
%token <sv_node> String_literal   /* string */

#INCLUDE "SV_token_table.h" 

%type <sv_node> '\''

#BEGIN precedence_table
%right '=' '+=' '-=' '*=' '/=' '%=' '&=' '^=' '|=' '<<=' '>>=' '<<<=' '>>>=' ':=' ':/'
%right '->'
%right '?' ':'
%left '||'
%left '&&'
%left '|'
%left '^' '~^' '^~'
%left '&'
%left '==' '!=' '===' '!==' '=?=' '!?='
%left '<=' '>' '<' '>=' 'inside' 
%left '+' '-'
%left '*' '/' '%'
%left '**'
/* unary (+ - etc. are not declared here) */
%right '~&' '~|' '++' '--'
%left '::' '.'

#END

%start verilog_src

%%


verilog_src: 
  <<null_root>>
  |
  source_file
  <<set_root>>
  ;

source_file:
  description
  |
  source_file description
  <<D1_next_eq_D2>>
  ;


number:
  integral_number
  |
  Real_number
  ;

integral_number:
  Unsigned_number
  <<integral_number>>
  |
  Decimal_number
  <<integral_number>>
  |
  Octal_number
  <<integral_number>>
  |
  Binary_number
  <<integral_number>>
  |
  Hex_number
  <<integral_number>>
  ;

real_or_realtime:
  'real'
  |
  'realtime'
  ;

attribute_list_opt:
  /* empty */
  |
  attribute_instance_list
  ;

attribute_instance_list:
  '(*' '*)' 
  |
  '(*' attribute_list '*)' 
  |
  attribute_instance_list '(*' '*)' 
  |
  attribute_instance_list '(*' attribute_list '*)'
  ;

attribute_list:
  attribute_list ',' attribute
  |
  attribute
  ;


attribute:
  Identifier
  |
  Identifier '=' expression
  ;

block_item_decl:
  attribute_list_opt 'reg'
    primitive_type_opt signed_opt range
    register_variable_list ';'
  |
  attribute_list_opt 'reg'
    primitive_type_opt signed_opt
    register_variable_list ';'
  |
  attribute_list_opt 'integer' register_variable_list ';'
  |
  attribute_list_opt 'time' register_variable_list ';'
  |
  attribute_list_opt 'real' real_variable_list ';'
  |
  attribute_list_opt 'realtime' real_variable_list ';'
  |
  'event' list_of_identifiers ';'
  |
  'parameter' parameter_assign_decl ';'
  |
  'localparam' localparam_assign_decl ';'
  ;

block_item_decls:
  block_item_decl
  |
  block_item_decls block_item_decl
  <<D1_next_eq_D2>>
  ;

block_item_decls_opt:
  /* empty */
  |
  block_item_decls
  ;

case_item:
  expression_list_proper ':' statement_or_null
  |
  'default' ':' statement_or_null
  |
  'default'  statement_or_null
  ;

case_items:
  case_items case_item
  <<D1_next_eq_D2>>
  |
  case_item
  ;

charge_strength:
  '(' 'small' ')'
  |
  '(' 'medium' ')'
  |
  '(' 'large' ')'
  ;

charge_strength_opt:
  /* empty */
  |
  charge_strength
  ;

defparam_assign:
  hierarchy_identifier '=' expression
  ;

defparam_assign_list:
  defparam_assign
  |
  range defparam_assign
  |
  defparam_assign_list ',' defparam_assign
  ;

delay1:
  '#' delay_value_simple
  |
  '#' '(' delay_value ')'
  ;

delay3:
  '#' delay_value_simple
  |
  '#' '(' delay_value ')'
  |
  '#' '(' delay_value ',' delay_value ')'
  |
  '#' '(' delay_value ',' delay_value ',' delay_value ')'
  ;

delay3_opt:
  /* empty */
  |
  delay3
  ;

delay_value_list:
  delay_value
  |
  delay_value_list ',' delay_value
  ;

delay_value:
  expression
  |
  expression ':' expression ':' expression
  ;

delay_value_simple:
  Unsigned_number
  |
  Decimal_number  
  |
  /*
  REALTIME
  |
  */
  Identifier
  ;

description:
  module
  /*
  |
  udp_primitive
  |
  config_declaration
  |
  nature_declaration
  |
  discipline_declaration
  ;
  */

drive_strength:
  '(' dr_strength0 ',' dr_strength1 ')'
  |
  '(' dr_strength1 ',' dr_strength0 ')'
  |
  '(' dr_strength0 ',' 'highz1' ')'
  |
  '(' dr_strength1 ',' 'highz0' ')'
  |
  '(' 'highz1' ',' dr_strength0 ')'
  |
  '(' 'highz0' ',' dr_strength1 ')'
  ;

drive_strength_opt:
  /* empty */
  |
  drive_strength
  ;

dr_strength0:
  'suppuy0' 
  |
  'strong0' 
  |
  'pull0'   
  |
  'weak0'   
  ;

dr_strength1:
  'supply1' 
  |
  'strong1'
  |
  'pull1'
  |
  'weak1'
  ;

event_control:
  '@' hierarchy_identifier
  |
  '@' '(' event_expression_list ')'
  ;

event_expression_list:
  event_expression
  |
  event_expression_list 'or' event_expression
  |
  event_expression_list ',' event_expression
  ;

event_expression:
  'posedge' expression
  <<posedge_event>>
  |
  'negedge' expression
  <<negedge_event>>
  |
  expression
  ;

branch_probe_expression:
  Identifier '(' Identifier ',' Identifier ')'
  |
  Identifier '(' Identifier ')'
  ;


/*
  '+' expr_primary 
  |
  '-' expr_primary
  <<unary_minus>> 
  |
  '~' expr_primary 
  |
 '&' expr_primary 
  |
 '!' expr_primary 
  |
 '|' expr_primary 
  |
  '^' expr_primary
  |
  '~' '&' expr_primary
  |
  '~' '|' expr_primary 
  |
  '~' '^' expr_primary 
  |
  '~&' expr_primary 
  |
  '~|' expr_primary 
  |
  '~^' expr_primary 
  |
  expression '^' expression
  |
  expression '**' expression
  |
  expression '*' expression
  |
  expression '/' expression
  |
  expression '%' expression
  |
  expression '+' expression
  |
  expression '-' expression
  |
  expression '&' expression
  |
  expression '|' expression
  |
  expression '~&' expression
  |
  expression '~|' expression
  |
  expression '~^' expression
  |
  expression '<' expression
  |
  expression '>' expression
  |
  expression '<<' expression
  |
  expression '<<<' expression
  |
  expression '>>' expression
  |
  expression '>>>' expression
  |
  expression '==' expression
  |
  expression '===' expression
  |
  expression '<=' expression
  |
  expression '>=' expression
  |
  expression '!=' expression
  |
  expression '!==' expression
  |
  expression '||' expression
  |
  expression '&&' expression
  |
  */


expr_mintypmax:
  expression
  |
  expression ':' expression ':' expression
  ;


expression_list_with_nuls:
  /* empty */
  |
  expression_list_with_nuls ',' expression
  |
  expression
  |
  expression_list_with_nuls ','
  ;

expression_list_proper:
  expression_list_proper ',' expression
  |
  expression
  ;

expr_primary:
  number
  |
  /*
  REALTIME
  |
  */
  String_literal
  |
  Sys_identifier
  |
  hierarchy_identifier
  |
  hierarchy_identifier '(' expression_list_proper ')'
  |
  Sys_identifier '(' expression_list_proper ')'
  <<system_function_call>>

  /* omit embedded functions
  |
  'acos' '(' expression ')'
  |
  'acosh' '(' expression ')'
  |
  'asin' '(' expression ')'
  |
  'asinh' '(' expression ')'
  |
  'atan' '(' expression ')'
  |
  'atanh' '(' expression ')'
  |
  'atan2' '(' expression ',' expression ')'
  |
  'ceil' '(' expression ')'
  |
  'cos' '(' expression ')'
  |
  'cosh' '(' expression ')'
  |
  'exp' '(' expression ')'
  |
  'floor' '(' expression ')'
  |
  'hypot' '(' expression ',' expression ')'
  |
  'ln' '(' expression ')'
  |
  'log' '(' expression ')'
  |
  '**' '(' expression ',' expression ')'
  |
  'sin' '(' expression ')'
  |
  'sinh' '(' expression ')'
  |
  'sqrt' '(' expression ')'
  |
  'tan' '(' expression ')'
  |
  'tanh' '(' expression ')'
  |
  'abs' '(' expression ')'
  |
  'max' '(' expression ',' expression ')'
  |
  'min' '(' expression ',' expression ')'
  */

  /* Parenthesized expressions are primaries. */
  |
  '(' expr_mintypmax ')'
  /* Various kinds of concatenation expressions. */
  |
  '{' expression_list_proper '}'
  |
  '{' expression '{' expression_list_proper '}' '}'
  ;

  /* A function_item_list borrows the task_port_item run to match
     declarations of ports. We check later to make sure there are no
     output or inout ports actually used. */
function_item_list:
  function_item
  |
  function_item_list function_item
  ;

function_item:
  task_port_item
  |
  block_item_decl
  ;

 /* A gate_instance is a module instantiation or a built in part
     type. In any case, the gate has a set of connections to ports. */
gate_instance:
  Identifier '(' expression_list_with_nuls ')'
  |
  Identifier range '(' expression_list_with_nuls ')'
  |
  '(' expression_list_with_nuls ')'
  |
  /* Degenerate modules can have no ports. */
  Identifier range
  |
  /* Modules can also take ports by port-name expressions. */
  Identifier '(' port_name_list ')'
  |
  Identifier range '(' port_name_list ')'
  ;

gate_instance_list:
  gate_instance_list ',' gate_instance
  |
  gate_instance
  ;

gatetype:
  'and'
  |
  'nand' 
  |
  'or'
  |
  '~|'
  |
  'xor'
  |
  'xnor'
  |
  'buf'
  |
  'bufif0'
  |
  'bufif1'
  |
  'not'
  |
  'notif0'
  |
  'notif1'
  ;

switchtype:
  'nmos'
  |
  'rnmos'
  |
  'pmos'
  |
  'rpmos'
  |
  'cmos'
  |
  'rcmos'
  |
  'tran'
  |
  'rtran'
  |
  'tranif0' 
  |
  'tranif1'
  |
  'rtranif0'
  |
  'rtranif1' 
  ;

hierarchy_identifier:
  Identifier
  <<identifier>>
  |
  hierarchy_identifier '.' Identifier
  <<hieracy_identifier>>
  |
  hierarchy_identifier '[' expression ']'
  <<identifier_singlesell>>
  |
  hierarchy_identifier '[' expression ':' expression ']'
  <<identifier_rangesell>>
  /*
  |
  hierarchy_identifier '[' expression '+:' expression ']'
  |
  hierarchy_identifier '[' expression '-:' expression ']'
  */
  ;

list_of_identifiers:
  Identifier
  |
  list_of_identifiers ',' Identifier
  ;

port_identifire:
  Identifier
  <<port_identifire>>
  |
  Identifier '=' expression
  <<port_idenfire_assign>>
  ;
  
list_of_port_identifiers:
  port_identifire
  |
  list_of_port_identifiers ',' port_identifire
  <<list_of_port_identifiers>>
  ;

list_of_ports_opt:
  /* empty */
  |
  list_of_ports
  ;
  
list_of_ports:
  port
  |
  list_of_ports ',' port
  ;

list_of_port_declarations:
  port_declaration
  |
  list_of_port_declarations ',' port_declaration
  |
  list_of_port_declarations ',' Identifier
  |
  list_of_port_declarations ','
  |
  list_of_port_declarations ';'
  ;

port_declaration:
  attribute_list_opt
    'input' net_type_opt signed_opt range_opt Identifier
  <<input_port_declaration>>
  |
  attribute_list_opt
    'inout'  net_type_opt signed_opt range_opt Identifier
  <<inout_port_declaration>>
  |
  attribute_list_opt
    'output' net_type_opt signed_opt range_opt Identifier
  <<output_port_declaration>>
  |
  attribute_list_opt
    'output' var_type signed_opt range_opt Identifier
  <<output_port_declaration>>
  |
  attribute_list_opt
    'output' var_type signed_opt range_opt Identifier '=' expression
  <<output_port_assign_declaration>>
  ;

net_type_opt:
  /* empty */
  |
  net_type
  ;

signed_opt:
  /* empty */
  |
  'signed' 
  ;

lpvalue:
  hierarchy_identifier
  |
  '{' expression_list_proper '}'
  ;

  /* Continuous assignments have a list of individual assignments. */

cont_assign:
  lpvalue '=' expression
  ;

cont_assign_list:
  cont_assign_list ',' cont_assign
  |
  cont_assign
  ;

/*******************************************************/
/* module                                              */
/*******************************************************/

module:
  attribute_list_opt
    module_start
    Identifier
    <<module_begin>>
    module_parameter_port_list_opt
    module_port_list_opt
    module_attribute_foreign
    ';'
    module_item_list_opt
    'endmodule'
    <<module_end>>
  ;

module_start:
  'module'
  /*  A.K. only accept module
  |
  'macromodule' 
  */
  ;

module_attribute_foreign:
  /* empty */
  |
  '(*' Identifier 'integer' Identifier '=' String_literal ';' '*)' 
  ;

module_port_list_opt:
  /* empty */
  <<empty_port_list>>
  |
  '(' list_of_ports_opt ')' 
  <<par_port_list>>
  |
  '(' list_of_port_declarations ')' 
  <<par_port_dcl_list>>
  ;
 

module_parameter_port_list_opt:
  /* empty */
  |
  '#' '(' module_parameter_port_list ')'
  ;

module_parameter_port_list:
  'parameter' parameter_assign
  |
  module_parameter_port_list ',' parameter_assign
  |
  module_parameter_port_list ',' 'parameter' parameter_assign
  ;

module_item:
  attribute_list_opt 
    net_type
    primitive_type_opt 
    signed_opt 
    range_opt
    delay3_opt
    net_variable_list 
    ';'
  <<net_declaration>>
  |
  attribute_list_opt net_type
    primitive_type_opt signed_opt range_opt
    delay3_opt net_decl_assigns ';'
  <<net_assign_declaration>>
  |
  attribute_list_opt net_type
    primitive_type_opt signed_opt
    drive_strength net_decl_assigns ';'
  <<net_st_assign_declaration>>
  |
  'trireg' 
    charge_strength_opt 
    range_opt 
    delay3_opt 
    list_of_identifiers 
    ';'
  <<trireg_dcl>>
  |
  port_type 
    signed_opt 
    range_opt 
    delay3_opt 
    list_of_identifiers 
    ';'
  <<port_dcl_a>>
  |
  port_type
    net_type
    signed_opt 
    range_opt 
    list_of_identifiers 
    ';'
  <<port_dcl_b>>    
  |
  'output'
    var_type
    signed_opt 
    range_opt 
    list_of_port_identifiers
    ';'
  <<port_dcl_c>>
  |
  'input' 
    var_type 
    signed_opt 
    range_opt 
    list_of_identifiers 
    ';'
  <<port_dcl_d>>
  |
  'inout' 
    var_type 
    signed_opt 
    range_opt 
    list_of_identifiers 
    ';'
  <<port_dcl_e>>
  |
  block_item_decl
  |
  'defparam' defparam_assign_list ';'
  |
  attribute_list_opt gatetype gate_instance_list ';'
  |
  attribute_list_opt gatetype delay3 gate_instance_list ';'
  |
  attribute_list_opt gatetype drive_strength gate_instance_list ';'
  |
   attribute_list_opt gatetype drive_strength delay3 gate_instance_list ';'
  |
  attribute_list_opt switchtype gate_instance_list ';'
  |
  attribute_list_opt switchtype delay3 gate_instance_list ';'
  |
  'pullup' gate_instance_list ';'
  |
  'pulldown' gate_instance_list ';'
  |
  'pullup' '(' dr_strength1 ')' gate_instance_list ';'
  |
  'pullup' '(' dr_strength1 ',' dr_strength0 ')' gate_instance_list ';'
  |
  'pullup' '(' dr_strength0 ',' dr_strength1 ')' gate_instance_list ';'
  |
  'pulldown' '(' dr_strength0 ')' gate_instance_list ';'
  |
  'pulldown' '(' dr_strength1 ',' dr_strength0 ')' gate_instance_list ';'
  |
  'pulldown' '(' dr_strength0 ',' dr_strength1 ')' gate_instance_list ';'
  |
  attribute_list_opt
    Identifier parameter_value_opt gate_instance_list ';'
  |
  'assign' drive_strength_opt delay3_opt cont_assign_list ';'
  |
  /* Always and initial items are behavioral processes. */
  attribute_list_opt 'always' statement
  |
  attribute_list_opt 'initial' statement
  |
  'task' automatic_opt Identifier ';'
    task_item_list_opt
    statement_or_null
    'endtask'
  |
  'task' automatic_opt Identifier '('
    task_port_decl_list ')' ';'
    block_item_decls_opt
    statement_or_null
    'endtask'
  | 
  'task' automatic_opt Identifier '(' ')' ';'
    block_item_decls_opt
    statement_or_null
    'endtask'
  |
  'function' automatic_opt function_range_or_type_opt Identifier ';'
    function_item_list statement
    'endfunction'
  |
  'function' automatic_opt function_range_or_type_opt Identifier
    '(' task_port_decl_list ')' ';'
    block_item_decls_opt
    statement
    'endfunction'
  |
  /*  A.K. generate is not supported 
  |
  'generate' module_item_list_opt 'endgenerate'
  |
  'genvar' list_of_identifiers ';'
  |
  'for' '(' Identifier '=' expression ';'
    expression ';'
    Identifier '=' expression ')'
    generate_block
  |
  generate_if
    generate_block_opt
    'else'
    generate_block
  |
  generate_if
    generate_block_opt less_than_K_else
  |
  'case' '(' expression ')'
    generate_case_items
    'endcase'
  |
  'generate' 'begin' module_item_list_opt 'end' 'endgenerate'
  |
  'generate' 'begin' ':' Identifier 
  |
  'specify' 'endspecify'
  |
  'specify' specify_item_list 'endspecify'
  |
  */
  /****************************************************/
  /*  A.K. Extension to include assertions            */
  /****************************************************/
  concurrent_assertion_item 
  |  
  concurrent_assertion_item_declaration  
  ;

automatic_opt:
  /* empty */
  |
  'automatic'
  ;

generate_if:
  'if' '(' expression ')' 
  ;

generate_case_items:
  generate_case_items generate_case_item
  |
  generate_case_item
  ;

generate_case_item:
  expression_list_proper ':' generate_block_opt
  |
  'default' ':' generate_block_opt
  ;

module_item_list:
  module_item_list module_item
  <<D1_next_eq_D2>>
  |
  module_item
  ;

module_item_list_opt:
  /* empty */
  |  
  module_item_list
  ;

  /* A generate block is the thing within a generate scheme. It may be
     a single module item, an anonymous block of module items, or a
     named module item. In all cases, the meat is in the module items
     inside, and the processing is done by the module_item rules. We
     only need to take note here of the scope name, if any. */

generate_block:
  module_item
  |
  'begin' module_item_list_opt 'end'
  |
  'begin' ':' Identifier module_item_list_opt 'end'
  ;

generate_block_opt: 
  ';'
  |
  generate_block 
  ;


  /* A net declaration assignment allows the programmer to combine the
     net declaration and the continuous assignment into a single
     statement.

     Note that the continuous assignment statement is generated as a
     side effect, and all I pass up is the name of the l-value. */

net_decl_assign:
  Identifier '=' expression
  <<net_decl_assign>>
  ;

net_decl_assigns:
  net_decl_assigns ',' net_decl_assign
  |
  net_decl_assign
  ;

primitive_type:
  'logic' 
  |
  'bool' 
  |
  'real' 
  ;

primitive_type_opt:
  /* empty */
  |
  primitive_type
  ;

net_type:
  'wire'
  |
  'tri'
  |
  'tri1'
  <<tri_wire>>
  |
  'supply0'
  |
  'wand'
  |
  'triand'
  |
  'tri0'
  <<tri_wire>>
  |
  'supply1'
  |
  'wor'
  |
  'trior'
  |
  'wone'
  |
  'uwire'
  ;

var_type:
  'reg'
  ;

parameter_assign_decl:
  parameter_assign_list
  |
  range
    parameter_assign_list
  |
  'signed' range
    parameter_assign_list
  |
  'integer'
     parameter_assign_list
  |
  'time'
    parameter_assign_list
  |
  real_or_realtime
    parameter_assign_list
  |
  'string' parameter_assign_list
  <<string_parameter_assign_list>>
  ;

parameter_assign_list:
  parameter_assign
  |
  parameter_assign_list ',' parameter_assign
  ;

parameter_assign:
  Identifier '=' expression parameter_value_ranges_opt
  <<parameter_assign>>
  ;

parameter_value_ranges_opt:
  /* empty */
  |
  parameter_value_ranges
  ;

parameter_value_ranges:
  parameter_value_ranges parameter_value_range
  |
  parameter_value_range
  ;

parameter_value_range:
  from_exclude '[' value_range_expression ':' value_range_expression ']'
  |
  from_exclude '[' value_range_expression ':' value_range_expression ')'
  |
  from_exclude '(' value_range_expression ':' value_range_expression ']'
  |
  from_exclude '(' value_range_expression ':' value_range_expression ')'
  |
  'exclude' expression
  ;

value_range_expression:
  expression 
  | 
  'inf' 
  | 
  '+' 'inf' 
  | 
  '-' 'inf' 
  ;

from_exclude: 
  'from' 
  |
  'exclude' 
  ;

  /* Localparam assignments and assignment lists are broken into
     separate BNF so that I can call slightly different parameter
     handling code. They parse the same as parameters, they just
     behave differently when someone tries to override them. */

localparam_assign:
  Identifier '=' expression
  <<localparam_assign>>
  ;

localparam_assign_decl:
  localparam_assign_list
  |
   range
    localparam_assign_list
  |
  'signed' range
    localparam_assign_list
  |
  'integer'
    localparam_assign_list
  |
   'time'
    localparam_assign_list
  |
  real_or_realtime
    localparam_assign_list
  ;

localparam_assign_list:
  localparam_assign
  |
  localparam_assign_list ',' localparam_assign
  ;

  /* The parameters of a module instance can be overridden by writing
     a list of expressions in a syntax much like a delay list. (The
     difference being the list can have any length.) The pform that
     attaches the expression list to the module checks that the
     expressions are constant.

     Although the BNF in IEEE1364-1995 implies that parameter value
     lists must be in parentheses, in practice most compilers will
     accept simple expressions outside of parentheses if there is only
     one value, so I'll accept simple numbers here.

     The parameter value by name syntax is OVI enhancement BTF-B06 as
     approved by WG1364 on 6/28/1998. */
parameter_value_opt:
  /* empty */
  |
  '#' '(' expression_list_with_nuls ')'
  |
  '#' '(' parameter_value_byname_list ')'
  |
  '#' Decimal_number

  ;

parameter_value_byname:
  '.' Identifier '(' expression ')'
  |
  '.' Identifier '(' ')'
  ;

parameter_value_byname_list:
  parameter_value_byname
  |
  parameter_value_byname_list ',' parameter_value_byname
  ;


port:
  port_reference
  ;
  /*
  |
  '.' Identifier '(' port_reference ')'
  |
  '{' port_reference_list '}'
  |
  '.' Identifier '(' '{' port_reference_list '}' ')'
  ;
  */
  
port_reference:
  Identifier
  <<port_ref>>
  |
  Identifier '[' expression ':' expression ']'
  <<port_ref_range2>>
  |
  Identifier '[' expression ']'
  <<port_ref_range>>
  ;

/*
port_reference_list:
  port_reference
  |
  port_reference_list ',' port_reference
  ;
*/

  /* The port_name rule is used with a module is being *instantiated*,
     and not when it is being declared. See the port rule if you are
     looking for the ports of a module declaration. */
port_name:
  '.' Identifier '(' expression ')'
  |
  '.' Identifier '(' ')'
  ;

port_name_list:
  port_name_list ',' port_name
  |
  port_name
  ;

port_type:
  'input' 
  |
  'output'
  |
  'inout'
  ;

range:
 '[' expression ':' expression ']'
  ;

range_opt:
  /* empty */
  |  
  range
  ;

dimensions_opt:
  /* empty */
  |
  dimensions 
  ;

dimensions:
  '[' expression ':' expression ']'
  |
  dimensions '[' expression ':' expression ']'
  ;

  /* This is used to express the return type of a function. */
function_range_or_type_opt:
  /* empty */
  |
  range
  |
  'signed' range
  |
  'integer'
  |
  'real'
  |
  'realtime'
  |
  'time'
  ;

  /* The register_variable rule is matched only when I am parsing
     variables in a "reg" definition. I therefore know that I am
     creating registers and I do not need to let the containing rule
     handle it. The register variable list simply packs them together
     so that bit ranges can be assigned. */
register_variable:
  Identifier dimensions_opt
  |
  Identifier '=' expression
  ;

register_variable_list:
  register_variable
  |
  register_variable_list ',' register_variable
  ;

real_variable:
  Identifier dimensions_opt
  |
  Identifier '=' expression
  ;

real_variable_list:
  real_variable
  |
  real_variable_list ',' real_variable
  ;

net_variable:
  Identifier dimensions_opt
  <<net_variable>>
  ;

net_variable_list:
  net_variable
  |
  net_variable_list ',' net_variable
  ;

specify_item:
  'specparam' specparam_list ';'
  |
  specify_simple_path_decl ';'
  |
  specify_edge_path_decl ';'
  |
  'if' '(' expression ')' specify_simple_path_decl ';'
  |
  'if' '(' expression ')' specify_edge_path_decl ';'
  |
  'ifnone' specify_simple_path_decl ';'
  |
  'ifnone' specify_edge_path_decl ';'

  /*
  |
  K_Sfullskew '(' spec_reference_event ',' spec_reference_event
	  ',' delay_value ',' delay_value spec_notifier_opt ')' ';'
  |
  K_Shold '(' spec_reference_event ',' spec_reference_event
	  ',' delay_value spec_notifier_opt ')' ';'
  |
  K_Snochange '(' spec_reference_event ',' spec_reference_event
	  ',' delay_value ',' delay_value spec_notifier_opt ')' ';'
  |
  K_Speriod '(' spec_reference_event ',' delay_value
	  spec_notifier_opt ')' ';'
  |
  K_Srecovery '(' spec_reference_event ',' spec_reference_event
	  ',' delay_value spec_notifier_opt ')' ';'
  |
  K_Srecrem '(' spec_reference_event ',' spec_reference_event
	  ',' delay_value ',' delay_value spec_notifier_opt ')' ';'
  |
  K_Sremoval '(' spec_reference_event ',' spec_reference_event
	  ',' delay_value spec_notifier_opt ')' ';'
  |
  K_Ssetup '(' spec_reference_event ',' spec_reference_event
	  ',' delay_value spec_notifier_opt ')' ';'
  |
  K_Ssetuphold '(' spec_reference_event ',' spec_reference_event
	  ',' delay_value ',' delay_value spec_notifier_opt ')' ';'
  |
  K_Sskew '(' spec_reference_event ',' spec_reference_event
	  ',' delay_value spec_notifier_opt ')' ';'
  |
  K_Stimeskew '(' spec_reference_event ',' spec_reference_event
	  ',' delay_value spec_notifier_opt ')' ';'
  |
  K_Swidth '(' spec_reference_event ',' delay_value ',' expression
	  spec_notifier_opt ')' ';'
  |
  K_Swidth '(' spec_reference_event ',' delay_value ')' ';'
  */

  |
  'pulsestyle_onevent' specify_path_identifiers ';'
  |
  'pulsestyle_ondetect' specify_path_identifiers ';'
  |
  'showcancelled' specify_path_identifiers ';'
  |
  'noshowcancelled' specify_path_identifiers ';'
  ;

specify_item_list:
  specify_item
  |
  specify_item_list specify_item
  ;

specify_edge_path_decl:
  specify_edge_path '=' '(' delay_value_list ')'
  |
  specify_edge_path '=' delay_value_simple
  ;

edge_operator:
  'posedge' 
  |
  'negedge'
  ;

specify_edge_path:
  '('  specify_path_identifiers spec_polarity
    '=>' '(' specify_path_identifiers polarity_operator expression ')' ')'
  |
  '(' edge_operator specify_path_identifiers spec_polarity
    '=>' '(' specify_path_identifiers polarity_operator expression ')' ')'
  |
  '('  specify_path_identifiers spec_polarity
    '*>'  '(' specify_path_identifiers polarity_operator expression ')' ')'
  |
  '(' edge_operator specify_path_identifiers spec_polarity
    '*>' '(' specify_path_identifiers polarity_operator expression ')' ')'
  ;

polarity_operator:
  '+:'
  |
  '-:'
  |
  ':'
  ;

specify_simple_path_decl:
  specify_simple_path '=' '(' delay_value_list ')'
  |
  specify_simple_path '=' delay_value_simple
  ;

specify_simple_path:
  '(' specify_path_identifiers spec_polarity
      '=>' specify_path_identifiers ')'
  |
  '(' specify_path_identifiers spec_polarity
      '*>' specify_path_identifiers ')'
  ;

specify_path_identifiers:
  Identifier
  |
  Identifier '[' expr_primary ']'
  |
  specify_path_identifiers ',' Identifier
  |
  specify_path_identifiers ',' Identifier '[' expr_primary ']'
  ;

specparam:
  Identifier '=' expression
  |
  Identifier '=' expression ':' expression ':' expression
  |
  ps_identifier '=' expression
  |
  ps_identifier '=' '(' expression ',' expression ')'
  ;

specparam_list:
  specparam
  |
  specparam_list ',' specparam
  ;

spec_polarity:
  /* empty */
  |
  '+'  
  |
  '-'  
  ;

spec_reference_event:
  'posedge' expression
  |
  'negedge' expression
  |
  'posedge' expr_primary '&&&' expression
  |
  'negedge' expr_primary '&&&' expression
  |

  /*
  'edge' '[' edge_descriptor_list ']' expr_primary
  |
  'edge' '[' edge_descriptor_list ']' expr_primary '&&&' expression
  |
  */

  expr_primary '&&&' expression
  |
  expr_primary
  ;

  /* The edge_descriptor is detected by the lexor as the various
     2-letter edge sequences that are supported here. For now, we
     don't care what they are, because we do not yet support specify
     edge events. */
/*
edge_descriptor_list:
  edge_descriptor_list ',' K_edge_descriptor
  |
  K_edge_descriptor
  ;
*/

spec_notifier_opt:
  /* empty */
 |
  spec_notifier
 ;

spec_notifier:
  ','
  |
  ','  hierarchy_identifier
  |
  spec_notifier ','
  |
  spec_notifier ',' hierarchy_identifier
  |
  /* How do we match this path? */
  Identifier
  ;

statement:
  'assign' lpvalue '=' expression ';'
  |
  'deassign' lpvalue ';'
  |
  /* Force and release statements are similar to assignments,
     syntactically, but they will be elaborated differently. */
  'force' lpvalue '=' expression ';'
  |
  'release' lpvalue ';'
  |
  'begin' statement_list 'end'
  |
  'begin' ':' Identifier
    block_item_decls_opt
    statement_list 'end'
  |
  'begin' 'end'
  |
  'begin' ':' Identifier 'end'
  |
  'fork' ':' Identifier
     block_item_decls_opt
    statement_list join_keyword
  |
  'fork' join_keyword
  |
  'fork' ':' Identifier join_keyword
  |
  'disable' hierarchy_identifier ';'
  |
  '->' hierarchy_identifier ';'
  |
  'forever' statement
  |
  'fork' statement_list join_keyword
  |
  'repeat' '(' expression ')' statement
  |
  'case' '(' expression ')' case_items 'endcase'
  |
  'casex' '(' expression ')' case_items 'endcase'
  |
  'casez' '(' expression ')' case_items 'endcase'
  |
  'if' '(' expression ')' statement_or_null opt_else_statement
  |
  'for' '(' lpvalue '=' expression ';' expression ';'
    lpvalue '=' expression ')' statement
  |
  'while' '(' expression ')' statement
  |
  // '#' delay_value_simple statement_or_null
  delay1 statement_or_null
  |
  event_control attribute_list_opt statement_or_null
  |
  '@' '*' attribute_list_opt statement_or_null
  |
  '@' '(' '*' ')' attribute_list_opt statement_or_null
  |
  lpvalue '=' expression ';'
  |
  lpvalue '<=' expression ';'
  |
  lpvalue '=' delay1 expression ';'
  |
  lpvalue '<=' delay1 expression ';'
  |
  lpvalue '=' event_control expression ';'
  |
  lpvalue '=' 'repeat' '(' expression ')' event_control expression ';'
  |
  lpvalue '<=' event_control expression ';'
  |
  lpvalue '<=' 'repeat' '(' expression ')' event_control expression ';'
  |
  'wait' '(' expression ')' statement_or_null
  |
  Sys_identifier '(' expression_list_with_nuls ')' ';'
  |
  Sys_identifier ';'
  |
  hierarchy_identifier '(' expression_list_proper ')' ';'
  |
  /* NOTE: The standard doesn't really support an empty argument list
     between parentheses, but it seems natural, and people commonly
     want it. So accept it explicitly. */
  hierarchy_identifier '(' ')' ';'
  |
  hierarchy_identifier ';'
  |
  expect_property_statement
  ;

opt_else_statement:
  /* empty */
  |
  'else' statement_or_null
  ;
  
join_keyword:
  'join'
  |
  'join_any'
  |
  'join_none'
  ;

statement_list:
  statement_list statement
  <<D1_next_eq_D2>>
  |
  statement
  ;

statement_or_null:
  statement
  |
 ';'
  ;

/*
analog_statement:
  branch_probe_expression '<+' expression ';'
  ;
*/
  /* Task items are, other than the statement, task port items and
     other block items. */
task_item:
  block_item_decl
  |
  task_port_item 
  ;

reg_opt:
  /* empty */
  |
  'reg' 
  ;

task_port_item:
  'input' reg_opt signed_opt range_opt list_of_identifiers ';'
  |
  'output' reg_opt signed_opt range_opt list_of_identifiers ';'
  |
  'inout' reg_opt signed_opt range_opt list_of_identifiers ';'
  |
  /* When the port is an integer, infer a signed vector of the integer
     shape. Generate a range ([31:0]) to make it work. */
  'input' 'integer' list_of_identifiers ';'
  |
  'output' 'integer' list_of_identifiers ';'
  |
  'inout' 'integer' list_of_identifiers ';'
  |
  /* Ports can be time with a width of [63:0] (unsigned). */
  'input' 'time' list_of_identifiers ';'
  |
  'output' 'time' list_of_identifiers ';'
  |
  'inout' 'time' list_of_identifiers ';'
  |
  /* Ports can be real or realtime. */
  'input' real_or_realtime list_of_identifiers ';'
  |
  'output' real_or_realtime list_of_identifiers ';'
  |
  'inout' real_or_realtime list_of_identifiers ';'
  ;

task_item_list:
  task_item_list task_item
  |
  task_item
  ;

task_item_list_opt:
  /* empty */
  |
  task_item_list
  ;

task_port_decl:
  'input' reg_opt signed_opt range_opt Identifier
  |
  'output' reg_opt signed_opt range_opt Identifier
  |
  'inout' reg_opt signed_opt range_opt Identifier
  |
  /* Ports can be integer with a width of [31:0]. */
  'input' 'integer' Identifier
  |
  'output' 'integer' Identifier
  |
  'inout' 'integer' Identifier
  |  
  /* Ports can be time with a width of [63:0] (unsigned). */
  'input' 'time' Identifier
  |
  'output' 'time' Identifier
  |
  'inout' 'time' Identifier
  |
  /* Ports can be real or realtime. */
  'input' real_or_realtime Identifier
  |
  'output' real_or_realtime Identifier
  |
  'inout' real_or_realtime Identifier
  ;

task_port_decl_list:
  task_port_decl_list ',' task_port_decl
  |
  task_port_decl
  |
  task_port_decl_list ',' Identifier
  |
  task_port_decl_list ','
  |
  task_port_decl_list ';'
  ;

udp_body:
  'table'  udp_entry_list 'endtable' 
  ;

udp_entry_list:
  udp_comb_entry_list
  |
  udp_sequ_entry_list
  ;

udp_comb_entry:
  udp_input_list ':' udp_output_sym ';'
  ;

udp_comb_entry_list:
  udp_comb_entry
  |
  udp_comb_entry_list udp_comb_entry
  ;

udp_sequ_entry_list:
  udp_sequ_entry
  |
  udp_sequ_entry_list udp_sequ_entry
  ;

udp_sequ_entry:
  udp_input_list ':' udp_input_sym ':' udp_output_sym ';'
  ;

udp_initial:
  'initial' Identifier '=' number ';'
  ;

udp_init_opt:
  /* empty */
  |
  udp_initial
  ;

udp_input_list:
  udp_input_sym
  |
  udp_input_list udp_input_sym
  ;

udp_input_sym:
 '0' 
  |
  '1'
  |
  'x'
  |
  '?'
  |
  'b'
  |
  '*'
  |
  '%'
  |
  'f'
  |
  'F'
  |
  'l'
  |
  'h'
  |
  'B'
  |
  'r' 
  |
  'R'
  |
  'M'
  |
  'n'
  |
  'N'
  |
  'p'
  |
  'P'
  |
  'Q'
  |
  'q'
  |
  '_'
  |
  '+' 
  ;

udp_output_sym:
  '0' 
  |
  '1' 
  |
  'x'
  |
  '-'
  ;

  /* Port declarations create wires for the inputs and the output. The
     makes for these ports are scoped within the UDP, so there is no
     hierarchy involved. */
udp_port_decl:
  'input' list_of_identifiers ';'
  |
  'output' Identifier ';'
  |
  'reg' Identifier ';'
  |
  'reg' 'output' Identifier ';'
  ;

udp_port_decls:
  udp_port_decl
  |
  udp_port_decls udp_port_decl
  ;

udp_port_list:
  Identifier
  |
  udp_port_list ',' Identifier
  ;

udp_reg_opt:
  /* empty */
  |
  'reg' 
  ;

udp_initial_expr_opt:
  /* empty */
  |
  '=' expression
  ;

udp_input_declaration_list:
  'input' Identifier
  |
  udp_input_declaration_list ',' 'input' Identifier
  ;

udp_primitive:
        /* This is the syntax for primitives that uses the IEEE1364-1995
	   format. The ports are simply names in the port list, and the
	   declarations are in the body. */
  'primitive' Identifier '(' udp_port_list ')' ';'
    udp_port_decls
    udp_init_opt
    udp_body
    'endprimitive'
  |
    /* This is the syntax for IEEE1364-2001 format definitions. The port
     names and declarations are all in the parameter list. */
  'primitive' Identifier
    '(' 'output' udp_reg_opt Identifier udp_initial_expr_opt ','
      udp_input_declaration_list ')' ';'
      udp_body
    'endprimitive'
  ;



 /****************************************************/
 /*  A.K. Extension to include assertions            */
 /****************************************************/
concurrent_assertion_item_declaration:
  property_declaration
  |
  sequence_declaration
  ;

property_declaration:
  'property' 
    Identifier 
    <<property_begin>>
    opt_pars_list_of_formals 
    ';'
    opt_assertion_variable_declarations 
    property_spec 
    ';'
    'endproperty'  
    opt_end_identifier
    <<property_end>>
  |
  'property' 
    Property_Name 
    <<property_begin>>
    opt_pars_list_of_formals 
    ';'
    opt_assertion_variable_declarations 
    property_spec 
    ';'
    'endproperty'  
    opt_end_identifier
    <<property_end>>  
  ;

opt_pars_list_of_formals:
  /* empty */
  |
  '(' opt_list_of_formals ')'
  ;

opt_list_of_formals:
  /* empty */
  |
  list_of_formals
  ;

property_spec:
  opt_clocking_event opt_disable_iff_block property_expr
  ;

property_expr:
  Property_Name opt_pars_actual_arg_list 
  <<property_instance>>
  | 
  '(' property_expr ')' 
  <<par_property_par>>
  |
  'not' property_expr 
  <<not_property>>
  | 
  property_expr 'or' property_expr 
  <<prop_or_prop>>
  |
  property_expr 'and' property_expr 
  <<prop_and_prop>>
  | 
  sequence_expr '|->' property_expr
  <<seq_ovi_prop>>
  | 
  sequence_expr '|=>' property_expr 
  <<seq_novi_prop>>
  | 
  'if' '(' expression ')' property_expr opt_else_property_expr
  <<if_else_prop>>
  | 
  /* avoid conflict
  clocking_event property_expr
  <<clk_property>>
  |
  */
  sequence_expr
  ;

opt_else_property_expr:
  /* empty */
  |
  'else' property_expr 
  ;

/* sequence definition */

sequence_declaration:
  'sequence' 
    Identifier 
    <<sequence_begin>>
    opt_pars_list_of_formals 
    ';'
    opt_assertion_variable_declarations 
    sequence_expr 
    ';'
    'endsequence' 
    opt_end_identifier
    <<sequence_end>>
  ;

opt_assertion_variable_declarations:
  /* empty */
  |
  assertion_variable_declarations
  ;

assertion_variable_declarations:
  assertion_variable_declaration
  |
  assertion_variable_declarations assertion_variable_declaration
  <<D1_next_eq_D2>>
  ;

sequence_item:
  expression
  |
  expression opt_boolean_abbrev
  <<seq_expression_abbrev>>
  |
  '(' expression opt_coma_sequence_match_items ')' 
    opt_boolean_abbrev
  <<seq_par_exp_match_par_abbrev>>  
  |
  sequence_instance opt_sequence_abbrev
  <<seq_inst_abbrev>>
  | 
  'first_match' '(' sequence_expr opt_coma_sequence_match_items ')'
  <<seq_first_match>>
  | 
  expression 'throughout' sequence_expr 
  <<seq_exp_throughout_seq>>
  |
  expression 'and' sequence_expr
  <<seq_seq_and_seq>>
  | 
  '(' sequence_expr ')' 'and' sequence_expr
  <<seq_par_and_seq>>
  |
  expression 'intersect' sequence_expr
  <<seq_seq_intersect_seq>>
  |
  '(' sequence_expr ')' 'intersect' sequence_expr  
  <<seq_par_intersect_seq>>
  |
  expression 'or' sequence_expr 
  <<seq_seq_or_seq>>  
  |
  '(' sequence_expr ')' 'or' sequence_expr
  <<seq_par_or_seq>>
  |
  expression 'within' sequence_expr
  <<seq_seq_within_seq>>
  |
  '(' sequence_expr ')' 'within' sequence_expr
  <<seq_par_within_seq>>
  |
  '(' sequence_expr opt_coma_sequence_match_items ')' opt_sequence_abbrev 
  <<seq_par_seq_match_par_abbrev>>  
  ;
  
/* from here */
  
sequence_expr:
  opt_cycle_delay_range sequence_item opt_more_sequence_item
  <<sequence_expr>>
  |
  '(' sequence_expr ')'
  <<par_sequence_expr>>  
  ;

opt_cycle_delay_range:
  /* empty */
  |
  cycle_delay_range
  ;
  
opt_more_sequence_item:
  /* empty */
  |
  more_sequence_item
  ;

more_sequence_item:
  cycle_delay_range_sequence_item
  |
  more_sequence_item cycle_delay_range_sequence_item
  <<more_cycle_delay_range_sequence_item>>  
  ;

cycle_delay_range_sequence_item:
  cycle_delay_range  sequence_expr_item
  <<cycle_delay_range_sequence_item>>
  ;
    
sequence_expr_item:
  /*  expression_or_dist opt_boolean_abbrev */
  expression opt_boolean_abbrev
  <<seq_expression_abbrev>>
  | 
  /*  '(' expression_or_dist opt_coma_sequence_match_items ')' */
  '(' expression opt_coma_sequence_match_items ')' 
    opt_boolean_abbrev
  <<seq_par_exp_match_par_abbrev>>
  |
  sequence_instance opt_sequence_abbrev
  <<seq_inst_abbrev>>
  | 
  '(' sequence_expr opt_coma_sequence_match_items ')' opt_sequence_abbrev 
  <<seq_par_seq_match_par_abbrev>>
  | 
  sequence_expr 'and' sequence_expr
  <<seq_seq_and_seq>>
  | 
  sequence_expr 'intersect' sequence_expr
  <<seq_seq_intersect_seq>>
  |
   sequence_expr 'or' sequence_expr 
   <<seq_seq_or_seq>>
  | 
  'first_match' '(' sequence_expr opt_coma_sequence_match_items ')'
  <<seq_first_match>>
  | 
  /*  expression_or_dist 'throughout' sequence_expr  */
  expression 'throughout' sequence_expr 
  <<seq_exp_throughout_seq>>
  | 
  sequence_expr 'within' sequence_expr 
  <<seq_seq_within_seq>>
  | 
  clocking_event sequence_expr
  <<seq_clk_seq>>
  ;
  /*
  |
  '(' sequence_item ')'
  <<par_seq_item>>
  ;
  */
  
opt_sequence_abbrev:
  /* empty */
  |
  sequence_abbrev
  ;

opt_boolean_abbrev:
  /* empty */
  |
  boolean_abbrev
  ;

cycle_delay_range_sequence_expr:
  cycle_delay_range  sequence_expr
  <<cycle_delay_range_sequence_expr>>
  ;

opt_coma_sequence_match_items:
  /* empty */
  |
  coma_sequence_match_items
  ;

coma_sequence_match_items:
  ',' sequence_match_item
  |
  coma_sequence_match_items ',' sequence_match_item
  <<coma_sequence_match_items>>
  ;

cycle_delay_range:
  '##' integral_number
  <<delay_integral_number>>
  |
  '##' Identifier 
  <<delay_Identifier>>
  |
  '##' '(' constant_expression ')'
  <<delay_par_constant_expression>>
  |
  '##' '[' cycle_delay_const_range_expression ']'
  <<delay_br_delay_range>>
  ;

/* to here */

sequence_method_call:
  sequence_instance '.' Identifier
  ;

sequence_match_item:
  operator_assignment
  |
  inc_or_dec_expression 
  ;

/* subroutine call is not arrowed.
  | 
  subroutine_call
  ;
*/

sequence_instance:
  Identifier opt_pars_actual_arg_list
  <<sequence_instance>>
  ;
  
/* above is simplified from
  ps_identifier opt_pars_actual_arg_list
  ;
*/
formal_list_item:
  Identifier opt_assign_actual_arg_expr
  <<formal_list_item>>
  ;

opt_assign_actual_arg_expr:
  /* empty */
  |
  '=' actual_arg_expr 
  ;

list_of_formals:
  formal_list_item
  |
  list_of_formals ',' formal_list_item
  ;


formal_arg_list:
  formal_arg
  |
  formal_arg_list ',' formal_arg
  <<formal_arg_list>>
  ;

formal_arg:
  '.' Identifier '(' actual_arg_expr ')'
  <<formal_arg>>
  ;

actual_arg_expr:
  expression
  ;

/* above is simplified from
  event_expression
  |
  '$'
  ;
*/

boolean_abbrev:
  consecutive_repetition
  | 
  non_consecutive_repetition
  | 
  goto_repetition
  ;

sequence_abbrev:
  consecutive_repetition
  ;

consecutive_repetition:
  '[' '*' const_or_range_expression ']'
  <<consecutive_repetition>>
  ; 

non_consecutive_repetition:
  '[' '=' const_or_range_expression ']' 
  <<non_consecutive_repetition>>
  ;

goto_repetition:
  '[' '->' const_or_range_expression ']'
  <<goto_repetition>>
  ;

const_or_range_expression:
  constant_expression
  |
  cycle_delay_const_range_expression
  ;

cycle_delay_const_range_expression:
  constant_expression ':' constant_expression
  <<ranged_bounded_cycle_delay>>
  |
  constant_expression ':' '$'
  <<ranged_unbounded_cycle_delay>>
  ;

expression_or_dist:
  expression opt_dist_list
  ;

opt_dist_list:
  /* empty */
  |
  dist_list
  ;

dist_list:
  dist_item
  |
  dist_list ',' dist_item
  ;

dist_item:
  value_range opt_dist_weight
  ;

opt_dist_weight:
  /* empty */
  |
  ':=' expression
  |
  ':/' expression
  ;

assertion_variable_declaration:
  data_type list_of_variable_identifiers ';'
  <<assertion_variable_declaration>>
  ;

/* concurrent assertion item definitions */ 

concurrent_assertion_item:
  opt_block_id concurrent_assertion_statement 
  <<concurrent_assertion_item>>
  ;

opt_block_id:
  /* empty */
  |
  Identifier ':'
  <<block_id>>
  ;

concurrent_assertion_statement:
  assert_property_statement 
  |
  assume_property_statement
  | 
  cover_property_statement
  ;

assert_property_statement:
  'assert' 
   'property' 
   <<assert_begin>>
   '(' 
   property_spec
   ')' 
   action_block
  <<assert_property_statement>>
  ;

assume_property_statement:
  'assume' 'property'
   <<assert_begin>>
   '(' property_spec ')' ';'
  <<assume_property_statement>>
  ;

cover_property_statement:
  'cover' 'property' 
   <<assert_begin>>
  '(' property_spec ')' statement_or_null
  <<cover_property_statement>>
  ;

expect_property_statement:
  'expect' '(' property_spec ')' action_block
  <<expect_property_statement>>
  ;

/* 
property_instance:
  Identifier opt_pars_actual_arg_list 
  <<property_instance>>
  ;
*/

/* ps_identifier opt_pars_actual_arg_list */

action_block:
  statement_or_null
  |
  opt_statement 'else' statement_or_null
  ;
  
opt_clocking_event:
  /* empty */
  |
  clocking_event
  ;

opt_disable_iff_block:
  /* empty */
  |
/* A.K. simplified */
/*  'disable' 'iff' '(' expression_or_dist ')' */
  'disable' 'iff' '(' expression ')'
  ;
  
clocking_event:
  '@' Identifier
  |
  '@' '(' event_expression ')'
  ;
  
/*
event_expression:
  opt_edge_identifier expression opt_iff_expression 
  |
  sequence_instance opt_iff_expression
  |
  event_expression 'or' event_expression 
  | 
  event_expression ',' event_expression
  ;
*/

opt_edge_identifier:
  /* empty */
  |
  edge_identifier
  ;

edge_identifier:
  'posedge'
  |
  'negedge'
  ;

opt_iff_expression:
  /* empty */
  |
  'iff' expression 
  ;

list_of_variable_identifiers:
  a_variable_identifier
  |
  list_of_variable_identifiers a_variable_identifier
  <<D1_next_eq_D2_c>> 
  ;

a_variable_identifier:
  Identifier variable_dimension
  ;

variable_dimension:
  /* empty */
  |
  sized_or_unsized_dimensions
  ;
  
sized_or_unsized_dimensions:
  sized_or_unsized_dimension
  |
  sized_or_unsized_dimensions sized_or_unsized_dimension
  ;

sized_or_unsized_dimension:
  unpacked_dimension
  |
  unsized_dimension
  ;

unsized_dimension:
  '['  ']'
  ;
  
unpacked_dimension:
  '[' constant_range ']'
  |
  '[' constant_expression ']'
  ;
  
ps_identifier:
  opt_package_scope Identifier
  <<ps_identifier>>
  ;
  
opt_package_scope:
  /* empty */
  |
  package_scope
  ;

package_scope:
  Identifier '::'
/*
  |
  '$unit' '::'
*/
  ;
  
opt_statement:
  /* empty */
  |
  statement
  ;
  
constant_expression:
  constant_primary
  |
  unary_operator constant_primary
  <<unary_constant>>
  |
  constant_expression binary_operator  constant_expression
  <<binary_constant>>
  |
  constant_expression '?' constant_expression ':' constant_expression
  <<selection_constant>>
  ;
  
constant_primary:
  primary_literal
  |
  ps_identifier
/*
  |
  genvar_identifier
  |
  opt_package_scope_or_class_scope enum_identifier
  |
  constant_concatenation
  |
  constant_multiple_concatenation
  |
  constant_function_call

  |
  '(' constant_mintypmax_expression ')'
  |
  constant_cast
*/
  ;

primary_literal:
  number
  |
  time_literal
  |
  Unbased_unsized_literal
  |
  String_literal
  ;

unary_operator:
  '+'
  <<unary_plus>>
  |
  '-'
  <<unary_minus>>
  |
  '!'
  <<unary_not>>
  |
  '~'
  <<unary_tilda>>
  |
  '&'
  <<unary_and>>
  |
  '~&'
  <<unary_nand>>
  |
  '|'
  <<unary_or>>
  |
  '~|'
  <<unary_nor>>
  |
  '^'
  <<unary_xor>>
  |
  '~^'
  <<unary_nxor>>
  |
  '^~'
  <<unary_xorn>>
  ;

binary_operator:
  '+'
  <<binary_plus>>
  |
  '-'
  <<binary_minus>>
  |
  '*'
  <<binary_star>>
  |
  '/'
  <<binary_div>>
  |
  '%'
  <<binary_mod>>
  |
  '=='
  <<binary_eqeq>>
  |
  '!='
  <<binary_neq>>
  |
  '==='
  <<binary_eqeqeq>>
  |
  '!=='
  <<binary_noteqeq>>
  |
  '=?='
  <<binary_eqqeq>>
  |
  '!?='
  <<binary_nqeq>>
  |
  '&&'
  <<binary_land>>
  |
  '||'
  <<binary_lor>>
  |
  '**'
  <<binary_starstar>>
  |
  '<'
  <<binary_lt>>  
  |
  '<='
  <<binary_le>>
  |
  '>'
  <<binary_gt>>
  |
  '>='
  <<binary_ge>>
  |
  '&'
  <<binary_and>>
  |
  '|'
  <<binary_or>>
  |
  '^'
  <<binary_xor>>
  |
  '^~'
  <<binary_xorn>>
  |
  '~^'
  <<binary_nxor>>
  |
  '>>'
  <<binary_rshift>>
  |
  '<<'
  <<binary_lshift>>
  |
  '>>>'
  <<binary_lrshift>>
  |
  '<<<'
  <<binary_llshift>>
  ;

inc_or_dec_operator:
  '++'
  <<inc_operator>>
  |
  '--'
  <<dec_operator>>
  ;

time_literal:
  Unsigned_number time_unit
  ;

time_unit:
  's'
  |
  'ms'
  |
  'us'
  |
  'ns'
  |
  'ps'
  |
  'fs'
  |
  'step'
  ;


/* limitted type of data are allowed to be used in SVA variable */
data_type:
  integer_vector_type opt_signing opt_packed_dimension
  |
  integer_atom_type opt_signing
  ;
  
  /*
  non_integer_type
  |

  struct_union opt_packed_signing '{' struct_union_menbers '}'
    opt_packed_dimensions
  |
  'enum' opt_enum_base_type '{' enam_name_declarations '}'
  |
  'string'
  |
  'chandle'
  |
  'virtual' opt_interface_keyword Identifier
  |
  opt_class_or_package_scope Identifier opt_packed_dimensions
  |
  class_type
  |
  'event'
  |
  ps_identifier  
  ;
  */
  
integer_type:
  integer_vector_type
  |
  integer_atom_type
  ;

integer_atom_type:
  'byte'
  <<byte>>
  |
  'shortint'
  <<shorting>>
  |
  'int'
  <<int>>
  |
  'longint'
  <<longint>>
  |
  'integer'
  <<integer>>
  ;
  
  /*
  |
  'time'
  ;
  */
  
integer_vector_type:
  'bit'
  <<bit>>
  |
  'logic'
  <<logic>>
  |
  'reg'
  <<reg>>
  ;

non_integer_type:
  'shortreal'
  |
  'real'
  |
  'realtime'
  ;

opt_signing:
  /* empty */
  |
  signing
  ;

signing:
  'signed'
  |
  'unsigned'
  ;

constant_range:
  constant_expression ':' constant_expression
  ;

/* 
   next is simplified, 
   actually:
     lpvalue assignment_operator expression
*/

operator_assignment:
  Identifier assignment_operator expression
  <<operator_assignment>>
  ;


assignment_operator:
  '='
  <<assign_operator>>
  |
  '+=' 
  <<func_assign_operator>>
  |
  '-='
  <<func_assign_operator>>
  |
  '*='
  <<func_assign_operator>>
  |
  '/=' 
  <<func_assign_operator>>
  |
  '%=' 
  <<func_assign_operator>>
  |
  '&='
  <<func_assign_operator>>
  |
  '|='
  <<func_assign_operator>>
  |
  '^='
  <<func_assign_operator>>
  |
  '<<=' 
  <<func_assign_operator>>
  |
  '>>='
  <<func_assign_operator>>
  |
  '<<<='
  <<func_assign_operator>>
  |
  '>>>='
  <<func_assign_operator>>
  ;

/*
  next is simplified
  actually:
  inc_or_dec_operator lpvalue
  |
  lpvalue inc_or_dec_operator
*/
inc_or_dec_expression:
  inc_or_dec_operator Identifier
  <<inc_or_dec_Identifier>>
  |
  Identifier inc_or_dec_operator
  <<Identifier_inc_or_dec>>
  ;

opt_end_identifier:
  /* empty */
  |
  ':' Identifier
  ;

value_range:
  expression
  |
  '[' expression ':' expression ']'
  ;

opt_pars_actual_arg_list:
  /* empty */
  |
  '(' opt_actual_arg_list ')' 
  ;

opt_actual_arg_list:
  /* empty */
  |
  actual_arg_list
  |
  formal_arg_list
  ;

actual_arg_list:
  actual_arg_expr 
  |
  actual_arg_list ',' actual_arg_expr 
  <<actual_arg_list>>
  ;

opt_packed_dimensions:
  /* empty */
  |
  packed_dimensions
  ;

packed_dimensions:
  packed_dimension
  |
  packed_dimensions packed_dimension
  ;

opt_packed_dimension:
  /* empty */
  |
  packed_dimension
  ;
  
packed_dimension:
  '[' constant_range ']'
  ;
  /*
  |
  '['  ']'
  ;
  */

expression:
  '(' expression ')'
  <<par_expression>>
  |
  expr_primary
  <<DDeqD1prim>>
  |
  unary_operator expr_primary
  <<unary_expression>>
  |
  expression binary_operator expression
  <<binary_expression>>
  |
  expression '?' expression ':' expression
  <<selection_expression>>
  ;
    
  
  