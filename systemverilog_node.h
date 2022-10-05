/***************************************************************************
 *
 *  systemverilog_node.h: Verilog Parse Nodes 
 *
 *  Author: Atsushi Kasuya
 *
 *   Copyright (C) 2011 Atsushi Kasuya 
 *
 ***************************************************************************/
typedef enum {
  SV_unknown_name = 0,
  SV_byte_type,
  SV_shortint_type,
  SV_int_type,
  SV_longint_type,
  SV_integer_type,
  SV_float_type,
  SV_reg_type,
  SV_bit_type,
  SV_logic_type,
  SV_string_type,
  SV_port_name,
  SV_parameter_name,
  SV_net_name,
  SV_reg_name,
  SV_arg_name,
  SV_localvar_name,
  SV_module_name,
  SV_func_name,
  SV_task_name,
  SV_sequence_name,
  SV_property_name,
  SV_label_name,
  SV_name_dummy
} SV_name_type ;

typedef enum {
  SV_unknown_sub_type=0,
  SV_single_sub_type,
  SV_array_sub_type,
  SV_multi_array_sub_type,
  SV_dummy_sub_type
} SV_sub_type ;

typedef enum {
  SV_port_input,
  SV_port_output,
  SV_port_inout,
  SV_port_dummy,
} SV_ioport_type ;

typedef enum {
  SV_noedge = 0,
  SV_posedge,
  SV_negedge,
  SV_bothedge,
  SV_clockedge
} SV_edge_type ;

typedef enum {
  SV_no_compile = 0,
  SV_module_top,
  SV_concurrent_assertion,
  SV_assert_property,
  SV_assume_property,
  SV_cover_property,
  SV_expect_property,
  
  SV_sequence_dcl,
  SV_property_dcl,
 
  /* property_expr: */
  SV_par_property_par,
  SV_not_property,
  SV_prop_or_prop,
  SV_prop_and_prop,
  SV_seq_ovi_prop,
  SV_seq_novi_prop,
  SV_if_else_prop,
  SV_prop_inst,
  SV_clk_property,
  SV_property_instance,
  SV_par_property_instance,
  
  /* sequence expr: */
  SV_sequence_expr,
  SV_par_sequence_expr,
  SV_par_seq_item,
  SV_cycle_delay_range_sequence_item,
  SV_seq_expression_abbrev,
  SV_seq_cycle_dly_seq_exprs,
  //SV_cycle_delay_range_sequence_item,
  SV_cycle_delay_range_sequence_expr,
  SV_seq_seq_itm_opt_dly_seq,
  SV_seq_par_exp_match_par_abbrev,
  SV_seq_inst_abbrev,
  SV_seq_par_seq_match_par_abbrev,
  SV_seq_seq_and_seq,
  SV_seq_seq_intersect_seq,
  SV_seq_seq_or_seq,
  SV_seq_first_match,
  SV_seq_exp_throughout_seq,
  SV_seq_seq_within_seq,
  SV_seq_clk_seq,
  
  SV_consecutive_repetition,
  SV_non_consecutive_repetition,
  SV_goto_repetition,
  
  SV_unary_constant,
  SV_binary_constant,
  SV_selection_constant,
  
  SV_delay_integral_number,
  SV_delay_Identifier,
  SV_delay_par_constant_expression,
  SV_delay_br_delay_range,
  
  /* expression */
  SV_expression,
  SV_par_expression,
  
  /* constant folding */
  SV_integral_number,
  SV_ranged_bounded_cycle_delay,
  SV_ranged_unbounded_cycle_delay,
 
  SV_unary_expression,
  SV_binary_expression,
  SV_select_expression,
  
  SV_sys_function_call,
  
  SV_sequence_instance,
  
  SV_identifier,
  SV_hieracy_identifier,
  SV_identifier_singlesell,
  SV_identifier_rangesell,
  
  SV_unary_plus,
  SV_unary_minus,
  SV_unary_not,
  SV_unary_tilda,
  SV_unary_and,
  SV_unary_nand,
  SV_unary_or,
  SV_unary_nor,
  SV_unary_xor,	
  SV_unary_nxor,
  SV_unary_xorn,
  
  SV_binary_plus,
  SV_binary_minus,
  SV_binary_star,
  SV_binary_div,
  SV_binary_mod,
  SV_binary_eqeq,
  SV_binary_neq,
  SV_binary_eqeqeq,
  SV_binary_noteqeq,
  SV_binary_eqqeq,
  SV_binary_nqeq,
  SV_binary_land,
  SV_binary_lor,
  SV_binary_starstar,
  SV_binary_lt,
  SV_binary_le,
  SV_binary_gt,
  SV_binary_and,
  SV_binary_or,
  SV_binary_xor,
  SV_binary_xorn,
  SV_binary_nxor,
  SV_binary_rshift,
  SV_binary_lshift,
  SV_binary_lrshift,
  SV_binary_llshift,
  
  SV_inc_operator,
  SV_dec_operator,
  
  SV_assign_operator,
  SV_func_assign_operator,
  
  /* port dcl */
  SV_port_ref,
  SV_port_ref_1,
  SV_port_ref_2,
  SV_input_port_dcl,
  SV_inout_port_dcl,
  SV_output_port_dcl,
  SV_net_declaration,
  SV_net_assign_declaration,
  SV_net_st_assign_declaration,
  SV_trireg_dcl,
  SV_port_dcl_a,
  SV_port_dcl_b,
  SV_port_dcl_c,
  SV_port_dcl_d,
  SV_port_dcl_e,
  SV_port_identifire,
  SV_port_identifire_assign,
  SV_list_of_port_identifiers,
  
  SV_operator_assignment,
  SV_inc_or_dec_Identifier,
  SV_Identifier_inc_or_dec,
  
  SV_formal_arg_list,
  SV_formal_arg,
  SV_actual_arg_list,
  
  SV_port_list,
  SV_port_dcl_list,
  SV_module_item_begin,
  
  SV_sysfunc_block,
  SV_sysfunc_past_block,
  SV_localvar_access,
  SV_onehot_block,
  
  SV_posedge_event,
  SV_negedge_event
  
} SV_assertion_type ;

typedef enum {
  sys_undef = 0,
  sys_rose,
  sys_fell,
  sys_onehot,
  sys_onehot0,
  sys_stable,
  sys_past,
  sys_sampled,
  sys_countones,
  sys_isunknown
} SV_system_function ;

typedef struct systemverilog_node_s systemverilog_node ;
typedef struct named_node_s named_node ;
typedef struct sva_node_s sva_node ;
typedef struct time_node_s time_node ;

struct systemverilog_node_s {
    char *name ;
    unsigned int  linenum ;
    unsigned int  debug_linenum ;
    unsigned int location ;
    char *filename ;
    int type ;            /* 0: nonterminal,  >0 : terminal node */
    SV_name_type data_type ;
    SV_assertion_type sva_type ;
    void *next ; 
    int num_node ;
    systemverilog_node *parent ;
    systemverilog_node *node[20] ;     /* 20 enough? */
    named_node *nm ;
    int const_flag  ;
    int const_value ;
    SV_system_function sysfunc ;
    systemverilog_node *exp_list ; /* expression linked list */
    systemverilog_node *lvar_exp_list ; /* localvar linked list */
    systemverilog_node *onehot_list ; /* onehot func linked list */
    int exp_id ;
    int clk_negedge ; 
    int localvar_access ;  /* flag if lvar access somewhere */
    systemverilog_node *sysfunc_block ;
    systemverilog_node *sysfunc_past_block ;
    systemverilog_node *onehot_block ;
    systemverilog_node *clock_node ;
    systemverilog_node *sync_input_node ;
    int rose_id ;
    int fell_id ;
    int past_id ;
    int stable_id ;
    int sampled_id ;
    int is_onehot ;
    sva_node *assertion_node ;
      
    int past_num ;

    int no_sync ;
  
    int num_error_vector ;
    int num_cover_vector ;

} ;

struct named_node_s {  
  char *name ;
  SV_name_type  type ;
  int match_item_flag ; /* flag local var used in match item */
  named_node  *data_type ;
  named_node  *next ;
  /* index for local variable */
  int var_index ;
  /* values for parameter, etc */
  systemverilog_node  *value  ;
  systemverilog_node  *value_range  ; 
  systemverilog_node  *default_arg_value ; 
  systemverilog_node  *arg_value  ;  /* for on the fly arg assignment */
 
  int lvar_exp_num ;
  int lvar_exp_size ;
  systemverilog_node  **lvar_exp  ;  /* link to top of exp using lvar */
 
  int lvar_acc_num ;
  int lvar_acc_size ;
  sva_node **lvar_acc ;
  
  int sign ;
  int bus_m ;
  int bus_n ;
  int bus_endian ;
  SV_ioport_type port_type ;
  int wire_type ;
  
  char *filename ;  /* debug info */
  int  linenum ;
  int location ;
  /* pointers to conform scope structure */
  named_node  *parent_scope ;
  named_node  *next_in_scope ;
  named_node  *child_scope ;
  named_node  *next_brother ;
  /* named_node stack */
  named_node  *prev_scope ;
  /* point to the scope node of its own */
  named_node  *scope ;
  int scope_id ;
  int index ;  /* for enum member index */
  /* flags for the name */
  int is_simple ;  /* simple port, etc.. */
  int is_local ;
  int local_var ;
 /* bit range info shared by bit/port */
  int  ub ;
  int  lb ;
  int  i_endian ;
  
  sva_node *sva ;  /* corresponding SVA declaration */
  
  int sync_id ;
  
  /* unused part
  int rose ;
  int fell ;
  int onehot ;
  int onehot0 ;
  int stable ;
  int past ;
  int sampled ;
  int countones ;
  char *rose_signame ;
  char *fell_signame ;
  char *onehot_signame ;
  char *stable_signame ;
  char *past_signame ;
  char *sampled_signame ;
  char *countones_signame ;
  
  union {
    struct {
      SV_ioport_type type ;
   } port ;
    struct {
      systemverilog_node *args ;
      systemverilog_node  *func_block ;
     int index ;
    } func ;
    struct {
      systemverilog_node *range ;
     int is_var ;
      int index ;
      int local ;
    } var ;
 } info ;
  */
} ;

typedef enum {
  SE_unknown = 0,
  SE_expression,
  SE_delay,
  SE_and,
  SE_or,
  SE_intersect,
  SE_within,
  SE_throughout,
  SE_first_match,
  SE_clock,
  SE_consective_repetition,
  SE_goto_repetition,
  SE_nonconsective_repetition,
  SE_sequience_dcl,
  SE_sequence_instance,
  SE_sequence_expr,
  
  SE_sequence_item,
  SE_argument,
    
  SE_match_item_assign,
  SE_match_item_inc_or_dec_identifier,
  SE_match_item_identifier_inc_or_dec,
  SE_sequence_dcl,
  
  SE_local_var_dcl,
  
  PR_seq,
  PR_not,
  PR_or,
  PR_and,
  PR_overlap_implication,
  PR_non_overlap_implication,
  PR_if_else_property,
  PR_clock_property,
  PR_property_instance,
  PR_property_dcl,
  PR_property_inst
} sva_node_type ;

typedef enum {
  SVN_none = 0,
  SVN_branch,
  SVN_filter,
  SVN_brfilter
} sva_node_attribute ;

typedef enum {
  RCS_free = 0,
  RCS_single,
  RCS_block 
} sva_resouce ;

struct sva_node_s {
  sva_node_type  type ;
  
  unsigned int  linenum ;
  char *filename ;  
  
  named_node *nm ;
  
  sva_node *node_a ;
  sva_node *node_b ;
    
  sva_node *arg_node_a ;
  sva_node *arg_node_b ;

  sva_resouce resource ;
  sva_node_attribute attrib ;
  sva_node_attribute p_attrib ;
  
  //sva_node *end_of_resblock ; // the last node of resource block
  
  char *operator ;
  systemverilog_node *exp ;
 
  sva_node *arg_list  ;
  sva_node *var_list  ;
  systemverilog_node *data_type ;

  systemverilog_node *clock ;
  systemverilog_node *disable_expression  ;
  
  sva_node *parent ;
  sva_node *next ;

  sva_node *p_stack ;

  systemverilog_node *origin ;
  
  int min_cyc ;
  int max_cyc ;  /* 0: Sinple Delay -1:Unbounded */
  int simple_delay ;
  
  int seq_match_id ;  // wire number to execute sequence match item
  
  // int inplicit_first_match ;
  
  time_node *tm_node ;
  int index ;
  sva_node *var_node ;
  sva_node *act_var_node ;
  
    // flags to handle prop-not ( implication ) and prop_and/prop_or
    int sub_property ;  // should generate property_busy
    int antece_zero ;
    int invert ;
    int error_check ;
    int initial_check ;

} ;

typedef enum {
  TMA_none = 0,
  TMA_F,
  TMA_H
} time_node_attribute ;

typedef enum {
  TM_zero = 0,
  TM_single,
  TM_multi,
  TM_unbound,
  TM_resouce
} time_node_type ;

struct time_node_s {
  time_node_type type ;
  time_node_attribute attrib ;
  int level ;
  int time1 ;
  int time2 ;
  sva_node *head ;
  sva_node *tail ;
  time_node *node_a ;
  time_node *node_b ;
  
  time_node *next ;

  //int first_match ;

} ;


#define ALLOC_SV_NODE (systemverilog_node *)calloc(1,sizeof(systemverilog_node)) 

#define SKIP_ON_ERROR  if( error_flag ) break

#define ALLOC_NM_NODE (name_node *)calloc(1,sizeof(name_node)) 

#define ALLOC_SVA_NODE (sva_node *)calloc(1,sizeof(sva_node)) 

#define ALLOC_TM_NODE (time_node *)calloc(1,sizeof(time_node)) 

#define ALLOC(x)  (x *)calloc(1, sizeof(x))

#define DEALOC(x) free(x)

#define PASS0 if ( compile_pass==0 )

#define PASS1 if ( compile_pass==1 )

#define PASS2 if ( compile_pass==2 )

#define PASS0_1 if ( compile_pass==0 || compile_pass==1 )

#define PASS1_2 if ( compile_pass==1 || compile_pass==2 )
