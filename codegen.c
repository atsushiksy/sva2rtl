/***************************************************************************
 *
 *  codegen.c: code generation for SVA to RTL compiler
 *
 *  Author: Atsushi Kasuya
 *
 *
 ***************************************************************************/
 /* 
   
   Copyright (C) 2011 Atsushi Kasuya

   
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include "systemverilog_node.h"
#include "symtab.h"
#include "code_def.h"

#include "y_tab.h"

extern FILE *out ;
extern unsigned int debug_line_num  ;

extern systemverilog_node *root_node ;
extern int error_count ;
extern int debug_line ;
extern int match_flag ;
extern int overwrap_flag ;
extern int overwrap_depth ;
extern int sync_expression ;
extern int sync_ff_num ;
extern int sync_input ;
extern int internal_overwrap_flag ;
extern int internal_filter_flag ;

extern int arv_use_counter ;
extern int arv_use_flat_rep ;

extern char *version_string ;

static unsigned int cur_lin, cur_loc ;
static unsigned int last_lin, last_loc ;
static char *last_name ;

static unsigned int pline = 0 ;

static int iovwp_depth = 0 ;

static char *cur_name ;

static flag = 0 ;
static in_flag = 0 ;

static int level ;
static int *p = NULL ;

static systemverilog_node *current_module = NULL ;

static systemverilog_node *exp_node = NULL ;
static systemverilog_node *exp_clock_node = NULL ;
static systemverilog_node *exp_lvar_node = NULL ;
static systemverilog_node *onehot_node = NULL ;
static systemverilog_node *current_exp_node = NULL ;
static systemverilog_node *error_enable_node = NULL ;

static int label_num = 1 ;

static systemverilog_node *clock_node = NULL ;
static int num_error_vector = 0 ;
static int num_cover_vector = 0 ;
static int assert_count = 0 ;
static int cover_count = 0 ;

static systemverilog_node *disable_node = NULL ;
static systemverilog_node *enable_node = NULL ;
static systemverilog_node *match_node = NULL ;
static systemverilog_node *busy_node = NULL ;
static systemverilog_node *block_busy_node = NULL ;
static systemverilog_node *fmatch_node = NULL ;
static systemverilog_node *error_node = NULL ;
static systemverilog_node *antece_error_node = NULL ;
static systemverilog_node *prop_error_node = NULL ;
static systemverilog_node *overwrap_node = NULL ;
static systemverilog_node *gate_node = NULL ;
static systemverilog_node *prop_busy_node = NULL ;

static int error_check = 0 ;
static int simple_pipe = 0 ;
static int initial_check = 0 ;
static int overwrap_gate = 0 ;

static int port_decl_done = 0 ;
static int internal_net_decl_done = 0 ;

static int kill_line_adjust = 0 ;

static int use_pipe_delay = 0 ;
static int get_busy_node = 0 ;
static int use_exp_id_node = 0 ;

static void rcv_node_out( systemverilog_node *node ) ;
static sva_node *sequence_dcl( 
  systemverilog_node *node, sva_node *n_args, sva_node *o_args
) ;
static sva_node *property_dcl(
  systemverilog_node *node, sva_node *n_args, sva_node *o_args
) ;
static void assign_arg_by_name( named_node *nm, sva_node *args ) ;
static void assign_arg_by_order( named_node *nm, sva_node *args ) ;
static void rtl_generation( sva_node *sva, int sub_prop ) ;

static int is_simple_delay( sva_node *sva, int flag ) ;
static void connect_port( char *prt, systemverilog_node *node, int next ) ;
static void node_out( systemverilog_node *node ) ;
static int find_lvar_expression( named_node *nm, systemverilog_node *node ) ;
static int is_zero_node( sva_node *sva ) ;
static systemverilog_node *gen_sync_input( systemverilog_node *node ) ;
static systemverilog_node *new_reg_node( int ub, int lb ) ;


static sva_node *sva_stack = NULL ;
static sva_node_attribute prev_attrib ;
static int prev_branch_depth = 0 ;

/* statistics of RTL */
static int number_of_ff = 0 ;
static int number_of_and = 0 ;
static int number_of_or = 0 ;
static int number_of_not = 0 ;
static int total_number_of_ff = 0 ;
static int total_number_of_and = 0 ;
static int total_number_of_or = 0 ;
static int total_number_of_not = 0 ;

static void init_nodes() {
  //clock_node = NULL ;
  //disable_node = NULL ;
  //enable_node = NULL ;
  match_node = NULL ;
  overwrap_node = NULL ;
  busy_node = NULL ;
  block_busy_node = NULL ;
  fmatch_node = NULL ;
  error_node = NULL ;
  antece_error_node = NULL ;
  prop_error_node = NULL ;
  overwrap_node = NULL ;
  gate_node = NULL ;
  prop_busy_node = NULL ;
}

/* constant folding */

static int get_constant( systemverilog_node *expr ) {
  int ret = 0 ;
  
  switch(expr->sva_type) {
    case SV_identifier:
      {
        if( expr->nm ) {
          if(  expr->nm->value ) {
            ret = get_constant( expr->nm->value ) ;
          }
          else if( expr->nm->arg_value ) {
            ret = get_constant( expr->nm->arg_value ) ;
          }
          else {
            fprintf( 
              stdout, "Value for Identifier %s not defined\n", expr->name 
            ) ;          
          }
        }
        else {
          fprintf( 
            stdout, "Value for Identifier %s not defined\n", expr->name 
          ) ;
       }
      }
      break ;
    case SV_integral_number:
      {
        if( expr->const_flag ) {
          ret = expr->const_value ;
        }
        else {
          fprintf( 
            stdout, "Constant value can not define at %d\n", expr->linenum
          ) ;
       }
      }
      break ;
    case SV_unary_plus:
      {
        ret = (+(get_constant(expr->node[1]) ) ) ;
     }
      break ;
    case SV_unary_minus:
      {
        ret = (- (get_constant(expr->node[1]) ) ) ;
    }
      break ;
    case SV_unary_not:
      {
        ret = (! (get_constant(expr->node[1]) ) ) ;
     }
     break ;
    case SV_unary_tilda:
      {
        ret = get_constant(expr->node[1]) ;
      }
      break ;
    case SV_unary_and:
      {
        ret = get_constant(expr->node[1]) ;
      }
      break ;
    case SV_unary_nand:
      {
        ret = get_constant(expr->node[1]) ;
      }
      break ;
    case SV_unary_or:
      {
        ret = get_constant(expr->node[1]) ;
      }
      break ;
    case SV_unary_nor:
      {
        ret = get_constant(expr->node[1]) ;
      }
      break ;
    case SV_unary_xor:
      {
        ret = get_constant(expr->node[1]) ;
      }
      break ;
    case SV_unary_nxor:
      {
        ret = get_constant(expr->node[1]) ;
      }
      break ;
    case SV_unary_xorn:
       {
        ret = get_constant(expr->node[1]) ;
      }
      break ;
   case SV_binary_plus:
     {
       ret = get_constant(expr->node[0]) + get_constant(expr->node[2]) ;
     }
     break ;
   case SV_binary_minus:
     {
       ret = get_constant(expr->node[0]) - get_constant(expr->node[2]) ;
     }
     break ;
   case SV_binary_star:
     {
       ret = get_constant(expr->node[0]) * get_constant(expr->node[2]) ;
     }
     break ;
   case SV_binary_div:
     {
       ret = get_constant(expr->node[0]) / get_constant(expr->node[2]) ;
     }
     break ;
   case SV_binary_mod:
     {
       ret = get_constant(expr->node[0]) % get_constant(expr->node[2]) ;
     }
     break ;
   case SV_binary_eqeq:
     {
       ret = (get_constant(expr->node[0]) ==  get_constant(expr->node[2]) ) ;
     }
     break ;
   case SV_binary_neq:
     {
       ret = (get_constant(expr->node[0]) !=  get_constant(expr->node[2]) ) ;
     }
     break ;
   case SV_binary_eqeqeq:
     {
       ret = ( get_constant(expr->node[0]) ==  get_constant(expr->node[2]) ) ;
     }
     break ;
   case SV_binary_noteqeq:
     {
       ret = !(get_constant(expr->node[0]) ==  get_constant(expr->node[2]) ) ;
     }
     break ;
   case SV_binary_eqqeq:
     {
       ret = (get_constant(expr->node[0]) ==  get_constant(expr->node[2]) ) ;
     }
     break ;
   case SV_binary_nqeq:
     {
       ret = ( get_constant(expr->node[0]) !=  get_constant(expr->node[2]) ) ;
     }
     break ;
   case SV_binary_land:
     {
       ret = ( get_constant(expr->node[0]) &&  get_constant(expr->node[2]) ) ;
     }
     break ;
   case SV_binary_lor:
     {
       ret = ( get_constant(expr->node[0]) ||  get_constant(expr->node[2]) ) ;
     }
     break ;
   case SV_binary_starstar:
     {
       //ret = get_constant(expr->node[0]) ** get_constant(expr->node[2]) ;
     }
     break ;
   case SV_binary_lt:
     {
       ret = (get_constant(expr->node[0]) < get_constant(expr->node[2]) ) ;
     }
     break ;
   case SV_binary_le:
     {
       ret = (get_constant(expr->node[0]) <= get_constant(expr->node[2]) ) ;
     }
     break ;
   case SV_binary_gt:
     {
       ret = ( get_constant(expr->node[0]) > get_constant(expr->node[2]) ) ;
     }
     break ;
   case SV_binary_and:
     {
       ret = get_constant(expr->node[0]) & get_constant(expr->node[2]) ;
     }
     break ;
   case SV_binary_or:
     {
       ret = get_constant(expr->node[0]) | get_constant(expr->node[2]) ;
     }
     break ;
   case SV_binary_xor:
     {
       ret = get_constant(expr->node[0]) ^ get_constant(expr->node[2]) ;
     }
     break ;
   case SV_binary_xorn:
     {
       ret = get_constant(expr->node[0]) ^ get_constant(expr->node[2]) ;
       ret = !ret ;
     }
     break ;
   case SV_binary_nxor:
     {
       ret = get_constant(expr->node[0]) ^ get_constant(expr->node[2]) ;
       ret = !ret ;
     }
     break ;
   case SV_binary_rshift:
     {
      ret = get_constant(expr->node[0]) >> get_constant(expr->node[2]) ;
     }
     break ;
   case SV_binary_lshift:
     {
       ret = get_constant(expr->node[0]) << get_constant(expr->node[2]) ;
    }
     break ;
   case SV_binary_lrshift:
     {
       ret = get_constant(expr->node[0]) >> get_constant(expr->node[2]) ;
     }
     break ;
   case SV_binary_llshift:
     {
       ret = get_constant(expr->node[0]) << get_constant(expr->node[2]) ;
     }
     break ;
  }
  
  return ret ;  
  
}


static void range_calcuration( sva_node *node, systemverilog_node *range ) {
 if( range->num_node == 1 ) {
    node->min_cyc = get_constant( range->node[0] ) ;
    node->max_cyc = 0 ;
    node->simple_delay = 1 ;
    node->attrib = SVN_none ;
    if( node->min_cyc >= arv_use_counter ) node->resource = RCS_single ;
  }
  else {
    node->min_cyc = get_constant( range->node[0] ) ;
    if( range->sva_type ==   SV_ranged_bounded_cycle_delay ) {
      node->max_cyc = get_constant( range->node[2] ) ;
      if( node->max_cyc >= arv_use_counter ) node->resource = RCS_single ;
    }
    else {
      node->max_cyc = -1 ;
      node->resource = RCS_single ;
    }
    if( node->min_cyc == node->max_cyc ) {
      node->max_cyc = 0 ;
      node->simple_delay = 1 ;
      node->attrib = SVN_none ;
      if( node->min_cyc >= arv_use_counter ) node->resource = RCS_single ;
    }
    else {
      node->simple_delay = 0 ;
      node->attrib = SVN_branch ;
      if( node->max_cyc >= arv_use_counter ) node->resource = RCS_single ;
    }
  }
}

static void set_boolean_abbrev( sva_node *node, systemverilog_node *abbrev ) {
  systemverilog_node *range = abbrev->node[2] ;
  if( range->sva_type == SV_ranged_bounded_cycle_delay ) {
    node->min_cyc = get_constant( range->node[0] ) ;
    node->max_cyc = get_constant( range->node[2] ) ;
    node->simple_delay = 0 ;  
    if( node->min_cyc == node->max_cyc ) {
      node->max_cyc = 0 ;
      node->simple_delay = 1 ;
    }
  }
  else {
    if( range->sva_type == SV_ranged_unbounded_cycle_delay ) {
      node->min_cyc = get_constant( range->node[0] ) ;
      node->max_cyc = -1 ;
      node->simple_delay = 0 ;
    }
    else {
      node->min_cyc = get_constant( range ) ;
      node->max_cyc = 0 ;
      node->simple_delay = 1 ;
    }
  }
  if( node->min_cyc == 0 ) {
    fprintf( 
      stderr, "Error at %d in %s Zero repetition is not supported\n", 
      abbrev->linenum, abbrev->filename
    ) ;
    exit(1) ;
  }
  switch( abbrev->sva_type) {
    case SV_consecutive_repetition:
    {
      if( node->node_a ||  node->max_cyc != 0 || 
                node->min_cyc > arv_use_flat_rep ) 
      {
	// not flat repetition
        if( node->resource == RCS_free ) node->resource = RCS_single ;
        if( node->simple_delay ) node->attrib = SVN_none ;
        else node->attrib = SVN_branch ;
      }
      else {
        node->attrib = SVN_none ;
      }
      node->type = SE_consective_repetition ;
    }
    break ;
    case SV_non_consecutive_repetition:
    {
      node->resource = RCS_single ; 
      node->type = SE_nonconsective_repetition ;
      node->attrib = SVN_branch ;
      // not supported              
      fprintf( 
        stderr,
        "Error at %d in %s Non consective repetition is not supported\n", 
        abbrev->linenum, abbrev->filename
      ) ;
      exit(1) ;
    }
    break ;
    case SV_goto_repetition:
    {
      // resource could already be set to RCS_block 
      if( node->resource == RCS_free ) node->resource = RCS_single ;
      node->type = SE_goto_repetition ;  
      if( node->simple_delay ) {
        node->attrib = SVN_none  ;
      }
      else {
        node->attrib = SVN_branch ;
      }
    }
    break ;
  }
}

static void delay_calculation( sva_node *node, systemverilog_node *delay ) {
  switch( delay->type ) {
    case SV_delay_integral_number :
      {
        node->min_cyc = get_constant( delay->node[1] ) ;
        node->max_cyc = 0 ;
        node->simple_delay = 1 ;         
        node->attrib = SVN_none ;
        if( node->min_cyc >= arv_use_counter ) node->resource = RCS_single ;
      }
      break ;
    case SV_delay_Identifier:
      {
        node->min_cyc = get_constant( delay->node[1] ) ;
        node->max_cyc = 0 ;
        node->simple_delay = 1 ;                 
        node->attrib = SVN_none ;
        if( node->min_cyc >= arv_use_counter ) node->resource = RCS_single ;
      }
      break ;
    case SV_delay_par_constant_expression:
      {
        node->min_cyc = get_constant( delay->node[2] ) ;
        node->max_cyc = 0 ;
        node->simple_delay = 1 ;                 
        node->attrib = SVN_none ;
        if( node->min_cyc >= arv_use_counter ) node->resource = RCS_single ;
     }
      break ;
    case SV_delay_br_delay_range:
      {
        range_calcuration(node, delay->node[2]) ;
      }
      break ;
  }

}

/*
coma_sequence_match_items:
  ',' sequence_match_item
  |
  coma_sequence_match_items ',' sequence_match_item
  ;
  
  sequence_match_item:
  operator_assignment
  |
  inc_or_dec_expression 
  ;
*/

static sva_node *get_sequence_match_items( systemverilog_node *node) {
  sva_node *new_node, *nn, *pnn ;
  systemverilog_node *item ;
   
  new_node = NULL ;
    
  while( node ) {
    named_node *nm ;
    nn = ALLOC_SVA_NODE ; 
    nn->linenum = node->linenum ;
    nn->filename = node->filename ;
    nn->attrib = SVN_none ;
    if( new_node == NULL ) new_node = nn ;
    else pnn->next = nn ;
    nn->origin = node ;      
    /* save origin node for possible future error detection */
    item = node->node[1] ;
    switch(item->type) {
    case SV_operator_assignment:
      nn->nm = item->node[0]->nm ;
      nn->type = SE_match_item_assign ;
      if( item->node[1]->sva_type != SV_assign_operator ) {
        fprintf( 
          stderr, "Error at %d in %s: Functional assignment %s in sequence match item is not supported\n", 
	  item->linenum, item->filename, item->node[1]->name 
        ) ;
        exit(1) ;
      }
      nn->operator = " = " ;
      nn->exp = item->node[2] ;
      break ;
    case SV_inc_or_dec_Identifier:
      nn->nm = item->node[1]->nm ;
      nn->type = SE_match_item_inc_or_dec_identifier ;
      if( item->node[0]->sva_type == SV_inc_operator ) 
        nn->operator = " + 1 " ;
      else
        nn->operator = " - 1 " ;     
      break ;
    case SV_Identifier_inc_or_dec:
      nn->nm = item->node[0]->nm ;
      nn->type = SE_match_item_identifier_inc_or_dec ;
     if( item->node[0]->sva_type == SV_inc_operator ) 
        nn->operator = " + 1 " ;
      else
        nn->operator = " - 1 " ;     
      break ;
    }
    // Store this node in local variable named node to create
    //  store timming
    nm = nn->nm ;
    if( nm->lvar_acc == NULL ) {
      nm->lvar_acc = (sva_node**)calloc( 32, sizeof(sva_node*) ) ;
      nm->lvar_acc_size = 32 ;
      nm->lvar_acc_num = 0 ;
    }
    else if( nm->lvar_acc_num == nm->lvar_acc_size-1 ) {
      nm->lvar_acc = (sva_node**)realloc( nm->lvar_acc, (nm->lvar_acc_size + 32) * sizeof(sva_node*)  ) ; 
      nm->lvar_acc_size += 32 ;
    }
    nm->lvar_acc[nm->lvar_acc_num++] = nn ;
    if( nn->nm->type ==  SV_localvar_name ) {
      nn->nm->match_item_flag = 1 ;
    }
    pnn = nn ;
    node = node->next ;
  }
  return new_node ;
}

/* 
sequence_expr:
  expression_or_dist opt_boolean_abbrev
  <<seq_expression_abbrev>>
  | 
  cycle_delay_range_sequence_expr_s
  <<cycle_delay_range_seq_exprs>>
  | 
  sequence_item 
    opt_cycle_delay_range_sequence_expr_s 
  <<seq_itm_opt_dly_seq>>
  |
  '(' expression_or_dist opt_coma_sequence_match_items ')' 
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
  *  expression_or_dist 'throughout' sequence_expr  *
  expression 'throughout' sequence_expr 
  <<seq_exp_throughout_seq>>
  | 
  sequence_expr 'within' sequence_expr 
  <<seq_seq_within_seq>>
  | 
  clocking_event sequence_expr
  <<seq_clk_seq>>
  ;

*/

static int is_expression( systemverilog_node *node ) {
  switch( node->sva_type ) {
  case SV_expression:
  case SV_par_expression:
  case SV_unary_expression:
  case SV_binary_expression:
  case SV_select_expression:
    return 1 ;
  case SV_identifier:
    switch( node->nm->type ) {
    case SV_sequence_name: return 0 ;
    }
    return 1 ;
  case SV_hieracy_identifier:
  case SV_identifier_singlesell:
  case SV_identifier_rangesell:
  case SV_sys_function_call:
    return 1 ;  
    break ;
  }
  return 0 ;
}

static int compare_expression( 
  systemverilog_node *node1, systemverilog_node *node2
) {
  int i ;
  if( node1 == NULL && node2 == NULL ) return 1 ;
  if( node1 == NULL || node2 == NULL ) return 0 ;
  if( node1->sva_type != node2->sva_type ) return 0 ;
  if( node1->num_node != node2->num_node ) return 0 ;
  if( node1->name != NULL || node2->name != NULL ) {
    if( node1->name == NULL || node2->name == NULL ) return 0 ;
    if( strcmp( node1->name, node2->name ) ) return 0 ;
  }
  if( node1->nm != node2->nm ) return 0 ;
  for( i = 0 ; i < node1->num_node ; i++ ) {
    if( !compare_expression( node1->node[i], node2->node[i] ) ) return 0 ;
  }
  if( node1->clk_negedge != node2->clk_negedge ) return 0 ;
  return 1 ;
}

static systemverilog_node *add2exp_clock_list ( systemverilog_node *node ) {
  systemverilog_node *tmp, *last ;
  if( node == NULL ) return node ;
  if( exp_clock_node == NULL ) { 
     exp_clock_node = node ;
    node->exp_id = label_num++ ;
  }
  else {
    last = tmp =  exp_clock_node ;
    while( tmp ) {
      if( compare_expression( tmp, node ) ) return tmp ;
      last = tmp ;
      tmp = tmp->exp_list ;
    }
    last->exp_list = node ;
    node->exp_id = label_num++ ;
  }
  /* node->clock_node = clock_node ; */
  return node ;
}

static systemverilog_node *add2exp_list ( systemverilog_node *node ) {
  systemverilog_node *tmp, *last ;
  if( node == NULL ) return node ;
  if( node->localvar_access ) {
    node->exp_id = label_num++ ; // this id is a temporary one
    if( exp_lvar_node == NULL ) {
      exp_lvar_node = node ;
    }
    else {
      tmp = exp_lvar_node ;
      while( tmp->exp_list ) tmp = tmp->exp_list ;
      tmp->exp_list = node ;
    }
    return node ;
  }
  if( exp_node == NULL ) { 
    exp_node = node ;
    node->exp_id = label_num++ ;
  }
  else {
    last = tmp = exp_node ;
    while( tmp ) {
      if( compare_expression( tmp, node ) ) return tmp ;
      last = tmp ;
      tmp = tmp->exp_list ;
    }
    last->exp_list = node ;
    node->exp_id = label_num++ ;
  }
  node->clock_node = clock_node ;
  return node ;
}

static systemverilog_node *lookup_exp_list ( systemverilog_node *node ) {
  systemverilog_node *tmp ;
  if( node == NULL ) return NULL ;
  tmp = exp_node ;
  while( tmp ) {
    if( compare_expression( tmp, node ) ) return tmp ;
    tmp = tmp->exp_list ;
  }
  return NULL ;
}

static systemverilog_node *add_sysfunc_block ( systemverilog_node *node ) {
  systemverilog_node *nd ;
  if( node->sysfunc_block ) return node->sysfunc_block ;
  node->sysfunc_block = nd = ALLOC_SV_NODE ;
  nd->sva_type = SV_sysfunc_block ; 
  nd->rose_id = label_num++ ;
  nd->fell_id = label_num++ ;
  nd->past_id = label_num++ ;
  nd->stable_id = label_num++ ;
  nd->sampled_id = label_num++ ;
  nd->clock_node = clock_node ;
  return nd ;
}

static systemverilog_node *add_sysfunc_past_block (
  systemverilog_node *node, int past_num
) {
  systemverilog_node *nd, *pd ;
  // past block is chained
  while( node->sysfunc_past_block ) node = node->sysfunc_past_block ;
  node->sysfunc_past_block = nd = ALLOC_SV_NODE ;
  nd->sva_type = SV_sysfunc_past_block ; 
  nd->past_id = label_num++ ;
  nd->clock_node = clock_node ;
  nd->past_num = past_num ;
  return nd ;
}


static systemverilog_node *add_onehot_node ( systemverilog_node *node, int is_onehot ) {
  systemverilog_node *tmp, *last ;
  
  if( node == NULL ) return node ;
  if( onehot_node == NULL ) { 
    onehot_node = node ;
    node->exp_id = label_num++ ;
  }
  else {
    last = tmp = onehot_node ;
    while( tmp ) {
      last = tmp ;
      tmp = tmp->onehot_list ;
    }
    last->onehot_list = node ;
    node->exp_id = label_num++ ;
  }
  node->clock_node = clock_node ;
  node->is_onehot = is_onehot ;
  return node ;
}

/*
clocking_event:
  '@' Identifier
  |
  '@' '(' event_expression ')'
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
 */
static systemverilog_node *clock_node_gen( systemverilog_node *node ) {
  systemverilog_node *nd, *ev ;
  if( node == NULL ) return node ;
  if( node->num_node == 2 ) {
    // '@' Identifier
    nd = add2exp_clock_list( node->node[1] ) ;
  }
  if( node->num_node == 4 ) {
    ev = node->node[2] ;
    if( ev->sva_type == SV_posedge_event ) {
      nd = add2exp_clock_list( ev->node[1] ) ;
    }
    else {
      if( ev->sva_type == SV_negedge_event ) {
        ev->node[1]->clk_negedge = 1 ;
        nd = add2exp_clock_list( ev->node[1] ) ;
      }
      else {
        nd = add2exp_clock_list( ev ) ;
      }
    }
  }
  return nd ;
}

static void gen_onehot( systemverilog_node *node ) 
{
  int sync_id ;
  int bus_size ;
  int func_id ;
  int carry_id ;
  int fail_id ;
  int onehot_id ;
  int i, j ;
  switch( node->sva_type ) {
  case SV_identifier:
    if( !node->nm ) {
      fprintf( 
        stderr, "Error at %d in %s: Unknown name %s for onehot system function. \n", 
        node->linenum, node->filename, node->name
      ) ;
      exit(1) ;          
    }
    // working here
    switch( node->nm->type ) {
      case SV_port_name:
      case SV_reg_name:
      case SV_net_name:
        if( node->nm->bus_m == 0 && node->nm->bus_n == 0 ) {
	  if( sync_expression ) {
	    sync_id = label_num++ ;
	    func_id = node->exp_id ;
	  }
	  else {
	    sync_id = func_id = node->exp_id ;
	  }
          if( sync_input ) {
	    bus_size = 1 ;
	    fprintf( out, "  wire %s%d ; \n", ARV_WIRE, sync_id ) ;
	    fprintf( out,  "  ARV_DFF_E sync_dff%d ( ", label_num++ ) ;
	    connect_port ( "Clk", clock_node, 1 ) ;
	    fprintf( 
	      out, ".RN(%s), .E((~%s) && %s), ", 
	      ARV_RESET_, ARV_CLEAR, ARV_ENABLE 
	    ) ;
	    fprintf( out, ".D(%s),", node->nm->name ) ;
	    fprintf( out, ".Q(%s%d)", ARV_WIRE, sync_id ) ;
	    fprintf( out, " ) ;\n" ) ;
	    number_of_ff++ ;	  
	  }
  	  else {
	    bus_size = 1 ;
	    fprintf( 
	      out, "  wire %s%d = %s ; \n", ARV_WIRE, 
	      sync_id, node->nm->name  
	    ) ;
	  }
	  if( sync_expression ) {
	    fprintf( out, "  wire %s%d ; \n", ARV_WIRE, func_id ) ;
	    fprintf( out,  "  ARV_DFF_ES #(%s) sync_dff%d ( ", ARV_SYNC_FF_NUM, label_num++ ) ;
	    connect_port ( "Clk", clock_node, 1 ) ;
	    fprintf( 
	      out, ".RN(%s), .E((~%s) && %s), ", 
	      ARV_RESET_, ARV_CLEAR, ARV_ENABLE 
	    ) ;
	    fprintf( out, ".D(%s%d),", ARV_WIRE, sync_id ) ;
	    fprintf( out, ".Q(%s%d)", ARV_WIRE, func_id ) ;
	    fprintf( out, " ) ;\n" ) ;
	    number_of_ff++ ;	  
	  }
	}
        else {
	  if( node->nm->bus_m > node->nm->bus_n ) {
	    bus_size = node->nm->bus_m - node->nm->bus_n + 1 ;
	  }
	  else {
	    bus_size = node->nm->bus_n - node->nm->bus_m + 1 ;
	  }       
	  if( sync_expression ) {
	    func_id = node->exp_id ;
	    onehot_id = label_num++ ;
	  }
	  else {
	    func_id = onehot_id = node->exp_id ;
	  }
	  sync_id = label_num++ ;
	  if( sync_input ) {
	    fprintf( out, 
	      "  reg [%d:%d] %s%d ; \n",
	      node->nm->bus_m, node->nm->bus_n, ARV_WIRE, sync_id
	    ) ;
	    number_of_ff += bus_size ;
	    fprintf( out, "  always @( posedge " ) ;
	    node_out( clock_node ) ;
	    fprintf( out, ") begin\n" ) ;
	    fprintf(
               out, "    %s%d <= %s ;\n",
               ARV_WIRE, sync_id, node->nm->name 
            ) ;
	    fprintf( out, "  end \n" ) ;

	  }
	  else {
	    fprintf( out, 
	      "  wire [%d:%d] %s%d = %s ; \n",
	      node->nm->bus_m, node->nm->bus_n, ARV_WIRE, 
              sync_id, node->nm->name
	    ) ;
	  }
	  for( i = 1 ; i < bus_size ; i++ ) {
	    if( i == 1 ) {
	      carry_id = label_num++ ;
	      fail_id = label_num++ ;
	      fprintf( 
		out, "  wire %s%d = %s%d[0] | %s%d[1] ; // carry \n",
		ARV_WIRE, carry_id, ARV_WIRE, sync_id, ARV_WIRE, sync_id
	      ) ;
	      fprintf( 
		out, "  wire %s%d = %s%d[0] & %s%d[1] ; // fail \n",
		ARV_WIRE, fail_id, ARV_WIRE, sync_id, ARV_WIRE, sync_id
	      ) ;
	      number_of_or++ ;
	      number_of_and++ ;
	    }
	    else {
	      fprintf( 
		out, "  wire %s%d = %s%d | %s%d[%d] ; // carry \n",
		ARV_WIRE, label_num, ARV_WIRE, carry_id, ARV_WIRE, sync_id, i
	      ) ;
	      fprintf( 
		out, "  wire %s%d = %s%d | (%s%d & %s%d[%d]) ; // fail \n",
		ARV_WIRE, label_num+1, ARV_WIRE, fail_id, 
		ARV_WIRE, carry_id, ARV_WIRE, sync_id, i
	      ) ;	      
	      carry_id = label_num++ ;
	      fail_id = label_num++ ;
	      number_of_or += 2 ;
	      number_of_and++ ;
	    }
	  }
	  if( node->is_onehot ) {
	    fprintf( 
	      out, " wire %s%d = %s%d & (~%s%d) ; \n",
	      ARV_WIRE, onehot_id, ARV_WIRE, carry_id, ARV_WIRE, fail_id
	      ) ;
	    number_of_and++ ;
	    number_of_not++ ;
	  }
	  else { // onehot0
	    fprintf( 
	      out, " wire %s%d = ( %s%d & (~%s%d) ) | (~%s%d) ; \n",
	      ARV_WIRE, onehot_id, ARV_WIRE, carry_id, ARV_WIRE, fail_id,
	      ARV_WIRE, carry_id
	      ) ;
	    number_of_and++ ;
	    number_of_or++ ;
	    number_of_not += 2 ;
	  }
	  if( sync_expression ) {
	    fprintf( out, "  wire %s%d ; \n", ARV_WIRE, func_id ) ;
	    fprintf( out,  "  ARV_DFF_ES #(%s) sync_dff%d ( ", ARV_SYNC_FF_NUM, label_num++ ) ;
	    connect_port ( "Clk", clock_node, 1 ) ;
	    fprintf( 
	      out, ".RN(%s), .E((~%s) && %s), ", 
	      ARV_RESET_, ARV_CLEAR, ARV_ENABLE 
	    ) ;
	    fprintf( out, ".D(%s%d),", ARV_WIRE, onehot_id ) ;
	    fprintf( out, ".Q(%s%d)", ARV_WIRE, func_id ) ;
	    fprintf( out, " ) ;\n" ) ;
	    number_of_ff++ ;	  
	    number_of_and++ ;
	    number_of_not++ ;
	  }
	}
	break ;
    default:
      fprintf( 
	stderr, "Error at %d in %s: Inproper type of name %s for onehot function argument is not supported. \n", 
	node->linenum, node->filename, node->node[0]->name
	) ;
      exit(1) ;
      break ;
    }
    break ;
  case SV_identifier_singlesell:
    if( !node->node[0]->nm ) {
      fprintf( 
        stderr, "Error at %d in %s: Unknown name %s for onehot function argument. \n", 
        node->linenum, node->filename, node->node[0]->name
      ) ;
      exit(1) ;          
    }   
    fprintf( 
      stderr, "Error at %d in %s: Partial vector for name %s for onehot function argument is not supported. \n", 
      node->linenum, node->filename, node->node[0]->name
    ) ;
    exit(1) ;     
    break ;
  case SV_identifier_rangesell:
    if( !node->node[0]->nm ) {
      fprintf( 
        stderr, "Error at %d in %s: Unknown name %s for onehot function argument. \n", 
        node->linenum, node->filename, node->node[0]->name
      ) ;
      exit(1) ;          
    }   
    fprintf( 
      stderr, "Error at %d in %s: Partial vector for name %s for onehot function argument is not supported. \n", 
      node->linenum, node->filename, node->node[0]->name
    ) ;
    break ;
    
  case SV_par_expression:
    node->node[1]->is_onehot = node->is_onehot ;
    gen_onehot( node->node[1] ) ;
    break ;
  default:
      fprintf( 
        stderr, "Error at %d in %s: Unknown argument type for onehot system function. \n", 
        node->linenum, node->filename
      ) ;
      exit(1) ;    
    break ;
  }
  
}

static systemverilog_node *expression_analysis( systemverilog_node *node ) {
  if( node == NULL ) return NULL ;
  
  if( use_exp_id_node ) {
    systemverilog_node *tmp = lookup_exp_list( node ) ;
    if( tmp ) return tmp ;
  }
  switch( node->sva_type ) {
  case SV_expression:
  {
    int i ;
    for( i = 0 ; i < node->num_node ; i++ ) {
      node->node[i] = expression_analysis( node->node[i] ) ;
      node->localvar_access |= node->node[i]->localvar_access ;
    }
    return node ;
  }
    break ;
  case SV_par_expression:
    node->node[1] = expression_analysis( node->node[1] ) ;
    node->localvar_access |= node->node[1]->localvar_access ;
    return node ;
    break ;
  case SV_no_compile:
  {
    int i ;
    for( i = 0 ; i < node->num_node ; i++ ) {
      node->node[i] = expression_analysis( node->node[i] ) ;
      node->localvar_access |= node->node[i]->localvar_access ;
    }
    return node ;
  }
    break ;
  case SV_unary_expression:
    node->node[1] = expression_analysis( node->node[1] ) ;
    node->localvar_access |= node->node[1]->localvar_access ;
    return node ;
    break ;
  case  SV_binary_expression:
    node->node[0] = expression_analysis( node->node[0] ) ;
    node->localvar_access |= node->node[0]->localvar_access ;
    node->node[2] = expression_analysis( node->node[2] ) ;  
    node->localvar_access |= node->node[2]->localvar_access ;
    return node ;
    break ;
  case SV_select_expression:
    node->node[0] = expression_analysis( node->node[0] ) ;
    node->localvar_access |= node->node[0]->localvar_access ;
    node->node[2] = expression_analysis( node->node[2] ) ;
    node->localvar_access |= node->node[2]->localvar_access ;
    node->node[4] = expression_analysis( node->node[4] ) ;
    node->localvar_access |= node->node[4]->localvar_access ;
    return node ;
    break ;
  case  SV_identifier:
    if( node->nm ) {
      switch( node->nm->type ) {
      case SV_parameter_name:
	return expression_analysis( node->nm->value ) ;
	break ;
      case SV_arg_name:
	if( node->nm->arg_value ) 
	  return expression_analysis( node->nm->arg_value ) ;
	else if( node->nm->default_arg_value )
	  return expression_analysis( node->nm->default_arg_value ) ;
	break ;
      case SV_localvar_name:
      {
        if( !use_exp_id_node ) {
	  named_node *nm = node->nm ;
	  if( nm->lvar_exp == NULL ) {
	    nm->lvar_exp = (systemverilog_node**)calloc( 32, sizeof(systemverilog_node*) ) ;
	    nm->lvar_exp_size = 32 ;
	    nm->lvar_exp_num = 0 ;
	  }
	  else if( nm->lvar_exp_num == nm->lvar_exp_size-1 ) {
	    nm->lvar_exp = (systemverilog_node**)realloc( nm->lvar_exp, (nm->lvar_exp_size + 32) * sizeof(systemverilog_node*)  ) ; 
	    nm->lvar_exp_size += 32 ;
	  }
	  nm->lvar_exp[nm->lvar_exp_num++] = current_exp_node ;
	  node->localvar_access = 1 ;
        }
	return node ;
      }
	break ;
      case SV_port_name:
      case SV_reg_name:
      case SV_net_name:        
        if( use_exp_id_node && node->exp_id == 0 ) {
          systemverilog_node *s_node = NULL ;
          if( sync_input ) {
            if( node->sync_input_node ) {
	      s_node = node->sync_input_node ;
	    }
	    else { 
	      s_node = node->sync_input_node =
		new_reg_node( node->nm->bus_m, node->nm->bus_n ) ;
	      fprintf( out, "  always @( negedge %s or posedge ", ARV_RESET_ ) ;
	      node_out( clock_node ) ;
	      fprintf( out, ") begin\n" ) ;
	      fprintf( out, "    if( !%s ) begin\n", ARV_RESET_ ) ;
	      fprintf( out, "      %s%d = 0 ;\n", ARV_WIRE, s_node->exp_id ) ;
	      fprintf( out, "    end\n" ) ;
	      fprintf( out, "    else begin \n" ) ;
	      fprintf( out, "      %s%d <= ", ARV_WIRE, s_node->exp_id ) ;
	      fprintf( out, "%s ;\n", node->nm->name ) ;
	      fprintf( out, "    end \n" ) ;	    
	      fprintf( out, "  end \n" ) ;
	    }	    
          }
	  if( sync_expression == 0 ) {
	    if( s_node ) node->exp_id = s_node->exp_id ;
	  }
	  else {
	    node->exp_id = label_num++ ;
	    if( node->nm->bus_m == 0 && node->nm->bus_n == 0 ) { 
	      fprintf( out, "  wire %s%d ; \n", ARV_WIRE, node->exp_id ) ;
	      fprintf( out,  "  ARV_DFF_ES #(%s) sync_dff%d ( ", ARV_SYNC_FF_NUM, label_num++ ) ;
	      connect_port ( "Clk", clock_node, 1 ) ;
	      fprintf( 
		out, ".RN(%s), .E((~%s) && %s), ", ARV_RESET_, ARV_CLEAR, ARV_ENABLE 
		) ;
	      if( s_node ) fprintf( out, ".D(%s%d),", ARV_WIRE, s_node->exp_id ) ;
	      else fprintf( out, ".D(%s),", node->nm->name ) ;
	      fprintf( out, ".Q(%s%d)", ARV_WIRE, node->exp_id ) ;
	      fprintf( out, " ) ;\n" ) ;
	      number_of_ff++ ;
	    }
	    else {
	      int wd ;
	      if( node->nm->bus_m > node->nm->bus_n ) 
		wd = (  node->nm->bus_m - node->nm->bus_n + 1 ) ;
	      else
		wd = (  node->nm->bus_n - node->nm->bus_m + 1 ) ;
  	      fprintf( out, 
	        "  wire [%d:%d] %s%d ; \n",
	        node->nm->bus_m, node->nm->bus_n, ARV_WIRE, node->exp_id
	      ) ;
	      fprintf( out,  "  ARV_DFF_ESW #(%s,%d) sync_dff%d ( ", ARV_SYNC_FF_NUM, wd, label_num++ ) ;
	      connect_port ( "Clk", clock_node, 1 ) ;
	      fprintf( 
		out, ".RN(%s), .E((~%s) && %s), ", ARV_RESET_, ARV_CLEAR, ARV_ENABLE 
		) ;
	      if( s_node ) fprintf( out, ".D(%s%d),", ARV_WIRE, s_node->exp_id ) ;
	      else fprintf( out, ".D(%s),", node->nm->name ) ;
	      fprintf( out, ".Q(%s%d)", ARV_WIRE, node->exp_id ) ;
	      fprintf( out, " ) ;\n" ) ;

	      number_of_ff += wd * sync_ff_num ;

	    }
	  }
        }
      }
    }
    return node ;
    break ;
  case SV_hieracy_identifier:
    return node ;
    break ;
  case SV_identifier_singlesell:
    return node ;
    break ;
  case SV_identifier_rangesell:
    return node ;
    break ;
  case SV_sys_function_call:
  {
    int id ;
    systemverilog_node *nd, *nn ;
    switch ( node->sysfunc ) {
    case sys_isunknown:
      nd = ALLOC_SV_NODE ;
      nd->name = "0" ;
      return nd ;
      break ;
    case sys_onehot:
    case sys_onehot0:
      if( use_exp_id_node ) return node ;
      // working here
      nd = add_onehot_node( node->node[2], node->sysfunc == sys_onehot ) ;
      return nd ;
      break ;
    case sys_countones:
      // not supported
      fprintf( 
        stderr, "Error at %d in %s: countones system function is not supported. \n", 
        node->linenum, node->filename
      ) ;
      exit(1) ;      
      break ;
    case sys_rose:
    case sys_fell:
    case sys_stable:
    case sys_sampled:
      if( use_exp_id_node ) return node ;
      nd = add2exp_list( node->node[2] ) ;
      nd = add_sysfunc_block( nd ) ;
      nn = ALLOC_SV_NODE ;
      nn->name = calloc(1, strlen( ARV_WIRE ) + 10 ) ;
      switch( node->sysfunc ) {
      case sys_rose:
	id = nd->rose_id ;
	break ;
      case sys_fell:
	id = nd->fell_id ;
	break ;
      case sys_stable:
	id = nd->stable_id ;
	break ;
      case sys_sampled:
	id = nd->sampled_id ;
	break ;
      } /* end of inside switch( node->sysfunc ) */
      sprintf( nn->name, "%s%d", ARV_WIRE, id ) ;
      nn->no_sync = 1 ;
      return nn ;
      break ;
    case sys_past:
    {
      systemverilog_node *pn, *arg0, *arg1 ;
      int past_num = 1 ;
      pn = node->node[2] ;
      arg0 = arg1 = NULL ;
      /*
      expression_list_with_nuls:
      * empty *
      |
      expression_list_with_nuls ',' expression
      |
      expression
      |
      expression_list_with_nuls ','
      */     
      if( pn && pn->sva_type == SV_no_compile ) {
        switch( pn->num_node ) {
        case 2:
          arg0 = pn->node[0] ;
          pn = NULL ;
          break ;
	case 3:
	  arg0 = pn->node[0] ;
	  pn = pn->node[2] ;
	  break ;
	}
      }
      else {
        arg0 = pn ;
        pn = NULL ;
      }
      if( (pn && pn->sva_type == SV_no_compile) || arg0 == NULL ) {
	fprintf( 
          stderr, "Error at %d in %s: $past function only support one or two arguments\n", 
          node->linenum, node->filename
        ) ;
        exit(1) ;        
      }
      else {
	arg1 = pn ;
      }
      if( arg1 ) {
        past_num = get_constant( arg1 ) ;
        if( past_num == 0 ) {
	  fprintf( 
            stderr, "Error at %d in %s: Illegal 2nd argument for $past function \n", 
            node->linenum, node->filename
          ) ;
          exit(1) ;        
        }
      }
      nd = add2exp_list( arg0 ) ;
      nd = add_sysfunc_past_block( nd, past_num ) ;
      nn = ALLOC_SV_NODE ;
      nn->name = calloc(1, strlen( ARV_WIRE ) + 10 ) ;      
      sprintf( nn->name, "%s%d", ARV_WIRE, nd->past_id ) ;
      nn->no_sync = 1 ;
      return nn ;
    }
    break ;
    } /* end of outside switch( node->sysfunc ) */
    break ;
  } /* end of block under case SV_sys_function_call: */
 
  } /* end of switch( node->sva_type ) */
  return node ;
}


static sva_node *sequence_expr( systemverilog_node *node) {
  sva_node *new_node = NULL ;
  if( is_expression( node ) ) {
    new_node =  ALLOC_SVA_NODE ;
    new_node->linenum = node->linenum ;
    new_node->filename = node->filename ;
    current_exp_node = node ;
    new_node->exp = expression_analysis( node ) ;
    if( new_node->exp->exp_id == 0 ) {
       new_node->exp = add2exp_list( new_node->exp ) ;
    }      
    new_node->type = SE_expression ;
    new_node->attrib = SVN_filter ;
    return new_node ;
  }
  switch( node->sva_type) {
    case SV_par_sequence_expr:
    {
      return sequence_expr( node->node[1] ) ;
    }
    case SV_identifier:
    {
      if( node->nm->type == SV_sequence_name ) {
        // working here sva->nm->value to be compiled
	  new_node = 
            sequence_dcl( 
              node->nm->value, NULL, NULL
            ) ;     
      }
      else {
	new_node =  ALLOC_SVA_NODE ;
	new_node->linenum = node->linenum ;
	new_node->filename = node->filename ;
	new_node->type = SE_sequence_item ;
	current_exp_node = node ;      
	new_node->exp = expression_analysis( node ) ;
	if( new_node->exp->exp_id == 0 ) {
	  new_node->exp = add2exp_list( new_node->exp ) ;
	}          
	new_node->attrib = SVN_filter ;
      }
    }
    break ;
    case SV_sequence_expr:
    {
      if( node->node[0] ) {
        new_node =  ALLOC_SVA_NODE ;
	new_node->linenum = node->linenum ;
	new_node->filename = node->filename ;
        new_node->type = SE_delay ;
        delay_calculation( new_node, node->node[0] ) ;
        new_node->next = sequence_expr( node->node[1] ) ;       
      }
      else {
        new_node = sequence_expr( node->node[1] ) ;
      }
      if( node->node[2] ) {
        sva_node *nn = new_node ;
        while( nn->next ) nn = nn->next ;
        nn->next = sequence_expr( node->node[2] ) ;
      }
    }
    break ;
    case SV_cycle_delay_range_sequence_item:
    {
      sva_node *nn, *pnn ;
      while( node ) {
        nn = ALLOC_SVA_NODE ; 
	nn->linenum = node->linenum ;
	nn->filename = node->filename ;
        if( new_node == NULL ) new_node = nn ;
        else pnn->next = nn ;
        nn->type = SE_delay ;
        delay_calculation( nn, node->node[0] ) ;
        pnn = nn->next = sequence_expr( node->node[1] ) ;
        while( pnn->next ) pnn = pnn->next ;
        node = node->next ;
      }
    }
    break ;
    case SV_seq_expression_abbrev:
      {
        new_node = ALLOC_SVA_NODE ; 
	new_node->linenum = node->linenum ;
	new_node->filename = node->filename ;
        current_exp_node = node->node[0] ;
        new_node->exp = expression_analysis( node->node[0] ) ;
        if( new_node->exp->exp_id == 0 ) {        
          new_node->exp = add2exp_list( new_node->exp ) ;
        }
        if( node->node[1] ) {
          /* setup repeat node */
          set_boolean_abbrev( new_node, node->node[1] ) ;
        }
        else {
          new_node->type = SE_expression ;
          new_node->attrib = SVN_filter ;
        }
      }
      break ;
    case SV_seq_cycle_dly_seq_exprs:
      {
        sva_node *nn, *pnn ;
        systemverilog_node *range ;
        
        while( node ) {
          nn = ALLOC_SVA_NODE ; 
	  nn->linenum = node->linenum ;
	  nn->filename = node->filename ;
          if( new_node == NULL ) new_node = nn ;
          else pnn->next = nn ;
          nn->type = SE_delay ;
          range = node->node[0] ;
          delay_calculation( nn, range ) ;
          if( nn->attrib == SVN_branch ) nn->attrib = SVN_brfilter ;
          if( is_expression( node->node[1] ) ) {
            current_exp_node = node->node[1] ;
            nn->exp = expression_analysis( node->node[1] ) ;
            if( nn->exp->exp_id == 0 ) {
              nn->exp = add2exp_list( nn->exp ) ;
            }     
          }
          else {
            current_exp_node = node->node[1]->node[1] ;
            nn->exp = expression_analysis( node->node[1]->node[1] ) ; 
            if( nn->exp->exp_id == 0 ) {
              nn->exp = add2exp_list( nn->exp ) ;
            }         
	    if( node->node[1]->node[2] ) {
 	      sva_node *n = nn ;
	      while( n->next ) n = n->next ;
   	      n->next = get_sequence_match_items( node->node[1]->node[2] ) ;
	      n->resource = RCS_free ;
            }   
          }
          pnn = nn ;
          node = node->next ;
        }
      }
      break ;
    case SV_cycle_delay_range_sequence_expr:
    {
      new_node =  ALLOC_SVA_NODE ;
      new_node->linenum = node->linenum ;
      new_node->filename = node->filename ;
      new_node->type = SE_delay ;
      delay_calculation( new_node, node->node[0] ) ;
      new_node->next = sequence_expr( node->node[1] ) ;
    }
      break ;
    case SV_seq_seq_itm_opt_dly_seq:
      {
        new_node =  ALLOC_SVA_NODE ;
	new_node->linenum = node->linenum ;
	new_node->filename = node->filename ;
        new_node->type = SE_sequence_item ;
	new_node->attrib = SVN_filter ;
        /* first node is sequence_item */
        if( is_expression( node->node[0] ) ) {
          current_exp_node = node->node[0] ;
          new_node->exp = expression_analysis( node->node[0] ) ;
          if( new_node->exp->exp_id == 0 ) {
            new_node->exp = add2exp_list( new_node->exp ) ;
          }
        }
        else { /* '(' exp coma_sequence_match_items ')' */
          current_exp_node = node->node[0]->node[1] ;
          new_node->exp = expression_analysis( node->node[0]->node[1] ) ; 
          if( new_node->exp->exp_id == 0 ) {
            new_node->exp = add2exp_list( new_node->exp ) ;
          }
          if( node->node[0]->node[2] ) {
	    sva_node *n = new_node ;
	    while( n->next ) n = n->next ;
	    n->next = get_sequence_match_items( node->node[0]->node[2] ) ;
	    n->next->resource = RCS_free ;
          }   
        }
        /* second node is opt_cycle_delay_range_sequence_expr_s */
        if( node->node[1] )  {
          new_node->next = sequence_expr(node->node[1]) ;
	}
      }
      break ;
    case SV_seq_par_exp_match_par_abbrev:
      {
        new_node = ALLOC_SVA_NODE ;
	new_node->linenum = node->linenum ;
	new_node->filename = node->filename ;
        current_exp_node = node->node[1] ;
	new_node->exp = expression_analysis( node->node[1] ) ;  
        if( new_node->exp->exp_id == 0 ) {
          new_node->exp = add2exp_list( new_node->exp ) ;
        }
	  /* expression_or_dist */
        if( node->node[2] ) {  /* opt_seq_match_items */
	  sva_node *n = new_node ;
	  while( n->next ) n = n->next ;
	  n->next = get_sequence_match_items( node->node[2] ) ;
	  n->next->resource = RCS_free ;
        } 
        if( node->node[4] ) {
          /* setup repeat node */
          set_boolean_abbrev( new_node, node->node[4] ) ;
        }
        else { 
          /* just '(' expression_or_dist opt_coma_sequence_match_items ')' */
          new_node->type = SE_expression ;
          new_node->attrib = SVN_filter ;
        }
      }
      break ;
    case SV_seq_inst_abbrev:
      { 
        /* 
           node -> sequence_instance opt_sequence_abbrev
           sequence_instance : Identifier opt_pars_actual_arg_list
           opt_pars_actual_arg_list :  |  '(' opt_actual_arg_list ')'
           opt_actual_arg_llist: empty   |
              actual_arg_list
              |
              formal_arg_list
           actual_arg_list: actual_arg_expr  |
               actual_arg_list ',' actual_arg_expr  
           actual_arg_expr: expression
          formal_arg_list: formal_arg |
            formal_arg_list ',' formal_arg
          formal_arg: '.' Identifier '(' actual_arg_expr ')'
	 */
	new_node = ALLOC_SVA_NODE ;
	new_node->linenum = node->linenum ;
	new_node->filename = node->filename ;
	new_node->type = SE_sequence_instance ;
	new_node->nm = node->node[0]->node[0]->nm ;
	if( new_node->nm == NULL || new_node->nm->type != SV_sequence_name ) {
	  fprintf( 
	    stderr, "Error at %d in %s:  Sequence name %s not found\n", 
            node->linenum, node->filename, node->node[0]->name
	  ) ;
	  exit(1) ;
	}
	// handling actual argument list 
	if( node->node[0]->node[1] && node->node[0]->node[1]->node[1] ) {
	  sva_node *arg_node, *pn ;
	  systemverilog_node *arg = node->node[0]->node[1]->node[1] ;
	  pn = NULL ;
	  if( arg->sva_type == SV_formal_arg || 
	      arg->sva_type ==  SV_formal_arg_list 
	    ) 
	  {
	    while( arg ) {
	      arg_node = ALLOC_SVA_NODE ;
	      arg_node->linenum = arg->linenum ;
	      arg_node->filename = arg->filename ;
	      arg_node->next = pn ;
	      pn = arg_node ;	      
	      switch( arg->sva_type ) {
	      case SV_formal_arg:
		pn->nm = arg->node[1]->nm ;
		pn->exp = arg->node[3] ;
		arg = NULL ;
		break ;
	      case SV_formal_arg_list:
	        pn->nm = arg->node[2]->node[1]->nm ;
	        pn->exp = arg->node[2]->node[3] ;
	        arg = arg->node[0] ; 
	      }
	    }
	    new_node->arg_node_a = arg_node ;
	  }
	  else {
	    while( arg ) {
	      arg_node = ALLOC_SVA_NODE ;
	      arg_node->linenum = arg->linenum ;
	      arg_node->filename = arg->filename ;
	      arg_node->next = pn ;
	      pn = arg_node ;	      
	      switch( arg->sva_type ) {
	      case SV_actual_arg_list:
		pn->exp = arg->node[2] ;
		arg = arg->node[0] ; 
		break ;
	      default: // single expression case
		pn->exp = arg ;
		arg = NULL ;
		break ;
	      }
	    }
	    new_node->arg_node_b = arg_node ;
	  }
	  new_node->next = 
            sequence_dcl( 
              new_node->nm->value, new_node->arg_node_a, new_node->arg_node_b
            ) ;
          new_node->attrib = new_node->node_a->attrib ;
          new_node->resource = new_node->node_a->resource ;          
	  // handling opt boolean_abbrev
	  if( node->node[1] ) {
	    sva_node *inst = new_node ;
	    new_node = ALLOC_SVA_NODE ;
	    new_node->linenum = node->linenum ;
	    new_node->filename = node->filename ;
            new_node->node_a = inst ;
	    set_boolean_abbrev(new_node, node->node[1]) ;
	  }
	}
      }
      break ;
      
    /* 
      '(' sequence_expr opt_coma_sequence_match_items ')' opt_sequence_abbrev
    */
    case SV_seq_par_seq_match_par_abbrev:
      {
        if( !node->node[2] && !node->node[4] ) {
          new_node = sequence_expr( node->node[1] ) ;
        }
        else {
	  new_node = ALLOC_SVA_NODE ;
	  new_node->linenum = node->linenum ;
	  new_node->filename = node->filename ;
	  new_node->next = sequence_expr( node->node[1] ) ;  /* seq_expr */
	  if( node->node[2] ) {  /* opt_seq_match_items */
	    sva_node *n = new_node ;
	    while( n->next ) n = n->next ;
	    n->next = get_sequence_match_items( node->node[2] ) ;
	    n->next->resource = RCS_free ;
	  }
	  new_node->type = SE_sequence_expr ;
	  if( node->node[4] ) {
	    /* setup repeat node */
	    sva_node *expr = new_node ;
	    new_node = ALLOC_SVA_NODE ;
	    new_node->linenum = node->node[4]->linenum ;
	    new_node->filename = node->node[4]->filename ;
	    new_node->node_a = expr ;
	    set_boolean_abbrev( new_node, node->node[4] ) ;          
	  }
        }
      }
      break ;
    case SV_seq_seq_and_seq:
    {
      new_node = ALLOC_SVA_NODE ;
      new_node->linenum = node->linenum ;
      new_node->filename = node->filename ;
      new_node->type = SE_and ;
      new_node->node_a = sequence_expr( node->node[0] ) ;
      new_node->node_b = sequence_expr( node->node[2] ) ;
      new_node->resource = RCS_single ;
      new_node->attrib = SVN_branch ;
    }
      break ;
    case SV_seq_seq_intersect_seq:
    {
      new_node = ALLOC_SVA_NODE ;
      new_node->linenum = node->linenum ;
      new_node->filename = node->filename ;
      new_node->type = SE_intersect ;
      new_node->node_a = sequence_expr( node->node[0] ) ;
      new_node->node_b = sequence_expr( node->node[2] ) ;
      new_node->resource = RCS_single ;
      new_node->attrib = SVN_branch ;
    }
      break ;
    case SV_seq_seq_or_seq:
    {
      new_node = ALLOC_SVA_NODE ;
      new_node->linenum = node->linenum ;
      new_node->filename = node->filename ;
      new_node->type = SE_or ;
      new_node->node_a = sequence_expr( node->node[0] ) ;
      new_node->node_b = sequence_expr( node->node[2] ) ;
      new_node->resource = RCS_single ;
      new_node->attrib = SVN_branch ;
    }
      break ;
    case SV_seq_first_match:
    {
      new_node = ALLOC_SVA_NODE ;
      new_node->linenum = node->linenum ;
      new_node->filename = node->filename ;
      new_node->type = SE_first_match ;
      new_node->node_a = sequence_expr( node->node[2] ) ;
      new_node->resource = RCS_single ;
      if( node->node[3] ) {  /* opt_seq_match_items */
	sva_node *n = new_node ;
	while( n->next ) n = n->next ;
	n->next = get_sequence_match_items( node->node[3] ) ;
	n->next->resource = RCS_free ;
      } 
    }
      break ;
    case SV_seq_exp_throughout_seq:
    {
      new_node = ALLOC_SVA_NODE ;
      new_node->linenum = node->linenum ;
      new_node->filename = node->filename ;
      new_node->type = SE_throughout ;
      current_exp_node = node->node[0] ;
      new_node->exp = expression_analysis( node->node[0] ) ;
      if( new_node->exp->exp_id == 0 ) {
         new_node->exp = add2exp_list( new_node->exp ) ;
      }         
      new_node->node_a = sequence_expr( node->node[2] ) ;
      new_node->resource = RCS_single ;
    }
      break ;
    case SV_seq_seq_within_seq:
    {
      new_node = ALLOC_SVA_NODE ;
      new_node->linenum = node->linenum ;
      new_node->filename = node->filename ;
      new_node->type = SE_within ;
      new_node->node_a = sequence_expr( node->node[0] ) ;
      new_node->node_b = sequence_expr( node->node[2] ) ;
      new_node->resource = RCS_single ;
    }      
    break ;
    case SV_seq_clk_seq:
    {
      new_node = ALLOC_SVA_NODE ;
      new_node->linenum = node->linenum ;
      new_node->filename = node->filename ;
      new_node->type = SE_clock ;
      new_node->clock = clock_node = clock_node_gen( node->node[0] ) ;
      new_node->next = sequence_expr( node->node[2] ) ;
      new_node->attrib = new_node->node_a->attrib ;
      new_node->resource = new_node->node_a->resource ;          
    }
    break ;
    default:
    {
      fprintf( 
        stderr, "Error at %d in %s: Unknown type:%d\n", 
	node->linenum, node->filename, node->sva_type 
      ) ;
      exit(1) ;
    }
  }
  
  return new_node ;
  
}

/*
property_expr:
  sequence_expr
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
  property_instance
  | 
  clocking_event property_expr
  <<clk_property>>
  ;
*/

static void set_actual_args( sva_node *new_node, systemverilog_node *arg ) {
  sva_node *arg_node, *pn ;
  pn = NULL ;
  if( arg->sva_type == SV_formal_arg || 
      arg->sva_type ==  SV_formal_arg_list 
    ) 
  {
    while( arg ) {
      arg_node = ALLOC_SVA_NODE ;
      arg_node->linenum = arg->linenum ;
      arg_node->filename = arg->filename ;
      arg_node->next = pn ;
      pn = arg_node ;	      
      switch( arg->sva_type ) {
      case SV_formal_arg:
	pn->nm = arg->node[1]->nm ;
	pn->exp = arg->node[3] ;
	arg = NULL ;
	break ;
      case SV_formal_arg_list:
	pn->nm = arg->node[2]->node[1]->nm ;
	pn->exp = arg->node[2]->node[3] ;
	arg = arg->node[0] ; 
      }
    }
    new_node->arg_node_a = arg_node ;
  }
  else {
    while( arg ) {
      arg_node = ALLOC_SVA_NODE ;
      arg_node->linenum = arg->linenum ;
      arg_node->filename = arg->filename ;
      arg_node->next = pn ;
      pn = arg_node ;	      
      switch( arg->sva_type ) {
      case SV_actual_arg_list:
	pn->exp = arg->node[2] ;
	arg = arg->node[0] ; 
	break ;
      default: // single expression case
	pn->exp = arg ;
	arg = NULL ;
	break ;
      }
    }
    new_node->arg_node_b = arg_node ;
  }
}

int is_prop_sequence( systemverilog_node *node ) {
  if( node == NULL ) return 0 ;
  switch( node->sva_type) {
    case SV_sequence_expr:
    case SV_par_sequence_expr:
    case SV_cycle_delay_range_sequence_item:
    case SV_seq_expression_abbrev:
    case SV_seq_cycle_dly_seq_exprs:
    case SV_seq_seq_itm_opt_dly_seq:
    case SV_seq_par_exp_match_par_abbrev:
    case SV_seq_inst_abbrev:
    case SV_seq_par_seq_match_par_abbrev:
    case SV_seq_seq_and_seq:
    case SV_seq_seq_intersect_seq:
    case SV_seq_seq_or_seq:
    case SV_seq_first_match:
    case SV_seq_exp_throughout_seq:
    case SV_seq_seq_within_seq:
    case SV_seq_clk_seq:
    case SV_cycle_delay_range_sequence_expr:
      return 1 ;
    break ;
    case SV_par_property_par:
    {
      return is_prop_sequence( node->node[1] ) ;
    }
    break ;
    case SV_not_property:
    case SV_prop_or_prop:
    case SV_prop_and_prop:
    case SV_seq_ovi_prop:
    case SV_seq_novi_prop:
    case SV_if_else_prop:
    case SV_clk_property:
    case SV_par_property_instance:
    case SV_property_instance:
    break ;
    default:
    break ;
  }
  
  return 0 ;
  
}

static sva_node* property_expr( systemverilog_node *node, int invert, int sub_prop ) {
  sva_node *tt ;
  sva_node *new_node = NULL ;
 
  if( node == NULL ) return NULL ;
  
  switch( node->sva_type) {
    case SV_sequence_expr:
    case SV_par_sequence_expr:
    case SV_cycle_delay_range_sequence_item:
    case SV_seq_expression_abbrev:
    case SV_seq_cycle_dly_seq_exprs:
    case SV_seq_seq_itm_opt_dly_seq:
    case SV_seq_par_exp_match_par_abbrev:
    case SV_seq_inst_abbrev:
    case SV_seq_par_seq_match_par_abbrev:
    case SV_seq_seq_and_seq:
    case SV_seq_seq_intersect_seq:
    case SV_seq_seq_or_seq:
    case SV_seq_first_match:
    case SV_seq_exp_throughout_seq:
    case SV_seq_seq_within_seq:
    case SV_seq_clk_seq:
    case SV_cycle_delay_range_sequence_expr:
      if( sub_prop ) {
        return sequence_expr( node ) ;
      } 
      else
      {
	new_node = ALLOC_SVA_NODE ;
	new_node->linenum = node->linenum ;
	new_node->filename = node->filename ;
	new_node->type = PR_seq ;
	new_node->node_a = sequence_expr( node ) ; 
	if( !is_simple_delay( new_node->node_a, 1 ) ) {
	  new_node->resource = RCS_single ;
	}
      }
    break ;
    case SV_par_property_par:
    {
      return property_expr( node->node[1], invert, 1 ) ;
    }
    break ;
    case SV_not_property:
    {
      new_node = ALLOC_SVA_NODE ;
      new_node->linenum = node->linenum ;
      new_node->filename = node->filename ;
      new_node->type = PR_not ;
      if( is_prop_sequence( node->node[1] ) ) {
        new_node->node_a = property_expr( node->node[1], 1, 0 ) ;
      }
      else {
        new_node->node_a = property_expr( node->node[1], 1, 1 ) ;
      }
      new_node->resource = RCS_single ;
      new_node->attrib = SVN_branch ;
    }
    break ;
    case SV_prop_or_prop:
    {
      new_node = ALLOC_SVA_NODE ;
      new_node->linenum = node->linenum ;
      new_node->filename = node->filename ;
      new_node->type = PR_or ;
      new_node->node_a = property_expr( node->node[0], 0, 1 ) ;
      new_node->node_b = property_expr( node->node[2], 0, 1 ) ;
      new_node->node_a->sub_property = 1 ;
      new_node->node_b->sub_property = 1 ;
      new_node->resource = RCS_single ;
      new_node->attrib = SVN_branch ;
    }
    break ;
    case SV_prop_and_prop:
    {
      new_node = ALLOC_SVA_NODE ;
      new_node->linenum = node->linenum ;
      new_node->filename = node->filename ;
      new_node->type = PR_and ;
      new_node->node_a = property_expr( node->node[0], 0, 1 ) ;
      new_node->node_b = property_expr( node->node[2], 0, 1 ) ;
      new_node->node_a->sub_property = 1 ;
      new_node->node_b->sub_property = 1 ;
      new_node->resource = RCS_single ;
      new_node->attrib = SVN_branch ;
    }
    break ;
    case SV_seq_ovi_prop:
    {
      sva_node *t, *tt ;
      tt = ALLOC_SVA_NODE ;
      tt->linenum = node->linenum ;
      tt->filename = node->filename ;
      tt->type = PR_overlap_implication ;
      tt->resource = RCS_single ;
      tt->invert = invert ;
      new_node = t = property_expr( node->node[0], 0, 1 ) ;
      if( is_simple_delay( new_node, 1 ) ) {
        new_node->error_check = 1 ;
        tt->antece_zero = 1 ;
      }
      else new_node->initial_check = 1 ;
      while( t->next ) {
        t = t->next ;
      }
      t->next = tt ;
      if( new_node->type == SE_expression ) 
        new_node->attrib = SVN_branch ;
      tt->node_a = property_expr( node->node[2], 0, 1 ) ;
    }
    break ;
    case SV_seq_novi_prop:
    {
      sva_node *t, *tt ;
      tt = ALLOC_SVA_NODE ;
      tt->linenum = node->linenum ;
      tt->filename = node->filename ;
      tt->type = PR_non_overlap_implication ;
      tt->resource = RCS_single ;
      tt->invert = invert ;
      new_node = t = property_expr( node->node[0], 0, 1 ) ;
      if( is_simple_delay( new_node, 1 ) ) {
        new_node->error_check = 1 ;
        tt->antece_zero = 1 ;
      }
      else new_node->initial_check = 1 ;
      while( t->next ) {
        t = t->next ;
      }
      t->next = tt ;
      if( new_node->type == SE_expression ) 
        new_node->attrib = SVN_branch ;
      tt->node_a = property_expr( node->node[2], 0, 1 ) ;
    }
    break ;
    case SV_if_else_prop:
    {
      new_node = ALLOC_SVA_NODE ;
      new_node->linenum = node->linenum ;
      new_node->filename = node->filename ;
      new_node->type = PR_if_else_property ;
      new_node->exp =  add2exp_list( node->node[2] ) ;
      new_node->node_a = property_expr( node->node[4], 0, 0 ) ;
      if( node->node[5] ) 
        new_node->node_b = property_expr( node->node[5]->node[1], 0, 0 ) ;
      else
        new_node->node_b = NULL ;
    }
    break ;
    case SV_clk_property:
    {
      new_node = ALLOC_SVA_NODE ;
      new_node->linenum = node->linenum ;
      new_node->filename = node->filename ;
      new_node->type = PR_clock_property ;
      new_node->clock = clock_node = clock_node_gen( node->node[0] ) ;
      new_node->next = property_expr( node->node[1], 0, 0 ) ;
    }
    break ;
    case SV_par_property_instance:
    {
      if( node->node[1]->nm == NULL ) {
        fprintf( 
          stderr, "Property name %s not found\n",
          node->node[0]->name 
        ) ;
        error_count++ ;
      }
      else {
        new_node = ALLOC_SVA_NODE ;
	new_node->linenum = node->linenum ;
	new_node->filename = node->filename ;
        new_node->type = PR_property_instance ;
        new_node->nm = node->node[1]->nm ;
	if( node->node[2] && node->node[2]->node[1] ) {
	  systemverilog_node *arg = node->node[2]->node[1] ;
	  set_actual_args( new_node, arg ) ;
	}
	new_node->next = 
	  property_dcl(
	    new_node->nm->value, new_node->arg_node_a, new_node->arg_node_b
	  ) ;
      }    
      
    }
    case SV_property_instance:
    {
      if( node->node[0]->nm == NULL ) {
        fprintf( 
          stderr, "Property name %s not found\n",
          node->node[0]->name 
        ) ;
        error_count++ ;
      }
      else {
        new_node = ALLOC_SVA_NODE ;
	new_node->linenum = node->linenum ;
	new_node->filename = node->filename ;
        new_node->type = PR_property_instance ;
        new_node->nm = node->node[0]->nm ;
	if( node->node[1] && node->node[1]->node[1] ) {
	  systemverilog_node *arg = node->node[1]->node[1] ;
	  set_actual_args( new_node, arg ) ;
	}
	new_node->next = 
	  property_dcl(
	    new_node->nm->value, new_node->arg_node_a, new_node->arg_node_b
	  ) ;
      }
    }
    break ;
    default:
    {
       fprintf( 
         stderr, "Unknown flag %d for property\n", node->sva_type
       ) ;
       error_count++ ;
    }
    break ;
  }
  
  return new_node ;
  
}

static sva_node *gen_arg_list(  systemverilog_node *node ) {
  // list_of_formals: 
  //     formal_list_item
  //   | list_of_formals ',' formal_list_item
  // formal_list_item:
  //   Identifier opt_assign_actual_arg_expr
  // Note that the arg is identified from the last here.
  sva_node *arg_node = NULL ;
  sva_node *pn, *anode ;
  systemverilog_node *ag ;
  while( node ) {
    anode = ALLOC_SVA_NODE ;
    anode->linenum = node->linenum ;
    anode->filename = node->filename ;
    if( arg_node == NULL ) arg_node = anode ;
    else pn->next = anode ;
    pn = anode ;
    if( node->num_node == 3 ) {
      ag = node->node[0] ;
      node = node->node[2] ;
    }
    else {
      ag = node ;
      node = NULL ;
    }
    pn->nm = ag->node[0]->nm ;
  }
  return arg_node ;
}

static sva_node *gen_var_list ( systemverilog_node *node ) {
  sva_node *var_node = NULL ;
  sva_node *pn, *anode ;
  systemverilog_node *var_org, *var, *dtype ;
  while( node ) {
    var = node->node[1] ;
    dtype = node->node[0] ;
    while( var ) {
      if( var->node[1] != NULL ) {
        fprintf( 
          stderr, 
          "Error at %d in %s: Local variable (%s) with dimention is not supported", 
	  var->linenum, var->filename, var->name
	) ;
	exit(1) ;
      }
      anode = ALLOC_SVA_NODE ;
      anode->linenum = node->linenum ;
      anode->filename = node->filename ;
      if( var_node == NULL ) var_node = anode;
      else pn->next = anode ;
      pn = anode ;
      pn->nm = var->node[0]->nm ;
      pn->data_type = dtype ;
      var = var->next ;
    } 
    node = node->next ;
  }
  return var_node ;
}

static int find_var_use( named_node *nm, sva_node *sva, int depth ) {
  sva_node *found = NULL ;

  while( sva ) {
  switch( sva->type ) {
  case SE_expression:
    if( sva->exp->localvar_access ) {
      if( find_lvar_expression( nm, sva->exp ) ) return 1 ;
    }
    break ;
  case SE_delay:
    if( sva->exp && sva->exp->localvar_access ) {
      if( find_lvar_expression( nm, sva->exp ) ) return 1 ;
    }
    break ;
  case SE_and:
  case SE_or:
  case SE_intersect:
  case SE_within:
    if( find_var_use( nm, sva->node_a, 1 ) || 
	find_var_use( nm, sva->node_b, 1 )    )
    {
      return 1 ;
    }
    break ;
  case SE_throughout:
    if( (sva->exp->localvar_access && find_lvar_expression( nm, sva->exp )) ||
	find_var_use( nm, sva->node_a, 1 )  )
    {
      return 1 ;
    }
    break ;
  case SE_first_match:
    if( find_var_use( nm, sva->node_a, 1 ) ) return 1 ;
    break ;
  case SE_clock:
    //if( find_var_use( nm, sva->node_a ) ) return 1 ;
    break ;
  case SE_consective_repetition:
    if( sva->exp && sva->exp->localvar_access && 
	find_lvar_expression( nm, sva->exp )       
      ) return 1 ;
    if( sva->node_a && find_var_use( nm, sva->node_a, 1 ) )
      return 1 ;
    break ;
  case SE_goto_repetition:
    if( sva->exp && sva->exp->localvar_access && 
	find_lvar_expression( nm, sva->exp )       
      ) return 1 ;
    break ;
  case SE_nonconsective_repetition:
    // not supported
    break ;
  case SE_sequence_dcl:
    //if( sva->node_a && find_var_use( nm, sva->node_a ) )
    //   return 1 ;
    break;
  case SE_sequence_instance:
    //if( sva->node_a && find_var_use( nm, sva->node_a ) )
    //  found = sva ;
    break ;
  case SE_sequence_expr:
    //if( sva->node_a && find_var_use( nm, sva->node_a ) )
    //  return 1 ;
    break ;
  case SE_sequence_item:
    if( sva->exp && sva->exp->localvar_access && 
	find_lvar_expression( nm, sva->exp )       
      ) return 1 ;
    break ;
  case SE_argument: // not used?
    break ;
  case SE_match_item_assign:
    if( sva->nm == nm ) return 1 ;
    break ;
  case SE_match_item_inc_or_dec_identifier:
    if( sva->nm == nm ) return 1 ;
    break ;
  case SE_match_item_identifier_inc_or_dec:
    if( sva->nm == nm ) return 1 ;
    break ;
  case PR_seq:
  case PR_not:
    if( find_var_use( nm, sva->node_a, 1 ) )
    {
      return 1 ;
    }
    break ;
  case PR_or:
  case PR_and:
    break ;
  case PR_overlap_implication:
  case PR_non_overlap_implication:
    if( find_var_use( nm, sva->node_a, 1 ) )
    {
      return 1 ;
    }
    break ;
  case PR_if_else_property:
    break ;
  case PR_clock_property:
    break ;
  case PR_property_instance:
    break ;
  case PR_property_dcl:
    break ;
  case PR_property_inst:
    break ;
  }
  if( depth ) sva = sva->next ;
  else sva = NULL ;
  }
  return 0 ;
}

//  generate local var block for depth generation
//    assign index to the top nodes
//    find last var usage node for all variables
//    detect overwrap of var usage and generate dup range
static void gen_var_block( sva_node *sva ) {
  int index = 0 ;
  sva_node *node, *vnode, *nn ;
  node = sva ;
  while( node ) {
    node->index = index++ ;
    node = node->next ;
  }
  node = sva ;
  while( node ) {
    if( node->type == SE_local_var_dcl ) {
      // find last node that reference this lvar
      vnode = NULL ;
      nn = node->next ;
      while( nn ) {
        if( find_var_use( node->var_list->nm, nn, 0 ) ) {
          vnode = nn ;
        }
        nn = nn->next ;
      }
      node->var_node = vnode ;
    }
    node = node->next ;
  }
  node = sva ;
  while( node ) {
    if( node->type == SE_local_var_dcl && node->resource == RCS_block ) {
      node->act_var_node = node->var_node ;
      nn = node->next ;
      while( nn && nn != node->var_node->next ) {
        if( nn->type == SE_local_var_dcl ) {
          // find another lvar within the block
          if( nn->var_node->index > node->act_var_node->index ) {
            node->act_var_node = nn->var_node ;
	  }
	  nn->resource = RCS_free ;
        }

        nn = nn->next ;
      }
      nn = node->next ;
      while( nn && nn != node->act_var_node->next ) {
         if( nn->type == PR_overlap_implication || 
            nn->type == PR_non_overlap_implication )
        {
          nn->resource = RCS_free ;
        }     
        nn = nn->next ;
      }
    }  
    node = node->next ;
  }
}

// set local var generation right before the first usage
//   if a var is not used, not generated
static sva_node *set_var_list( sva_node *sva, sva_node *var ) 
{
  sva_node *ret = sva ;
  sva_node *node, *pnode, *nn, *new_node ;
  while( var ) {
    node = ret ;
    pnode = NULL ;
    nn = var->next ;
    while( node ) {
      // working here
      if( find_var_use( var->nm, node, 0 ) ) {
        new_node = ALLOC_SVA_NODE ;
        new_node->linenum = node->linenum ;
        new_node->filename = node->filename ;
        new_node->type = SE_local_var_dcl ;
        new_node->var_list = var ;
        new_node->resource = RCS_block ;
        var->next = NULL ;
        new_node->next = node ;
        if( pnode ) pnode->next = new_node ;
        else ret = new_node ;
        node = NULL ;
      }
      if( node ) {
        pnode = node ;
        node = node->next ;
      }
    }
    var = nn ;
  }
  return ret ;
}

/* 
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
  ;
*/
static sva_node *property_dcl( 
  systemverilog_node *node, sva_node *n_args, sva_node *o_args
) {
  named_node *nm = node->node[1]->nm ;
  sva_node *new_node = ALLOC_SVA_NODE ;
  new_node->linenum = node->linenum ;
  new_node->filename = node->filename ;
  nm->sva = new_node ;
  new_node->type = PR_property_dcl ;
  new_node->nm = nm ;
  
  if( node->node[3] && node->node[3]->node[1] ) {
    /* opt_pars_list_of_formals */
    new_node->arg_list = gen_arg_list( node->node[3]->node[1] ) ;
  }
  if( node->node[5] ) {
    new_node->var_list = gen_var_list ( node->node[5] ) ;
  }
  if( node->node[6]->node[0] ) {  /* clocking event */
    new_node->clock = clock_node = clock_node_gen( node->node[6]->node[0] ) ;
  }

  if( n_args ) assign_arg_by_name( nm, n_args ) ;
  else if( o_args ) assign_arg_by_order( nm, o_args ) ;

  if( node->node[6]->node[1] ) { /* disable_iff_block */
    new_node->disable_expression = add2exp_list( node->node[6]->node[1]->node[3]) ;
  }
  new_node->next = property_expr( node->node[6]->node[2], 0, 1 ) ;
  if( new_node->var_list &&  overwrap_depth > 1 ) {
    new_node->next = set_var_list( new_node->next, new_node->var_list ) ;
    new_node->var_list = NULL ;
  }
  return new_node ;
}

/*
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
*/
static sva_node *sequence_dcl( 
  systemverilog_node *node, sva_node *n_args, sva_node *o_args 
) {
  named_node *nm = node->node[1]->nm ;
  sva_node *new_node = ALLOC_SVA_NODE ;
  new_node->linenum = node->linenum ;
  new_node->filename = node->filename ;
  nm->sva = new_node ;
  new_node->type = SE_sequence_dcl ;
  new_node->nm = nm ;
  if( node->node[3] && node->node[3]->node[2] ) {  
    //opt_pars_list_of_formals
    new_node->arg_list = gen_arg_list( node->node[3]->node[2] ) ;
  }
  if( n_args ) assign_arg_by_name( nm, n_args ) ;
  else if( o_args ) assign_arg_by_order( nm, o_args ) ;
  if( node->node[5] ) {
    new_node->var_list = gen_var_list ( node->node[5] ) ;
  } 
  new_node->next = sequence_expr( node->node[6] ) ;
  if( new_node->var_list &&  overwrap_depth > 1 ) {
    new_node->next = set_var_list( new_node->next, new_node->var_list ) ;
    new_node->var_list = NULL ;
  }
  return new_node ;
}

static sva_node *property_inst( systemverilog_node *node ) {
  // node = property_spec: 
  //   opt_clocking_event opt_disable_iff_block property_expr
  sva_node *new_node = ALLOC_SVA_NODE ;
  new_node->linenum = node->linenum ;
  new_node->filename = node->filename ;
  new_node->type = PR_property_inst ;
  new_node->attrib = SVN_branch ;
  if( node->node[0] ) {  // clocking_event defined
    new_node->clock = clock_node = clock_node_gen( node->node[0] ) ;
  }
  if( node->node[1] ) { // disable_iff defined
    new_node->disable_expression = add2exp_list( node->node[1]->node[3] ) ;
  }
  new_node->next = property_expr( node->node[2], 0, 0 ) ;
  
  return new_node ;
}

static void set_port_range( named_node *nm, systemverilog_node *node )
{
  /* '[' expression ':' expression ']' */
  int m, n ;
  nm->bus_m = get_constant( node->node[1] ) ;
  nm->bus_n = get_constant( node->node[3] ) ;
  if( nm->bus_n > nm->bus_m ) nm->bus_endian = 1 ;
}

static SV_ioport_type get_port_type( systemverilog_node *node )
{
  switch( node->type ) {
  case SV_input:
    return SV_port_input ;
  case SV_output:
    return SV_port_output ;
  case SV_inout:
    return SV_port_inout ;
  }
  return SV_port_dummy ;
}

// parsing port declaration and assign info to named_node
static void port_def_parse( systemverilog_node *node ) {
  named_node *nm ;
  systemverilog_node *tmp ;
  switch( node->sva_type) {
    case SV_port_ref:
      /* Identifier */
      break ;
    case SV_port_ref_1:
      /* Identifier '[' expression ']' */
      break ;
    case SV_port_ref_2:
      /* Identifier '[' expression ':' expression ']' */
      break ;
    case SV_input_port_dcl:
      /*
        attribute_list_opt
	'input' net_type_opt signed_opt range_opt Identifier
       */
      nm = node->node[5]->nm ;
      nm->port_type = SV_port_input ;
      if( node->node[2] ) nm->wire_type = node->node[2]->type ;
      if( node->node[3] ) nm->sign = 1 ;
      if( node->node[4] ) set_port_range( nm, node->node[4] ) ;
      break ;
    case SV_inout_port_dcl:
      /*
        attribute_list_opt
	'inout'  net_type_opt signed_opt range_opt Identifier
       */
      nm = node->node[5]->nm ;
      nm->port_type = SV_port_inout ;
      if( node->node[2] ) nm->wire_type = node->node[2]->type ;
      if( node->node[3] ) nm->sign = 1 ;
      if( node->node[4] ) set_port_range( nm, node->node[4] ) ;
      break ;
    case SV_output_port_dcl:
      /*
	attribute_list_opt
	'output' net_type_opt signed_opt range_opt Identifier
	|
        attribute_list_opt
	'output' var_type signed_opt range_opt Identifier
	|
	attribute_list_opt
	'output' var_type signed_opt range_opt Identifier '=' expression
       */
      nm = node->node[5]->nm ;
      nm->port_type = SV_port_output ;
      if( node->node[2] ) nm->wire_type = node->node[2]->type ;
      if( node->node[3] ) nm->sign = 1 ;
      if( node->node[4] ) set_port_range( nm, node->node[4] ) ;
      break ;
    case SV_net_declaration:
      /*
        attribute_list_opt 
	net_type
	primitive_type_opt 
	signed_opt 
	range_opt
	delay3_opt
	net_variable_list (Identifier dimensions_opt)
	';'
       */
      tmp = node->node[6] ;
      while( tmp ) {
	if( tmp->num_node == 3 ) {
          nm = tmp->node[2]->node[0]->nm ;
          tmp = tmp->node[0] ;
        }
        else {
          nm = tmp->node[0]->nm ;
          tmp = NULL ;
        }
        nm->wire_type = node->node[1]->type ;
        if( node->node[3] ) nm->sign = 1 ;
        if( node->node[4] ) set_port_range( nm, node->node[4] ) ;
      }     
      break ;
    case SV_net_assign_declaration:
      /*
	attribute_list_opt net_type
	primitive_type_opt signed_opt range_opt
	delay3_opt net_decl_assigns ';'
       */
      tmp = node->node[6] ;
      while( tmp ) {
	if( tmp->num_node == 3 ) {
          nm = tmp->node[2]->node[0]->nm ;
          tmp = tmp->node[0] ;
        }
        else {
          nm = tmp->node[0]->nm ;
          tmp = NULL ;
        }
        nm->wire_type = node->node[1]->type ;
        if( node->node[3] ) nm->sign = 1 ;
        if( node->node[4] ) set_port_range( nm, node->node[4] ) ;
      }     
      break ;
    case SV_net_st_assign_declaration:
      /*
	attribute_list_opt net_type
	primitive_type_opt signed_opt
	drive_strength net_decl_assigns ';'
       */
      tmp = node->node[5] ;
      while( tmp ) {
	if( tmp->num_node == 3 ) {
          nm = tmp->node[2]->node[0]->nm ;
          tmp = tmp->node[0] ;
        }
        else {
          nm = tmp->node[0]->nm ;
          tmp = NULL ;
        }
        nm->wire_type = node->node[1]->type ;
        if( node->node[3] ) nm->sign = 1 ;
        if( node->node[4] ) set_port_range( nm, node->node[4] ) ;
      }     
      break ;
    case SV_trireg_dcl:
      /*
        'trireg' 
	charge_strength_opt 
	range_opt 
	delay3_opt 
	list_of_identifiers 
	';'
       */
      tmp = node->node[4] ;
      while( tmp ) {
	if( tmp->num_node == 3 ) {
          nm = tmp->node[2]->nm ;
          tmp = tmp->node[0] ;
        }
        else {
          nm = tmp->nm ;
          tmp = NULL ;
        }
        nm->wire_type = node->node[0]->type ;
        if( node->node[2] ) set_port_range( nm, node->node[2] ) ;
      }  
      break ;
    case SV_port_dcl_a:
      /*
         port_type 
	 signed_opt 
	 range_opt 
	 delay3_opt 
	 list_of_identifiers 
	 ';'
       */
      tmp = node->node[4] ;
      while( tmp ) {
	if( tmp->num_node == 3 ) {
          nm = tmp->node[2]->nm ;
          tmp = tmp->node[0] ;
        }
        else {
          nm = tmp->nm ;
          tmp = NULL ;
        }
	nm->port_type = get_port_type( node->node[0] ) ;
	if( node->node[1] ) nm->sign = 1 ;
	if( node->node[2] ) set_port_range( nm, node->node[2] ) ; 
      }      
      break ;
    case SV_port_dcl_b:
      /*
	port_type
	net_type
	signed_opt 
	range_opt 
	list_of_identifiers 
	';'
       */
      tmp = node->node[4] ;
      while( tmp ) {
	if( tmp->num_node == 3 ) {
          nm = tmp->node[2]->nm ;
          tmp = tmp->node[0] ;
        }
        else {
          nm = tmp->nm ;
          tmp = NULL ;
        }
	nm->port_type = get_port_type( node->node[0] ) ;
        nm->wire_type = node->node[1]->type ;
	if( node->node[2] ) nm->sign = 1 ;
	if( node->node[3] ) set_port_range( nm, node->node[3] ) ; 
      }       
      break ;
    case SV_port_dcl_c:
      /*
        'output'
	var_type
	signed_opt 
	range_opt 
	list_of_port_identifiers
	';'
       */
      tmp = node->node[4] ;
      while( tmp ) {
        if( tmp->sva_type == SV_list_of_port_identifiers ) {
          if( tmp->node[2]->sva_type ==  SV_port_identifire_assign )
            nm = tmp->node[2]->node[0]->nm ;        
          else nm = tmp->node[2]->nm ;
          tmp = tmp->node[0] ;        
        }
        else {
          if( tmp->sva_type == SV_port_identifire_assign )
            nm = tmp->node[0]->nm ;
	  else nm = tmp->nm ;
          tmp = NULL ;
        }
	nm->port_type = SV_port_output ;
        nm->wire_type = node->node[1]->type ;
	if( node->node[2] ) nm->sign = 1 ;
	if( node->node[3] ) set_port_range( nm, node->node[3] ) ; 
      }   
      break ;
    case SV_port_dcl_d:
      /*
        'input' 
	var_type 
	signed_opt 
	range_opt 
	list_of_identifiers 
	';'
       */
      tmp = node->node[4] ;
      while( tmp ) {
 	if( tmp->num_node == 3 ) {
          nm = tmp->node[2]->nm ;
          tmp = tmp->node[0] ;
        }
        else {
          nm = tmp->nm ;
          tmp = NULL ;
        }
	nm->port_type = SV_port_input ;
        nm->wire_type = node->node[1]->type ;
	if( node->node[2] ) nm->sign = 1 ;
	if( node->node[3] ) set_port_range( nm, node->node[3] ) ; 
      }   
      break ;
    case SV_port_dcl_e:
      /*
        'inout' 
	var_type 
	signed_opt 
	range_opt 
	list_of_identifiers 
	';'
       */
      tmp = node->node[4] ;
      while( tmp ) {
	if( tmp->num_node == 3 ) {
          nm = tmp->node[2]->nm ;
          tmp = tmp->node[0] ;
        }
        else {
          nm = tmp->nm ;
          tmp = NULL ;
        }
	nm->port_type = SV_port_inout ;
        nm->wire_type = node->node[1]->type ;
	if( node->node[2] ) nm->sign = 1 ;
	if( node->node[3] ) set_port_range( nm, node->node[3] ) ; 
      } 
      break ;
  }
}

static int assertion_node_parse( systemverilog_node *node ) {
  switch( node->sva_type) {
  case SV_concurrent_assertion:
    {
      if( node->node[0] ) {
         cur_name = node->node[0]->node[0]->name ;
         last_lin = node->node[0]->node[0]->debug_linenum ;
         // fprintf( out, "/* concurrent assertion %s: */", cur_name ) ;
      }
      assertion_node_parse( node->node[1] ) ;
      return 1 ;
    }
    break ;
  case SV_sequence_dcl:
    {
      return 1 ;
    }
    break ;
  case SV_property_dcl:
    {
      return 1 ;
    }
    break ;
    case SV_assert_property:
    {
      node->assertion_node = property_inst( node->node[4] ) ;
      current_module->num_error_vector++ ;
      return 1 ;
    }
    break ;
    case SV_cover_property:
    {
      node->assertion_node = property_inst( node->node[4] ) ;
      current_module->num_cover_vector++ ;
      return 1 ;
    }
    break ;
    case SV_assume_property:
    {
      return 1 ;
    }
    break ;
    case SV_module_top:
    {
      current_module = node ;
      return 0 ;
    }
    break ;
    case SV_port_ref:
    case SV_port_ref_1:
    case SV_port_ref_2:
    case SV_input_port_dcl:
    case SV_inout_port_dcl:
    case SV_output_port_dcl:
    case SV_net_declaration:
    case SV_net_assign_declaration:
    case SV_net_st_assign_declaration:
    case SV_trireg_dcl:
    case SV_port_dcl_a:
    case SV_port_dcl_b:
    case SV_port_dcl_c:
    case SV_port_dcl_d:
    case SV_port_dcl_e:
      port_def_parse( node ) ;
      return 0 ;
      break ;
  }
  return 0 ;
  
}

static void rcv_node_parse( systemverilog_node *node ) {
  int i ;
  if( node == NULL ) return ;
  if( node->sva_type && assertion_node_parse(node) ) {
    flag = 0 ;
    if( node->next ) rcv_node_parse( node->next ) ;
    return ;
  }
  for ( i = 0 ; i < node->num_node ; i++ ) {
    rcv_node_parse( node->node[i] ) ;
  }
  if( node->next ) {
    //fprintf( out, "->next\n" ) ;
    rcv_node_parse( node->next ) ;
  }
}

static void assign_arg_by_name( named_node *nm, sva_node *args ) 
{
  sva_node *farg ;
  while( args ) {
    farg = nm->sva->arg_list ;
    while( farg ) {
      if( !strcmp(args->nm->name, farg->nm->name) ) break ;
      farg = farg->next ;
    }
    if( farg == NULL ) {
      fprintf( 
	stderr, "Argument name %s not found on instance %s\n",
	args->nm->name, nm->name 
      ) ;    
    }
    else {
      farg->nm->arg_value = args->exp ;
    }
    args = args->next ;
  }
}

static void assign_arg_by_order( named_node *nm, sva_node *args ) 
{
  sva_node *farg = nm->sva->arg_list ;
  while( args ) {
    if( farg == NULL ) {
      // burf error
      fprintf( 
	stderr, "Number of argument mismatch on instance %s\n",
	nm->name 
      ) ;
      return ;
    }
    farg->nm->arg_value = args->exp ;
    args = args->next ;
    farg = farg->next ;
  }
}

static time_node *cur_tm ;

static void time_analysis( sva_node *sva ) {
  sva_node *tmp ;
  int t_errchk ;
  
  while( sva ) {
  
    if( cur_tm->head == NULL ) cur_tm->head = sva ;
   
    switch( sva->type ) {
    case SE_expression:
      if( sva->resource ) {
	cur_tm->tail = sva ;
	cur_tm->next = ALLOC_TM_NODE ;
	cur_tm->next->attrib = cur_tm->attrib ;
	cur_tm = cur_tm->next ;
	cur_tm->head = sva ;
	sva->tm_node = cur_tm ;
      }
      else {
	sva->tm_node = cur_tm ;
      }
      break ;
    case SE_delay:
      if( sva->simple_delay ) {
	if( cur_tm->type == TM_zero || cur_tm->type == TM_single ) {
	  if( sva->resource ) {
	    cur_tm->tail = sva ;
	    cur_tm->next = ALLOC_TM_NODE ;
	    cur_tm->next->attrib = cur_tm->attrib ;
	    cur_tm = cur_tm->next ;
	    sva->tm_node = cur_tm ;
	    cur_tm->head = sva ;      
	    cur_tm->time1 = sva->min_cyc ;
	    cur_tm->type = TM_single ;
	  }
	  else {
	    cur_tm->type = TM_single ;
	    cur_tm->time1 += sva->min_cyc ;
	    sva->tm_node = cur_tm ;
	  }
	}
	else {
	  cur_tm->tail = sva ;
	  cur_tm->next = ALLOC_TM_NODE ;
	  cur_tm->next->attrib = cur_tm->attrib ;
	  cur_tm = cur_tm->next ;
	  sva->tm_node = cur_tm ;
	  cur_tm->time1 = sva->min_cyc ;
	  cur_tm->head = sva ;
	  cur_tm->type = TM_single ;
	}
      }
      else {
	cur_tm->tail = sva ;
	cur_tm->next = ALLOC_TM_NODE ;
	cur_tm->next->attrib = cur_tm->attrib ;
	cur_tm = cur_tm->next ;
	sva->tm_node = cur_tm ;
	cur_tm->head = sva ;
	cur_tm->time1 = sva->min_cyc ;
	cur_tm->time2 = sva->max_cyc ;
	if( cur_tm->time2 < 0 ) cur_tm->type = TM_unbound ;
	else cur_tm->type = TM_multi ;
      }
      sva->tm_node = cur_tm ;
      break ;
    case SE_and:
    case SE_or:
    case SE_intersect:
      if( cur_tm->attrib != TMA_none ) {
	cur_tm->tail = sva ;
	cur_tm->next = ALLOC_TM_NODE ;
	cur_tm->next->attrib = cur_tm->attrib ;
	cur_tm = cur_tm->next ;
	cur_tm->time1 = sva->min_cyc ;
	cur_tm->head = sva ;
	cur_tm->type = TM_resouce ;      
      }
      sva->tm_node = cur_tm ;
      cur_tm->node_a = ALLOC_TM_NODE ;
      cur_tm->node_a->attrib = cur_tm->attrib ;
      cur_tm->node_b = ALLOC_TM_NODE ;
      cur_tm->node_b->attrib = cur_tm->attrib ;    
      cur_tm = sva->tm_node->node_a ;
      time_analysis( sva->node_a ) ;
      cur_tm = sva->tm_node->node_b ;
      time_analysis( sva->node_b ) ;
      cur_tm = sva->tm_node ;
      // if both nodes are zero node, it will finish eval immediately, 
      // so no need for the pallarel logic
      if( is_zero_node( sva->node_a ) && is_zero_node( sva->node_b ) ) {
        sva->resource = RCS_free ;
        sva->attrib = SVN_filter ;
      }
      break ;
    case SE_within:
      if( cur_tm->attrib != TMA_none ) {
	cur_tm->tail = sva ;
	cur_tm->next = ALLOC_TM_NODE ;
	cur_tm->next->attrib = cur_tm->attrib ;
	cur_tm = cur_tm->next ;
	cur_tm->time1 = sva->min_cyc ;
	cur_tm->head = sva ;
	cur_tm->type = TM_resouce ;      
      }
      sva->tm_node = cur_tm ;
      cur_tm->node_a = ALLOC_TM_NODE ;
      cur_tm->node_a->attrib = cur_tm->attrib ;
      cur_tm->node_b = ALLOC_TM_NODE ;
      cur_tm->node_b->attrib = cur_tm->attrib ;    
      cur_tm = sva->tm_node->node_a ;
      time_analysis( sva->node_a ) ;
      cur_tm = sva->tm_node->node_b ;
      time_analysis( sva->node_b ) ;
      cur_tm = sva->tm_node ;
      break ;
    case SE_throughout:
      sva->tm_node = cur_tm ;
      time_analysis( sva->node_a ) ;
      break ;
    case SE_first_match:
      if( cur_tm->attrib == TMA_none ) {
	if( is_simple_delay( sva->node_a, 1 ) ) {
	  sva->tm_node = cur_tm ;
	  time_analysis( sva->node_a ) ;
	}
	else {
	  cur_tm->tail = sva ;
	  cur_tm->next = ALLOC_TM_NODE ;
	  cur_tm->next->attrib = TMA_F ;
	  cur_tm = cur_tm->next ;
	  sva->tm_node = cur_tm ; 
	  time_analysis( sva->node_a ) ;
	  cur_tm->next = ALLOC_TM_NODE ;
	  cur_tm = cur_tm->next ;
	}
      }
      else {
	sva->tm_node = cur_tm ; 
	time_analysis( sva->node_a ) ;
      }    
      break ;
    case SE_clock:
      sva->tm_node = cur_tm ;
      //time_analysis( sva->node_a ) ;   
      break ;
      // repetitions are by itself a resouce node
    case SE_consective_repetition:
      if( sva->simple_delay ) {
	cur_tm->tail = sva ;
	cur_tm->next = ALLOC_TM_NODE ;
	cur_tm->next->attrib = cur_tm->attrib ;
	cur_tm = cur_tm->next ;
	cur_tm->type = TM_resouce ;
	sva->tm_node = cur_tm ;
	cur_tm->head = sva ;      
	cur_tm->time1 = sva->min_cyc ;
      }
      else {
	cur_tm->tail = sva ;
	cur_tm->next = ALLOC_TM_NODE ;
	cur_tm->next->attrib = cur_tm->attrib ;
	cur_tm = cur_tm->next ;
	sva->tm_node = cur_tm ;
	cur_tm->head = sva ;
	cur_tm->time1 = sva->min_cyc ;
	cur_tm->time2 = sva->max_cyc ;
	if( cur_tm->time2 < 0 ) cur_tm->type = TM_unbound ;
	else cur_tm->type = TM_multi ;    
      }
      time_analysis( sva->node_a ) ;   
      break ;
    case SE_goto_repetition:
      if( sva->simple_delay ) {
	cur_tm->tail = sva ;
	cur_tm->next = ALLOC_TM_NODE ;
	cur_tm->next->attrib = cur_tm->attrib ;
	cur_tm = cur_tm->next ;
	cur_tm->type = TM_resouce ;
	sva->tm_node = cur_tm ;
	cur_tm->head = sva ;      
	cur_tm->time1 = sva->min_cyc ;
      }
      else {
	cur_tm->tail = sva ;
	cur_tm->next = ALLOC_TM_NODE ;
	cur_tm->next->attrib = cur_tm->attrib ;
	cur_tm = cur_tm->next ;
	sva->tm_node = cur_tm ;
	cur_tm->head = sva ;
	cur_tm->time1 = sva->min_cyc ;
	cur_tm->time2 = sva->max_cyc ;
	if( cur_tm->time2 < 0 ) cur_tm->type = TM_unbound ;
	else cur_tm->type = TM_multi ;    
      }
      break ;
    case SE_nonconsective_repetition:
      if( sva->simple_delay ) {
	cur_tm->tail = sva ;
	cur_tm->next = ALLOC_TM_NODE ;
	cur_tm->next->attrib = cur_tm->attrib ;
	cur_tm = cur_tm->next ;
	sva->tm_node = cur_tm ;
	cur_tm->head = sva ;      
	cur_tm->time1 = sva->min_cyc ;
      }
      else {
	cur_tm->tail = sva ;
	cur_tm->next = ALLOC_TM_NODE ;
	cur_tm->next->attrib = cur_tm->attrib ;
	cur_tm = cur_tm->next ;
	sva->tm_node = cur_tm ;
	cur_tm->head = sva ;
	cur_tm->time1 = sva->min_cyc ;
	cur_tm->time2 = sva->max_cyc ;
	if( cur_tm->time2 < 0 ) cur_tm->type = TM_unbound ;
	else cur_tm->type = TM_multi ;    
      }
      break ;
    case SE_sequence_dcl:
      sva->tm_node = cur_tm ;
      //time_analysis( sva->node_a ) ;
      break;
    case SE_sequence_instance:
      cur_tm->tail = sva ;
      cur_tm->next = ALLOC_TM_NODE ;
      cur_tm->next->attrib = cur_tm->attrib ;
      cur_tm = cur_tm->next ;
      sva->tm_node = cur_tm ;
      //time_analysis( sva->node_a->node_a ) ;
      break ;
    case SE_sequence_expr:
      if( sva->resource ) {
	cur_tm->tail = sva ;
	cur_tm->next = ALLOC_TM_NODE ;
	cur_tm->next->attrib = cur_tm->attrib ;
	cur_tm = cur_tm->next ;
	sva->tm_node = cur_tm ;
	//time_analysis( sva->node_a ) ;
      }
      else {
	sva->tm_node = cur_tm ;    
	//time_analysis( sva->node_a ) ;
      }
      break ;
    case SE_sequence_item:
      if( sva->resource ) {
	cur_tm->tail = sva ;
	cur_tm->next = ALLOC_TM_NODE ;
	cur_tm->next->attrib = cur_tm->attrib ;
	cur_tm = cur_tm->next ;
	sva->tm_node = cur_tm ;
      }
      else {
	sva->tm_node = cur_tm ;    
      }
      break ;
    case SE_argument: // not used?
      sva->tm_node = cur_tm ;    
      break ;
    case SE_match_item_assign:
      sva->tm_node = cur_tm ;    
      break ;
    case SE_match_item_inc_or_dec_identifier:
      sva->tm_node = cur_tm ;    
      break ;
    case SE_match_item_identifier_inc_or_dec:
      sva->tm_node = cur_tm ;    
      break ;
    case PR_seq:
    case PR_not:
      sva->tm_node = cur_tm ;
      time_analysis( sva->node_a ) ;
      break ;
    case PR_or:
    case PR_and:
      if( cur_tm->attrib != TMA_none ) {
	cur_tm->tail = sva ;
	cur_tm->next = ALLOC_TM_NODE ;
	cur_tm->next->attrib = cur_tm->attrib ;
	cur_tm = cur_tm->next ;
	cur_tm->time1 = sva->min_cyc ;
	cur_tm->head = sva ;
	cur_tm->type = TM_resouce ;      
      }
      sva->tm_node = cur_tm ;
      cur_tm->node_a = ALLOC_TM_NODE ;
      cur_tm->node_a->attrib = cur_tm->attrib ;
      cur_tm->node_b = ALLOC_TM_NODE ;
      cur_tm->node_b->attrib = cur_tm->attrib ;    
      cur_tm = sva->tm_node->node_a ;
      time_analysis( sva->node_a ) ;
      cur_tm = sva->tm_node->node_b ;
      time_analysis( sva->node_b ) ;
      cur_tm = sva->tm_node ;
      // if both nodes are zero node, it will finish eval immediately, 
      // so no need for the pallarel logic
      if( is_zero_node( sva->node_a ) && is_zero_node( sva->node_b ) ) {
        sva->resource = RCS_free ;
        sva->attrib = SVN_filter ;
      }
      break ;
    case PR_overlap_implication:
    case PR_non_overlap_implication:
      sva->tm_node = cur_tm ;
      cur_tm->next = ALLOC_TM_NODE ;
      cur_tm = cur_tm->next ;
      cur_tm->attrib = TMA_H ;
      time_analysis( sva->node_a ) ;
      cur_tm = sva->tm_node ;
      break ;
    case PR_if_else_property:
      sva->tm_node = cur_tm ;
      sva->tm_node->node_a = cur_tm = ALLOC_TM_NODE ;
      time_analysis( sva->node_a ) ;
      sva->tm_node->node_b = cur_tm = ALLOC_TM_NODE ;
      time_analysis( sva->node_b ) ;
      cur_tm = sva->tm_node ;
      break ;
    case PR_clock_property:
      sva->tm_node = cur_tm ;
      //time_analysis( sva->node_a ) ;
      break ;
    case PR_property_instance:
      sva->tm_node = cur_tm ;
      //tmp = sva->nm->sva ;
      //time_analysis( tmp ) ;
      break ;
    case PR_property_dcl:
      sva->tm_node = cur_tm ;
      //time_analysis( sva->node_a ) ;
      break ;
    case PR_property_inst:
      sva->tm_node = cur_tm = ALLOC_TM_NODE ;
      cur_tm->head = sva ;
      clock_node = sva->clock ;
      //time_analysis( sva->node_a ) ;
      break ;
    }
  
    sva = sva->next ;
  
  }
  
}

static void node_out( systemverilog_node *node ) {
  fprintf( out, "%s%d", ARV_WIRE, node->exp_id ) ;
}

static systemverilog_node *node_not( systemverilog_node *node ) {
  systemverilog_node *nd ;
  nd = ALLOC_SV_NODE ;
  nd->exp_id = label_num++ ;
  
  fprintf( out, "  wire " ) ;
  node_out( nd ) ;
  fprintf( out, " = ~" ) ;
  node_out( node ) ;
  fprintf( out, " ; \n" ) ;
  number_of_not++ ;
  return nd ;
}

static systemverilog_node *new_wire_node() {
  systemverilog_node *nd ;
  nd = ALLOC_SV_NODE ;
  nd->exp_id = label_num++ ;
  
  fprintf( out, "  wire " ) ;
  node_out( nd ) ;
  fprintf( out, " ; \n" ) ;
  return nd ;
}

static systemverilog_node *new_reg_node( int ub, int lb ) {
  systemverilog_node *nd ;
  nd = ALLOC_SV_NODE ;
  nd->exp_id = label_num++ ;
  
  if( ub == 0 && lb == 0 ) {
  fprintf( out, "  reg " ) ;
  node_out( nd ) ;
  fprintf( out, " ; \n" ) ;
  }
  else {
    fprintf( out, 
      "  reg [%d:%d] %s%d ; \n",
      ub, lb, ARV_WIRE, nd->exp_id
    ) ;  
  }
  return nd ;
}

static void connect_port( char *prt, systemverilog_node *node, int next ) {
  fprintf( out, ".%s(", prt ) ;
  
  if( node )  node_out( node ) ;
  else fprintf( out, " 1 " ) ;
  
  if( next )
    fprintf( out, "), " ) ;
  else
    fprintf( out, ") " ) ;
  
}

static systemverilog_node *node_sync( systemverilog_node *node ) {
  systemverilog_node *nd ;
  nd = ALLOC_SV_NODE ;
  nd->exp_id = label_num++ ;
  
  fprintf( out, "  wire " ) ;
  node_out( nd ) ;
  fprintf( out, " ; \n" ) ;
  fprintf( out,  "  ARV_DFF_E sync_dff%d ( ", label_num++ ) ;
  connect_port ( "Clk", clock_node, 1 ) ;
  fprintf( 
    out, ".RN(%s), .E((~%s) && %s), ", ARV_RESET_, ARV_CLEAR, ARV_ENABLE 
  ) ;
  connect_port( "D", node , 1) ;
  connect_port( "Q", nd, 0 ) ;
  fprintf( out, " ) ;\n" ) ;
  
  number_of_ff++ ;
  number_of_and += 2 ;
  number_of_not++ ;
  
  return nd ;
}

static systemverilog_node *node_sync_c( 
  systemverilog_node *node, systemverilog_node *clear 
) {
  systemverilog_node *nd ;
  nd = ALLOC_SV_NODE ;
  nd->exp_id = label_num++ ;
  
  fprintf( out, "  wire " ) ;
  node_out( nd ) ;
  fprintf( out, " ; \n" ) ;
  fprintf( out,  "  ARV_DFF_E sync_dff%d ( ", label_num++ ) ;
  connect_port ( "Clk", clock_node, 1 ) ;
  fprintf( 
    out, ".RN(%s), .E( (~%s) && %s && (~ ", ARV_RESET_, ARV_CLEAR, ARV_ENABLE 
  ) ;
  node_out( clear ) ;
  fprintf( out, ") ), " ) ;
  connect_port( "D", node , 1) ;
  connect_port( "Q", nd, 0 ) ;
  fprintf( out, " ) ;\n" ) ;
  
  number_of_ff++ ;
  number_of_and += 3 ;
  number_of_not++ ;
  
  return nd ;
}

static systemverilog_node *node_or( 
  systemverilog_node *node_a, systemverilog_node *node_b
) {
  systemverilog_node *nd ;
  nd = ALLOC_SV_NODE ;
  nd->exp_id = label_num++ ;
  fprintf( out, "  wire " ) ;
  node_out( nd ) ;
  fprintf( out, " = " ) ;
  node_out( node_a ) ;
  fprintf( out, " | " ) ;
  node_out( node_b ) ;
  fprintf( out, " ;\n" ) ;
  number_of_or++ ;
  return nd ;
}

static systemverilog_node *node_and( 
  systemverilog_node *node_a, systemverilog_node *node_b
) {
  systemverilog_node *nd ;
  nd = ALLOC_SV_NODE ;
  nd->exp_id = label_num++ ;
  fprintf( out, "  wire " ) ;
  node_out( nd ) ;
  fprintf( out, " = " ) ;
  node_out( node_a ) ;
  fprintf( out, " & " ) ;
  node_out( node_b ) ;
  fprintf( out, " ;\n" ) ;
  number_of_and++ ;
  return nd ;
}

static void connect_first_match() {
  fprintf( out, "  assign " ) ;
  node_out( fmatch_node ) ;
  fprintf( out, " = " ) ;
  node_out( match_node ) ;
  fprintf( out, " ;\n" ) ;  
}

static int is_zero_node( sva_node *sva ) {
  time_node *t = sva->tm_node ;
  while( t ) {
    if( t->type != TM_zero ) return 0 ;
    t = t->next ;
  }
  return 1 ;
}

static void gen_error_zero( int sync ) {
  if( sync ) error_node = prop_error_node = node_sync( error_node ) ;
  else prop_error_node = error_node ;
  if( overwrap_flag ) {
    overwrap_node = new_wire_node() ;
    fprintf( out, "  assign " ) ;
    node_out( overwrap_node ) ;
    fprintf( out, " = 1'b0 ; \n" ) ;
  }
}

static void gen_error( int flag, int sync ) {
  if( simple_pipe ) {
    // error_node is already created
    if( sync )  prop_error_node = node_sync( error_node ) ;
    else prop_error_node =  error_node  ;
  }
  else {
    prop_error_node = new_wire_node() ;
    fprintf( out, "  ARV_ERROR_GEN arb_error_gen%d ( ", label_num++ ) ;
    connect_port( "Clk", clock_node, 1 ) ;
    fprintf( 
      out, ".RN(%s), .E(%s), .C(%s)," , ARV_RESET_, ARV_ENABLE, ARV_CLEAR 
    ) ; 
    connect_port( "B", busy_node, 1 ) ;
    connect_port( "M", match_node, 1 ) ;
    connect_port( "ER", prop_error_node, 0 ) ;
    fprintf( out, ") ;\n" ) ;
    number_of_ff += ARV_ERROR_GEN_FF ;
    number_of_and += ARV_ERROR_GEN_AND ;
    number_of_or += ARV_ERROR_GEN_OR ;            
    number_of_not += ARV_ERROR_GEN_NOT ;     
    if( error_node ) {  // first exp after imply may generate this node
      error_node = prop_error_node = node_or( error_node, prop_error_node ) ;
    }
  }
  if( flag && overwrap_flag && overwrap_node == NULL ) {
    overwrap_node = new_wire_node() ;
    fprintf( out, "  assign " ) ;
    node_out( overwrap_node ) ;
    fprintf( out, " = 1'b0 ; \n" ) ;
  }
}

static void gen_delay( sva_node *sva ) 
{
  systemverilog_node *q, *b, *tmp ;
  int check_ovwp = 0 ;
  // time_node *t = sva->tm_node ;
  //   1. if( not H or F, not generate Busy )
  //   2. if( not single && 
  //         H or F and length > USE_COUNTER, use counter type )
      
  q = new_wire_node() ;
  b = new_wire_node() ;
  if( sva->simple_delay ) {
    if( sva->min_cyc == 1 ) {
      fprintf( out, "  ARV_DELAY_PIPE1 arv_pipe%d(", label_num++ ) ;
    }
    else {
      if( !use_pipe_delay && sva->min_cyc >= arv_use_counter ) {
	int bw = 0 ;
	int tmp = sva->min_cyc ;
	while( tmp ) {
	  bw++ ;
	  tmp /= 2 ;
	}
	check_ovwp = 1 ;
	fprintf( 
	  out, "  ARV_DELAY_COUNTER #(%d, %d, %d) arv_pipe%d (",
	  sva->min_cyc, sva->min_cyc, bw, label_num++ 
        ) ;
        number_of_ff += ARV_DELAY_COUNTER_FF * bw ;
        number_of_and += ARV_DELAY_COUNTER_AND * bw ;
        number_of_or += ARV_DELAY_COUNTER_OR * bw ;
        number_of_not += ARV_DELAY_COUNTER_NOT * bw ;
      }
      else {
	fprintf( 
	  out, "  ARV_DELAY_PIPE #(%d, %d) arv_pipe%d (",
	  sva->min_cyc, sva->min_cyc, label_num++ 
	) ;
        number_of_ff += ARV_DELAY_PIPE_FF * sva->min_cyc ;
        number_of_and += ARV_DELAY_PIPE_AND * sva->min_cyc ;
        number_of_or += ARV_DELAY_PIPE_OR * sva->min_cyc ;      
        number_of_not += ARV_DELAY_PIPE_NOT * sva->min_cyc ;      
      }
    }
    prev_branch_depth = 0 ;
  }
  else {
    if( sva->max_cyc > 0 ) {
      if( !use_pipe_delay && sva->max_cyc >= arv_use_counter ) {
	int bw = 0 ;
	int tmp = sva->max_cyc ;
	while( tmp ) {
	  bw++ ;
	  tmp /= 2 ;
	}
	check_ovwp = 1 ;
	fprintf( 
	  out, "  ARV_DELAY_COUNTER #(%d, %d, %d) arv_pipe%d (",
	  sva->min_cyc, sva->max_cyc, bw, label_num++ 
        ) ;
        number_of_ff += ARV_DELAY_COUNTER_FF * bw ;
        number_of_and += ARV_DELAY_COUNTER_AND * bw ;
        number_of_or += ARV_DELAY_COUNTER_OR * bw ;
        number_of_not += ARV_DELAY_COUNTER_NOT * bw ;
      }
      else {
        fprintf( 
  	  out, "  ARV_DELAY_PIPE #(%d, %d) arv_pipe%d (",
	  sva->min_cyc, sva->max_cyc, label_num++ 
        ) ;
        number_of_ff += ARV_DELAY_PIPE_FF * sva->max_cyc ;
        number_of_and += ARV_DELAY_PIPE_AND * sva->max_cyc ;
        number_of_or += ARV_DELAY_PIPE_OR * sva->max_cyc ;            
        number_of_not += ARV_DELAY_PIPE_NOT * sva->max_cyc ; 
      }
      prev_branch_depth = sva->max_cyc + 1 - sva->min_cyc ;
        
    }
    else {
      // [n:$] delay case
      int bw = 0 ;
      int tmp = sva->min_cyc ;
      while( tmp ) {
	bw++ ;
	tmp /= 2 ;
      }
      check_ovwp = 1 ;
      fprintf( 
	out, "  ARV_DELAY_EVER #(%d, %d) arv_pipe%d (",
	sva->min_cyc, bw, label_num++ 
      ) ;
      number_of_ff += ARV_DELAY_EVER_FF * sva->max_cyc ;
      number_of_and += ARV_DELAY_EVER_AND * sva->max_cyc ;
      number_of_or += ARV_DELAY_EVER_OR * sva->max_cyc ;           
      number_of_not += ARV_DELAY_EVER_NOT * sva->max_cyc ;
      prev_branch_depth = overwrap_depth ;        
    }
  }
  connect_port( "Clk", clock_node, 1 ) ;
  fprintf( out, ".RN(%s), .E(%s),", ARV_RESET_, ARV_ENABLE ) ;
  connect_port( "D", match_node, 1 ) ;
  fprintf( out, " .C(%s", ARV_CLEAR ) ;
  if( fmatch_node ) {
    fprintf( out, " | " ) ;
    node_out( fmatch_node ) ;
  }
  fprintf( out, "), " ) ;
  connect_port( "Q", q, 1 ) ;
  connect_port( "B", b, 0 ) ;
  fprintf( out, " ) ;\n" ) ;
  if(  get_busy_node || (!use_pipe_delay && sva->min_cyc >= arv_use_counter) || (sva->tm_node->attrib != TMA_none && !simple_pipe) ) {
    if( busy_node ) busy_node = node_or( b, busy_node ) ;
    else busy_node = b ;
  }
  if( check_ovwp && overwrap_flag  && !simple_pipe && (sva->tm_node->attrib != TMA_none) ) 
  {
    systemverilog_node *ovr = node_and( b, match_node ) ;
    if( overwrap_node ) overwrap_node = node_or( overwrap_node, ovr ) ;
    else overwrap_node = ovr ;
  }
  if( sva->exp ) {
    match_node = node_and( q, sva->exp ) ;
    if( error_check ) {
      tmp = node_not( sva->exp ) ;
      tmp = node_and( q, tmp ) ;
      if( error_node ) error_node = node_or( error_node, tmp ) ;
      else error_node = tmp ;
    }
  }
  else {
    if( error_check ) {
      // nothing to do here, next stage will handle it
    }
    match_node = q ;
  }
  if( sva->node_b ) { // sequence match item
    fprintf( out, "  assign %s%d = ", ARV_WIRE, sva->node_b->seq_match_id ) ;
    node_out( match_node ) ;
    fprintf( out, " ; /* assign sequence match trigger */\n" ) ;
  }

}

static void gen_seq_and( sva_node *sva )
{
  systemverilog_node *tmp, *mp, *bp, *b0, *b1 ;
  systemverilog_node *q, *b ;
  int t_ini ;
  t_ini = initial_check ;
  initial_check = 0 ;
  if( is_zero_node( sva->node_a ) && is_zero_node( sva->node_b ) ) {
    // if both node is zero node, just create and logic
    mp = match_node ;
    rtl_generation( sva->node_a, 1 ) ;    
    tmp = match_node ;
    match_node = mp ;
    rtl_generation( sva->node_b, 1 ) ; 
    match_node = node_and( tmp, match_node ) ;
    if( t_ini ) {
      tmp = node_not( match_node ) ;
      tmp = node_and( tmp, mp ) ;
      if( error_node ) error_node = node_or( tmp, error_node ) ;
      else error_node = tmp ;
    }
    return ;
  }
  bp = busy_node ;
  busy_node = NULL ;
  mp = match_node ;
  rtl_generation( sva->node_a, 1 ) ;
  tmp = match_node ;
  b0 = busy_node ;
  busy_node = NULL ;
  match_node = mp ;
  rtl_generation( sva->node_b, 1 ) ;
  b1 = busy_node ;
  q = new_wire_node() ;
  b = new_wire_node() ;
  fprintf( out, "  ARV_SEQ_AND_S arv_and%d (", label_num++ ) ;      
  connect_port( "Clk", clock_node, 1 ) ;
  fprintf( out, ".RN(%s), .E(%s), .C(%s" , ARV_RESET_, ARV_ENABLE, ARV_CLEAR ) ;
  if( fmatch_node ) {
    fprintf( out, " | " ) ;
    node_out( fmatch_node ) ;
  }
  fprintf( out, ")," ) ;
  if( b0 ) connect_port( "B1", b0, 1 ) ;
  else fprintf( out, ".B1(1'b0)," ) ;
  if( b1 ) connect_port( "B2", b1, 1 ) ;
  else fprintf( out, ".B2(1'b0)," ) ;
  connect_port( "D1", tmp, 1 ) ;
  connect_port( "D2", match_node, 1 ) ;
  connect_port( "Q", q, 1 ) ;
  connect_port( "B", b, 0 ) ;
  fprintf( out, " ) ;\n" ) ;
  number_of_ff += ARV_SEQ_AND_FF ;
  number_of_and += ARV_SEQ_AND_AND ;
  number_of_or += ARV_SEQ_AND_OR ;           
  number_of_not += ARV_SEQ_AND_NOT ;           
  if( sva->tm_node->attrib != TMA_none ) {
    //if( bp || b0 || b1 ) {
    //  if( !bp ) bp = b0 ;
    //  else {
    //     if( b0 ) bp = node_or( bp, b0 ) ;
    //  }
    //  if( !bp ) bp = b1 ;
    //  else {
    //    if( b1 ) bp = node_or( bp, b1 ) ;
    //  }
    //}
    if( bp ) busy_node = node_or( b, bp ) ;
    else busy_node = b ;
    if( overwrap_flag && sva->tm_node->attrib == TMA_H ) {
      systemverilog_node *ovr = node_and( busy_node, mp ) ;
      if( overwrap_node ) overwrap_node = node_or( overwrap_node, ovr ) ;
      else overwrap_node = ovr ;
    }    
  }
  match_node = q ;
}

static void gen_prop_or( sva_node *sva )
{
  systemverilog_node *pm, *tmp, *cs, *b0, *b1, *e0, *e1, *pfm, *pgt ;
  systemverilog_node *q, *b, *er ;
  int tby ;
  if( is_zero_node( sva->node_a ) && is_zero_node( sva->node_b ) ) {
    // if both node is zero node, just create and logic
    match_node = NULL ;
    rtl_generation( sva->node_a, 0 ) ;    
    tmp = match_node ;
    match_node = NULL ;
    rtl_generation( sva->node_b, 0 ) ; 
    match_node = node_or( tmp, match_node ) ;
    prop_error_node = error_node = node_not( match_node ) ;
    return ;
  }
  cs = new_wire_node() ;
  pm = match_node ; // in case eval gate is used
  pfm = fmatch_node ;
  pgt = gate_node ;
  init_nodes() ;
  tby = get_busy_node ;
  get_busy_node = 1 ;
  match_node = cs ;
  rtl_generation( sva->node_a, 0 ) ;
  tmp = match_node ;
  if( prop_busy_node ) b0 = prop_busy_node ;
  else b0 = busy_node ;
  e0 = prop_error_node ;
  init_nodes() ;
  get_busy_node = 1 ;
  match_node = cs ;
  rtl_generation( sva->node_b, 0 ) ;
  if( prop_busy_node ) b1 = prop_busy_node ;
  else b1 = busy_node ;
  e1 = prop_error_node ;
  get_busy_node = tby ;
  fmatch_node = pfm;
  gate_node = pgt ;
  q = new_wire_node() ;
  b = new_wire_node() ;
  er = new_wire_node() ;
  fprintf( out, "  ARV_PRP_OR arv_or%d (", label_num++ ) ;      
  connect_port( "Clk", clock_node, 1 ) ;
  fprintf( 
    out, ".RN(%s), .E(%s), .C(%s" , ARV_RESET_, ARV_ENABLE, ARV_CLEAR 
  ) ;
  if( fmatch_node ) {
    fprintf( out, " | " ) ;
    node_out( fmatch_node ) ;
  }
  fprintf( out, ")," ) ;
  if( pm ) connect_port( "S", pm, 1 ) ;
  else fprintf( out, ".S(1'b1)," ) ;
  connect_port( "CS", cs, 1 ) ;
  if( b0 ) connect_port( "B1", b0, 1 ) ;
  else fprintf( out, ".B1(1'b0)," ) ;
  if( b1 ) connect_port( "B2", b1, 1 ) ;
  else fprintf( out, ".B2(1'b0)," ) ;
  if( e0 ) connect_port( "E1", e0, 1 ) ;
  else fprintf( out, ".E1(1'b0)," ) ;
  if( e1 ) connect_port( "E2", e1, 1 ) ;
  else fprintf( out, ".E2(1'b0)," ) ;
  connect_port( "D1", tmp, 1 ) ;
  connect_port( "D2", match_node, 1 ) ;
  connect_port( "Q", q, 1 ) ;
  connect_port( "B", b, 1 ) ;
  connect_port( "ER", er, 0 ) ;
  fprintf( out, " ) ;\n" ) ;
  number_of_ff += ARV_PRP_OR_FF ;
  number_of_and += ARV_PRP_OR_AND ;
  number_of_or += ARV_PRP_OR_OR ;           
  number_of_not += ARV_PRP_OR_NOT ;           
  busy_node = b ;
  match_node = q ;  
  prop_error_node = error_node = er ;
  if( overwrap_flag  ) {
    systemverilog_node *ovr ;
    if( pm ) ovr = node_and( b, pm ) ;
    else ovr = b ;
    if( overwrap_node ) overwrap_node = node_or( overwrap_node, ovr ) ;
    else overwrap_node = ovr ;
  }
}
  
static void gen_prop_and( sva_node *sva )
{
  systemverilog_node *pm, *tmp, *cs, *b0, *b1, *e0, *e1, *pfm, *pgt ;
  systemverilog_node *q, *b, *er ;
  int tby ;
  if( is_zero_node( sva->node_a ) && is_zero_node( sva->node_b ) ) {
    // if both node is zero node, just create and logic
    match_node = NULL ;
    rtl_generation( sva->node_a, 0 ) ;    
    tmp = match_node ;
    match_node = NULL ;
    rtl_generation( sva->node_b, 0 ) ; 
    match_node = node_and( tmp, match_node ) ;
    prop_error_node = error_node = node_not( match_node ) ;
    return ;
  }
  cs = new_wire_node() ;
  pm = match_node ; // in case eval gate is used
  pfm = fmatch_node ;
  pgt = gate_node ;
  init_nodes() ;
  tby = get_busy_node ;
  get_busy_node = 1 ;
  match_node = cs ;
  fmatch_node = pfm;
  rtl_generation( sva->node_a, 0 ) ;
  tmp = match_node ;
  if( prop_busy_node ) b0 = prop_busy_node ;
  else b0 = busy_node ;
  e0 = prop_error_node ;
  init_nodes() ;
  get_busy_node = 1 ;
  match_node = cs ;
  fmatch_node = pfm;
  rtl_generation( sva->node_b, 0 ) ;
  if( prop_busy_node ) b1 = prop_busy_node ;
  else b1 = busy_node ;
  e1 = prop_error_node ;
  get_busy_node = tby ;
  fmatch_node = pfm;
  gate_node = pgt ;
  q = new_wire_node() ;
  b = new_wire_node() ;
  er = new_wire_node() ;
  fprintf( out, "  ARV_PRP_AND arv_and%d (", label_num++ ) ;      
  connect_port( "Clk", clock_node, 1 ) ;
  fprintf( 
    out, ".RN(%s), .E(%s), .C(%s" , ARV_RESET_, ARV_ENABLE, ARV_CLEAR 
  ) ;
  if( fmatch_node ) {
    fprintf( out, " | " ) ;
    node_out( fmatch_node ) ;
  }
  fprintf( out, ")," ) ;
  if( pm ) connect_port( "S", pm, 1 ) ;
  else fprintf( out, ".S(1'b1)," ) ;
  connect_port( "CS", cs, 1 ) ;
  if( b0 ) connect_port( "B1", b0, 1 ) ;
  else fprintf( out, ".B1(1'b0)," ) ;
  if( b1 ) connect_port( "B2", b1, 1 ) ;
  else fprintf( out, ".B2(1'b0)," ) ;
  if( e0 ) connect_port( "E1", e0, 1 ) ;
  else fprintf( out, ".E1(1'b0)," ) ;
  if( e1 ) connect_port( "E2", e1, 1 ) ;
  else fprintf( out, ".E2(1'b0)," ) ;
  connect_port( "D1", tmp, 1 ) ;
  connect_port( "D2", match_node, 1 ) ;
  connect_port( "Q", q, 1 ) ;
  connect_port( "B", b, 1 ) ;
  connect_port( "ER", er, 0 ) ;
  fprintf( out, " ) ;\n" ) ;
  number_of_ff += ARV_PRP_AND_FF ;
  number_of_and += ARV_PRP_AND_AND ;
  number_of_or += ARV_PRP_AND_OR ;           
  number_of_not += ARV_PRP_AND_NOT ;           
  busy_node = b ;
  match_node = q ;
  prop_error_node = error_node = er ;
  if( overwrap_flag  ) {
    systemverilog_node *ovr ;
    if( pm ) ovr = node_and( b, pm ) ;
    else ovr = b ;
    if( overwrap_node ) overwrap_node = node_or( overwrap_node, ovr ) ;
    else overwrap_node = ovr ;
  }
}


static void gen_con_rep_e( sva_node *sva )
{
  if( sva->min_cyc == 0 ) {
    fprintf( 
      stderr, "Error at %d in %s: Null repetition is not supported\n",
      sva->linenum, sva->filename
    ) ;
    exit(1) ;
  }
  if( sva->max_cyc == 0 && sva->min_cyc <= arv_use_flat_rep ) {
    // Flat expansion of the logic
    int i  ;
    systemverilog_node *pm, *nm, *orb, *lgc ;
    orb = NULL ;
    pm = match_node ;
    if( match_node )   match_node = node_and( match_node, sva->exp ) ;
    else match_node = sva->exp ;
    orb = match_node ;
    //if( busy_node ) busy_node = node_or( busy_node, match_node ) ;
    //else busy_node = match_node;
    // for [* n ], we need n-1 stages 
    //   x [* 3 ] =>  x ##1 x ##1 x 
    for( i = 1 ; i < sva->min_cyc ; i++ ) {
      if( fmatch_node ) {
        lgc = node_sync_c( match_node, fmatch_node ) ;
      }
      else lgc = node_sync( match_node ) ;
      match_node = node_and( lgc, sva->exp ) ;
      
      if( error_check || initial_check ) {
        nm = node_not( sva->exp ) ;
        lgc = node_and( lgc, nm ) ;
	if( initial_check ) lgc = node_and( error_enable_node, lgc ) ;
        if( error_node ) error_node = node_or( lgc, error_node ) ;
        else error_node = lgc ;
      }
    }
    if( (error_check || initial_check) && sva->min_cyc == 1 && pm) {
      lgc = node_not( sva->exp ) ;
      lgc = node_and( lgc, pm ) ;
      if( initial_check ) lgc = node_and( error_enable_node, lgc ) ;
      if( error_node ) error_node = node_or( lgc, error_node ) ;
      else error_node = lgc ;
    }
  }
  else {
    if( sva->max_cyc < 0 ) {
      fprintf( 
        stderr, "Error at %d in %s: Unbounded repetition is not supported\n",
        sva->linenum, sva->filename
      ) ;
      exit( 1 ) ;
    }
    else {
      if( !sva->simple_delay && sva->max_cyc <= arv_use_flat_rep ) {
	// Flat expansion of the logic
	int i  ;
	systemverilog_node *nm, *lgc, *pm, *mt ;
	mt = NULL ;
	if( match_node )   pm = node_and( match_node, sva->exp ) ;
	else pm = sva->exp ;
	if( sva->tm_node->attrib == TMA_H && match_node ) { 
	  lgc = node_not( sva->exp ) ;
	  lgc = node_and( lgc, match_node ) ;
	  if( error_node ) error_node = node_or( lgc, error_node ) ;
	  else error_node = lgc ;
	}
	// for [* n ], we need n-1 stages 
	//   x [* 3 ] =>  x ##1 x ##1 x 
	if( sva->min_cyc == 1 ) mt = pm ;
	for( i = 1 ; i < sva->max_cyc ; i++ ) {
	  if( fmatch_node ) {
	    lgc = node_sync_c( pm, fmatch_node ) ;
	  }
	  else lgc = node_sync( pm ) ;
	  pm = node_and( lgc, sva->exp ) ;
	  if( busy_node ) busy_node = node_or( busy_node, lgc ) ;
	  else busy_node = lgc ;
	  if( i + 1 >= sva->min_cyc ) {
	    if( mt ) mt = node_or( pm, mt ) ;
	    else mt = pm ;
	  }
	}
	match_node = mt ;
      }
      else {
	systemverilog_node *q, *b ;
	int bw = 0 ;
	int tmp, tmin  ;
	if( sva->max_cyc == 0 ) {
	  tmp = sva->min_cyc  ;
	  while( tmp ) {
	    bw++ ;
	    tmp /= 2 ;
	  }
	  tmp = tmin = sva->min_cyc ;	
	}
	else {
	  tmp = sva->max_cyc  ;
	  while( tmp ) {
	    bw++ ;
	    tmp /= 2 ;
	  }
	  tmp = sva->max_cyc  ;
	  tmin = sva->min_cyc ;
	}
	if( tmp > 1 ) { 
	  q = new_wire_node() ;
	  b = new_wire_node() ;
	  if( tmin == 1 ) {
	    fprintf( 
	      out, "  ARV_C_REP_E1 #(%d, %d) arv_crep_e%d (",
	      tmp, bw, label_num++ 
	      ) ;
	  }
	  else {
	    fprintf( 
	      out, "  ARV_C_REP_EN #(%d, %d, %d) arv_crep_e%d (",
	      tmin, tmp, bw, label_num++ 
	      ) ;        
	  }
	  connect_port( "Clk", clock_node, 1 ) ;
	  fprintf( 
	    out, ".RN(%s), .E(%s), .C(%s" , ARV_RESET_, ARV_ENABLE, ARV_CLEAR 
	    ) ;
	  if( fmatch_node ) {
	    fprintf( out, " | " ) ;
	    node_out( fmatch_node ) ;
	  }
	  fprintf( out, ")," ) ;
	  number_of_ff += ARV_C_REP_E_FF * bw ;
	  number_of_and += ARV_C_REP_E_AND * bw ;
	  number_of_or += ARV_C_REP_E_OR * bw ;            
	  number_of_not += ARV_C_REP_E_NOT * bw ; 
	  if( match_node ) 
	    connect_port( "S", match_node, 1 ) ;
	  else fprintf( out, ".S(1'b1), " ) ;
	  connect_port( "D", sva->exp, 1 ) ;
	  connect_port( "Q", q, 1 ) ;
	  connect_port( "B", b, 0 ) ;
	  fprintf( out, " ) ;\n" ) ;
	  if( busy_node ) busy_node = node_or( b, busy_node ) ;
	  else busy_node = b ;
	  //if( overwrap_flag && sva->tm_node->attrib != TMA_none ) {
	  // overwrap should be detected anywhere
	  // When this is used at the top, we won't report overwrap.
	  if( overwrap_flag && match_node ) {
	    systemverilog_node *ovr = node_and( b, match_node ) ;
	    if( overwrap_node ) overwrap_node = node_or( overwrap_node, ovr ) ;
	    else overwrap_node = ovr ;
	  }
	  match_node = q ;
	}
	else {
	  // should not happen
	  fprintf( stderr, 
            "Error at %d in %s: Wrong parameter is given on repetition\n",
 	    sva->linenum, sva->filename
          ) ;
	  exit(1) ;
	}
      }
    }
  }
}

static void gen_con_rep_s( sva_node *sva ) 
{
  systemverilog_node *q, *b ;
  
  if( !is_simple_delay( sva->node_a, 0 ) ){
    fprintf(
      stderr, 
      "Error at %d in %s: Repetition of branching sequence is not supported\n",
      sva->linenum, sva->filename
    ) ;
    exit( 1 ) ;  
  }
  if( sva->max_cyc < 0 ) {
    fprintf( 
      stderr, "Error at %d in %s:Unbounded repetition is not supported\n",
      sva->linenum, sva->filename
    ) ;
    // fix me
    // burf error info here
    exit( 1 ) ;
  }
  if( (sva->max_cyc == 0 && sva->min_cyc == 1) || sva->max_cyc == 1 ) {
    // single repetition is just one sequence
    rtl_generation( sva->node_a, 1 ) ;    
  }
  else {
    systemverilog_node *omp, *tb, *tf, *s, *q, *b, *n, *pe ;
    int bw = 0 ;
    int tmp  ;
    int tby ;
    omp = match_node ;
    if ( match_node == NULL ) {
      // Very first element in a sequence
      tby = get_busy_node ;
      get_busy_node = 1 ;
      rtl_generation( sva->node_a, 1 ) ;
      match_node = node_sync( match_node ) ;
      get_busy_node = tby ;
      if( sva->max_cyc == 0 ) sva->min_cyc-- ;
      else {
        fprintf( 
          stderr, 
          "Error at %d in %s: Branching repetition at the begining of a sequence is not supported\n",
          sva->linenum, sva->filename
        ) ;
        exit(1) ;
        // fix me 
        sva->max_cyc-- ;
        if( sva->min_cyc == 1 ) {
        
        }
        else sva->min_cyc-- ;
      }
    }
    if( sva->max_cyc == 0 ) {
      tmp = sva->min_cyc ;
      while( tmp ) {
	bw++ ;
	tmp /= 2 ;
      }
      tmp = sva->min_cyc ;	
    }
    else {
      tmp = sva->max_cyc ;
      while( tmp ) {
	bw++ ;
	tmp /= 2 ;
      }
      tmp = sva->max_cyc ;
    }
    q = new_wire_node() ;
    b = new_wire_node() ;    
    s = match_node ;
    pe = error_node ;
    match_node = n = new_wire_node() ;
    tb = busy_node ;
    busy_node = NULL ;
    tf = fmatch_node ;
    fmatch_node = q ;
    tby = get_busy_node ;
    get_busy_node = 1 ;
    rtl_generation( sva->node_a, 1 ) ;
    get_busy_node = tby ;
    error_node = pe ;
    fprintf( 
      out, "  ARV_C_REP_S #(%d, %d, %d) arv_crep_s%d (",
      sva->min_cyc, tmp, bw, label_num++ 
    ) ;
    connect_port( "Clk", clock_node, 1 ) ;
    fprintf( 
      out, ".RN(%s), .E(%s), .C(%s" , ARV_RESET_, ARV_ENABLE, ARV_CLEAR 
    ) ;
    if( tf ) {
      fprintf( out, " | " ) ;
      node_out( tf ) ;
    }
    fprintf( out, ")," ) ;   
    connect_port( "S", s, 1 ) ;
    connect_port( "D", match_node, 1 ) ;
    connect_port( "G", busy_node, 1 ) ;
    connect_port( "N", n , 1 ) ;
    connect_port( "Q", q, 1 ) ;
    connect_port( "B", b, 0 ) ;
    fprintf( out, " ) ;\n" ) ;
    number_of_ff += ARV_C_REP_S_FF * bw ;
    number_of_and += ARV_C_REP_S_AND * bw ;
    number_of_or += ARV_C_REP_S_OR * bw ;         
    number_of_not += ARV_C_REP_S_NOT * bw ;         
    if( tb ) busy_node = node_or( b, tb ) ;
    else busy_node = b ;
    fmatch_node = tf ;
    if( overwrap_flag && omp ) {
      systemverilog_node *ovr = node_and( b, omp ) ;
      if( overwrap_node ) overwrap_node = node_or( overwrap_node, ovr ) ;
      else overwrap_node = ovr ;
    }
    match_node = q ;
    
  }
}

static void gen_goto_rep( sva_node *sva )
{
  if( sva->max_cyc < 0 ) {
    fprintf( 
      stderr, 
      "Error at %d in %s: Unbounded repetition is not supported\n",
      sva->linenum, sva->filename
    ) ;
    exit( 1 ) ;
  }
  else {
    systemverilog_node *q, *b ;
    int bw = 0 ;
    int tmp  ;
    if( sva->max_cyc == 0 ) {
      tmp = sva->min_cyc ;
      while( tmp ) {
	bw++ ;
	tmp /= 2 ;
      }
      tmp = sva->min_cyc ;
	
    }
    else {
      tmp = sva->max_cyc ;
      while( tmp ) {
	bw++ ;
	tmp /= 2 ;
      }
      tmp = sva->max_cyc ;
    }
    q = new_wire_node() ;
    b = new_wire_node() ;
    if( tmp == 1 ) {
      fprintf( 
        out, "  ARV_G_REP1 arv_g_rep%d (",
        label_num++ 
      ) ;    
    }
    else {
      fprintf( 
        out, "  ARV_G_REP #(%d, %d, %d) arv_g_rep%d (",
        sva->min_cyc, tmp, bw, label_num++ 
      ) ;
    }
    connect_port( "Clk", clock_node, 1 ) ;
    fprintf( 
      out, ".RN(%s), .E(%s), .C(%s" , ARV_RESET_, ARV_ENABLE, ARV_CLEAR 
      ) ;
    if( fmatch_node ) {
      fprintf( out, " | " ) ;
      node_out( fmatch_node ) ;
    }
    fprintf( out, ")," ) ;
 
    connect_port( "S", match_node, 1 ) ;
    connect_port( "D", sva->exp, 1 ) ;
    connect_port( "Q", q, 1 ) ;
    connect_port( "B", b, 0 ) ;
    fprintf( out, " ) ;\n" ) ;
    number_of_ff += ARV_G_REP_FF * bw ;
    number_of_and += ARV_G_REP_AND * bw ;
    number_of_or += ARV_G_REP_OR * bw ;         
    number_of_not += ARV_G_REP_NOT * bw ;         
    if( busy_node ) busy_node = node_or( b, busy_node ) ;
    else busy_node = b ;
    if( overwrap_flag && match_node ) {
      systemverilog_node *ovr = node_and( b, match_node ) ;
      if( overwrap_node ) overwrap_node = node_or( overwrap_node, ovr ) ;
      else overwrap_node = ovr ;
    }
    match_node = q ;
  }

}

static void gen_seq_or( sva_node *sva ) 
{
  systemverilog_node *tmp, *mp, *bp, *b0 ;
  int ini_chk = initial_check ;
  initial_check = 0 ;
  bp = busy_node ;
  busy_node = NULL ;
  mp = match_node ;
  rtl_generation( sva->node_a, 1 ) ;
  b0 = busy_node ;
  busy_node = NULL ;
  tmp = match_node ;
  match_node = mp ;
  rtl_generation( sva->node_b, 1 ) ;
  match_node = node_or( tmp, match_node ) ;
  if( ini_chk && is_zero_node( sva->node_a ) && is_zero_node( sva->node_b ) ) {
    tmp = node_not( match_node ) ;
    if( mp ) tmp = node_and( tmp, mp ) ;
    if( error_node ) error_node = node_or( tmp, error_node ) ;
    else error_node = tmp ;  
  }
  if( sva->tm_node->attrib != TMA_none ) {
    if( bp) {
      if( b0 ) b0 = node_or( bp, b0 ) ;
      else b0 = bp ;
    }
    if( b0 ) {
      if( busy_node ) busy_node = node_or( b0, busy_node ) ;
      else busy_node = b0 ;
    }
  }
}

static void gen_throughout( sva_node *sva ) 
{
  systemverilog_node *tov, *m, *n, *f, *tf, *tb, *q, *b, *te ;
  int ini_chk = initial_check ;
  initial_check = 0 ;
  tb = busy_node ;
  busy_node = NULL ;
  tov = overwrap_node ;
  m = match_node ;
  match_node = n = new_wire_node() ;
  tf = fmatch_node ;
  fmatch_node = f = new_wire_node() ;
  te = error_node ;
  rtl_generation( sva->node_a, 1 ) ;
  error_node = te ;
  q = new_wire_node() ;
  b = new_wire_node() ;
  fprintf( out, "  ARV_THROUGHOUT arv_throughout%d (", label_num++ ) ;
  connect_port( "Clk", clock_node, 1 ) ;
  fprintf( 
    out, ".RN(%s), .E(%s), .C(%s" , ARV_RESET_, ARV_ENABLE, ARV_CLEAR 
    ) ;
  if( tf ) {
    fprintf( out, " | " ) ;
    node_out( tf ) ;
  }
  fprintf( out, ")," ) ;
  number_of_ff += ARV_THROUGHOUT_FF ;
  number_of_and += ARV_THROUGHOUT_AND ;
  number_of_or += ARV_THROUGHOUT_OR ;          
  number_of_not += ARV_THROUGHOUT_NOT ;          
   
  connect_port( "S", m, 1 ) ;
  connect_port( "G", busy_node, 1 ) ;
  connect_port( "D", match_node, 1 ) ;
  connect_port( "P", sva->exp, 1 ) ;
  connect_port( "N", n, 1 ) ;
  connect_port( "F", f, 1 ) ;
  connect_port( "Q", q, 1 ) ;
  connect_port( "B", b, 0 ) ;
  fprintf( out, " ) ;\n" ) ;
  if( overwrap_flag && sva->tm_node->attrib != TMA_none ) {
    systemverilog_node *ovr = node_and( b, m ) ;
    if( tov ) overwrap_node = node_or( tov, ovr ) ;
    else overwrap_node = ovr ;
  }
  // b = node_or( b, m ) ;
  if( tb ) busy_node = node_or( b, tb ) ;
  else busy_node = b ;
  match_node = q ;
  fmatch_node = tf ;
  
}

static void gen_intersect( sva_node *sva ) 
{
  systemverilog_node *tmp, *mp, *bp, *b0 ;
  bp = busy_node ;
  busy_node = NULL ;
  mp = match_node ;
  rtl_generation( sva->node_a, 1 ) ;
  b0 = busy_node ;
  busy_node = NULL ;
  tmp = match_node ;
  match_node = mp ;
  rtl_generation( sva->node_b, 1 ) ;
  match_node = node_and( tmp, match_node ) ;
  if( sva->tm_node->attrib != TMA_none ) {
    if( bp ) b0 = node_or( bp, b0 ) ;
    busy_node = node_or( b0, busy_node ) ;
  }
}

static void gen_busy_gate() {
  systemverilog_node *tmp, *tmp1 ;
  gate_node = new_wire_node() ;
  tmp = node_not( gate_node ) ;
  tmp1 = node_and( match_node, tmp ) ;
  tmp = node_and( match_node, gate_node ) ;
  if( overwrap_node ) overwrap_node = node_or( tmp, overwrap_node ) ;
  else overwrap_node = tmp ;
  match_node = tmp1 ;
}

static void connect_busy_gate() {
  fprintf( out, "  assign " ) ;
  node_out( gate_node ) ;
  fprintf( out, " = " ) ;
  node_out( busy_node ) ;
  fprintf( out, " ;\n" ) ;
}

static int is_simple_delay( sva_node *sva, int flag ) {
  if( sva->resource ) return 0 ;
  while( sva ) {
    switch( sva->type ) {
    case SE_sequence_item:
      if( sva->node_a ) {
	if( !is_simple_delay( sva->node_a, flag ) ) return 0 ;
      }
      break ;
    case SE_expression:
      break ;
    case SE_delay:
      if(!sva->simple_delay || (flag && sva->min_cyc >= arv_use_counter) ) return 0 ;
      break ;
    case SE_and:
      return 0 ;
      break ;
    case SE_or:
      return 0 ;
      break ;
    case SE_intersect:
      return 0 ;
      break ;
    case SE_within:
      return 0 ;
      break ;
    case SE_throughout:
      return 0 ;
      break ;
    case SE_first_match:
      return 0 ;
      break ;
    case SE_clock:
      //if( !is_simple_delay( sva->node_a ) ) return 0 ;
      break ;
    case SE_consective_repetition:
      if( sva->max_cyc != 0 || (flag && sva->min_cyc > arv_use_flat_rep) || sva->node_a != NULL ) return 0 ;
      break ;
    case SE_goto_repetition:
      return 0 ;
      break ;
    case SE_nonconsective_repetition:
      return 0 ;
      break ;
    case SE_sequence_dcl:
      //if( !is_simple_delay( sva->node_a, flag ) ) return 0 ;
      break;
    case SE_sequence_instance:
      //if( !is_simple_delay( sva->node_a, flag ) ) return 0 ;
      break ;
    case SE_sequence_expr:
      //if( !is_simple_delay( sva->node_a ) ) return 0 ;
      break ;
    case SE_argument: // not used?
      return 0 ;
      break ;
    case SE_match_item_assign:
      return 0 ;
      break ;
    case SE_match_item_inc_or_dec_identifier:
      return 0 ;
      break ;
    case SE_match_item_identifier_inc_or_dec:
      return 0 ;
      break ;
    }
    sva = sva->next ;
  }
  return 1 ;
}

static void gen_local_var( sva_node *var ) {
  int i, j ;
  int lvar_count = 0 ;
  sva_node *tmp = var ;
  systemverilog_node *exp ;
  systemverilog_node *s_tmp ;
  int sync_done ;
  kill_line_adjust = 1 ;
  // first count number of expression which using lvar
  while( tmp ) {
    tmp->nm->var_index = label_num++ ;
    lvar_count += tmp->nm->lvar_exp_num ;
    tmp = tmp->next ;
  }
  // output local variable decl
  tmp = var ;
  while( tmp ) {
    rcv_node_out( tmp->data_type ) ;
    fprintf( out, "  %s_%d ;\n", tmp->nm->name, tmp->nm->var_index ) ;
    tmp = tmp->next ;
  }  
  // output local variable sequence match items
  tmp = var ;
  while( tmp ) {
    sync_done = 0 ;
    for( i = 0 ; i < tmp->nm->lvar_acc_num ; i++ ) {
      sva_node *acc = tmp->nm->lvar_acc[i] ;
      acc->seq_match_id = label_num++ ;
      if( sync_input ) {
	s_tmp = gen_sync_input( acc->exp ) ;
      }
      else s_tmp = NULL ;

      // working here
      if( !sync_done && sync_expression && acc->type == SE_match_item_assign )
      {
        rcv_node_out( tmp->data_type ) ;
        fprintf( out, "  %s_%d_l ;\n", tmp->nm->name, tmp->nm->var_index ) ;
        
        if( sync_ff_num > 1 ) {
          int p ;
          int st = label_num ;
          for( p = 0 ; p < sync_ff_num-1 ; p++ ) {
	    rcv_node_out( tmp->data_type ) ;
	    fprintf( out, "  %s%d ;\n", ARV_WIRE, label_num++ ) ;
	  }
          fprintf( out, "  always @( negedge %s or posedge ", ARV_RESET_ ) ;
	  node_out( clock_node ) ;
	  fprintf( out, ") begin\n" ) ;
          fprintf( out, "    if( !%s ) begin\n", ARV_RESET_ ) ;
	  fprintf( out, "      %s_%d_l = 0 ;\n", tmp->nm->name, tmp->nm->var_index ) ;
	    
          for( p = 0 ; p < sync_ff_num-1 ; p++ ) {
	    fprintf( out, "  %s%d = 0 ;\n", ARV_WIRE, st + p ) ;
	  }
          fprintf( out, "    end\n" ) ;
          fprintf( out, "    else begin \n" ) ;
          for( p = 0 ; p < sync_ff_num-1 ; p++ ) {
	    if( p == 0 ) {
	      fprintf( out, "  %s%d <= ", ARV_WIRE, st ) ;
	      if( s_tmp ) rcv_node_out( s_tmp ) ;
	      else rcv_node_out( acc->exp ) ;
	      fprintf( out, "  ; \n" ) ;
	    }
	    else {
	      fprintf( out, "  %s%d <= %s%d ;\n", ARV_WIRE, st + p, ARV_WIRE, st + p - 1 ) ;
	    }
	  }          
	  fprintf( out, "      %s_%d_l <= ", tmp->nm->name, tmp->nm->var_index ) ;

	  fprintf( out, " %s%d ; \n", ARV_WIRE, st + sync_ff_num - 2  ) ;
          fprintf( out, "    end\n" ) ;
	  fprintf( out, "  end \n" ) ;
	  sync_done = 1 ;
        }
        else {
          fprintf( out, "  always @( negedge %s or posedge ", ARV_RESET_ ) ;
	  node_out( clock_node ) ;
	  fprintf( out, ") begin\n" ) ;
          fprintf( out, "    if( !%s ) begin\n", ARV_RESET_ ) ;
	  fprintf( out, "      %s_%d_l = 0 ;\n", tmp->nm->name, tmp->nm->var_index ) ;
          fprintf( out, "    end\n" ) ;
          fprintf( out, "    else begin \n" ) ;
	  fprintf( out, "      %s_%d_l <= ", tmp->nm->name, tmp->nm->var_index ) ;
	  if( s_tmp ) rcv_node_out( s_tmp ) ;
	  else rcv_node_out( acc->exp ) ;
	  fprintf( out, "; \n" ) ;
	  fprintf( out, "    end \n" ) ;
	  fprintf( out, "  end \n" ) ;
	  sync_done = 1 ;
        }
      }
      fprintf( out, "  wire %s%d ; \n", ARV_WIRE, acc->seq_match_id ) ;
      
      
      fprintf( out, "  always @( negedge %s or posedge ", ARV_RESET_ ) ;
      node_out( clock_node ) ;
      fprintf( out, " ) begin\n" ) ;
      fprintf( out, "    if( !%s ) begin\n", ARV_RESET_ ) ;
      fprintf( out, "      %s_%d = 0 ;\n", tmp->nm->name, tmp->nm->var_index ) ;
      fprintf( out, "    end\n" ) ;
      fprintf( out, "    else begin \n" ) ;
      fprintf( out, "      if( %s%d ) begin \n", ARV_WIRE, acc->seq_match_id ) ;
      switch( acc->type ) {
      case SE_match_item_assign:
        fprintf( out, "        %s_%d <= ", tmp->nm->name, tmp->nm->var_index ) ;
        if( sync_expression ) {
          fprintf( out, "%s_%d_l ;\n", tmp->nm->name, tmp->nm->var_index ) ;            }
        else {
	  if( s_tmp ) rcv_node_out( s_tmp ) ;
  	  else rcv_node_out( acc->exp ) ;
	  fprintf( out, "; \n" ) ;        
        }
	break ;
      case SE_match_item_inc_or_dec_identifier:
      case SE_match_item_identifier_inc_or_dec:
        fprintf( out, "        %s_%d = ", tmp->nm->name, tmp->nm->var_index ) ;
        fprintf( out, "%s_%d ", tmp->nm->name, tmp->nm->var_index ) ;
        fprintf( out, "%s ;", acc->operator ) ;
	break ;
      
      }
      fprintf( out, "      end\n" ) ;
      fprintf( out, "    end\n" ) ;
      fprintf( out, "  end\n" ) ;
      
    } // end of for loop
    tmp = tmp->next ;
  }  
  if( lvar_count ) {
    // then allocate sufficient size of buffer
    systemverilog_node **buff = (systemverilog_node **)calloc(lvar_count,sizeof(systemverilog_node*) ) ;
    lvar_count = 0 ;
    tmp = var ;
    // then collect unique expressions that relates to all local vars
    while( tmp ) {
      for( i = 0 ; i < tmp->nm->lvar_exp_num ; i++ ) {
        systemverilog_node *nd = tmp->nm->lvar_exp[i] ;
        for( j = 0 ; j < lvar_count ; j++ ) {
          if( buff[j] == nd ) break ;
        }
        if( j == lvar_count ) buff[lvar_count++] = nd ;
      }
      tmp = tmp->next ;
    }
    // then create expression node for the unique expressions
    for( i = 0 ; i < lvar_count ; i++ ) {
      int t ;
      exp = buff[i] ;
      exp->exp_id = label_num++ ;
      if( sync_expression || sync_input ) {  //check here
        use_exp_id_node = 1 ;
        exp = expression_analysis( exp ) ;
      }
      fprintf( out, "  wire %s%d = ", ARV_WIRE, exp->exp_id ) ;
      t = exp->exp_id ;
      exp->exp_id = 0 ;
      rcv_node_out( exp ) ;
      use_exp_id_node = 0 ;
      exp->exp_id = t ;
      fprintf( out, " ;\n" ) ;
    }
    free( buff ) ;
  }

  kill_line_adjust = 0 ;
}

static int find_lvar_expression( named_node *nm, systemverilog_node *node ) {
  int result = 0 ;
  switch( node->sva_type ) {
  case SV_expression:
  {
    int i ;
    for( i = 0 ; i < node->num_node ; i++ ) {
      result |= find_lvar_expression( nm, node->node[i] ) ;
    }
    return result ;
  }
    break ;
  case SV_par_expression:
    result |= find_lvar_expression( nm, node->node[1] ) ;
    return result ;
    break ;
  case SV_no_compile:
  {
    int i ;
    for( i = 0 ; i < node->num_node ; i++ ) {
      result |= find_lvar_expression( nm, node->node[i] ) ;
    }
    return result ;
  }
    break ;
  case SV_unary_expression:
    result |= find_lvar_expression( nm, node->node[1] ) ;
    return result ;
    break ;
  case  SV_binary_expression:
    result |= find_lvar_expression( nm, node->node[0] ) ;
    result |= find_lvar_expression( nm, node->node[2] ) ;  
    return result ;
    break ;
  case SV_select_expression:
    result |= find_lvar_expression( nm, node->node[0] ) ;
    result |= find_lvar_expression( nm, node->node[2] ) ;
    result |= find_lvar_expression( nm, node->node[4] ) ;
    return result ;
    break ;
  case  SV_identifier:
    if( node->nm ) {
      switch( node->nm->type ) {
      case SV_parameter_name:
	return find_lvar_expression( nm, node->nm->value ) ;
	break ;
      case SV_arg_name:
	if( node->nm->arg_value ) 
	  return find_lvar_expression( nm, node->nm->arg_value ) ;
	else if( node->nm->default_arg_value )
	  return find_lvar_expression( nm, node->nm->default_arg_value ) ;
	break ;
      case SV_localvar_name:
	if( nm == node->nm ) return 1 ;
	else return 0 ;
	break ;
      case SV_port_name:
      case SV_reg_name:
      case SV_net_name:
	return 0 ;
	break ;
      }
    }
    return 0 ;
    break ;
  case SV_hieracy_identifier:
    return 0 ;
    break ;
  case SV_identifier_singlesell:
    return 0 ;
    break ;
  case SV_identifier_rangesell:
    return 0 ;
    break ;
  case SV_sys_function_call:
    return 0 ;
    break ;
  } /* end of block */

}

static sva_node *get_resource_block_end( named_node *nm, sva_node *sva ) {
  sva_node *found = NULL ;

  while( sva ) {
    switch( sva->type ) {
    case SE_expression:
      if( sva->exp->localvar_access ) {
        if( find_lvar_expression( nm, sva->exp ) ) found = sva ;
      }
      break ;
    case SE_delay:
      if( sva->exp && sva->exp->localvar_access ) {
        if( find_lvar_expression( nm, sva->exp ) ) found = sva ;
      }
      break ;
    case SE_and:
    case SE_or:
    case SE_intersect:
    case SE_within:
      if( get_resource_block_end( nm, sva->node_a ) || 
          get_resource_block_end( nm, sva->node_b )    )
      {
        found = sva ;
      }
      break ;
    case SE_throughout:
      if( (sva->exp->localvar_access && find_lvar_expression( nm, sva->exp )) ||
          get_resource_block_end( nm, sva->node_a )  )
      {
        found = sva ;
      }
      break ;
    case SE_first_match:
      if( get_resource_block_end( nm, sva->node_a ) ) found = sva ;
      break ;
    case SE_clock:
      if( get_resource_block_end( nm, sva->node_a ) ) found = sva ;
      break ;
    case SE_consective_repetition:
      if( sva->exp && sva->exp->localvar_access && 
          find_lvar_expression( nm, sva->exp )       
        ) found = sva ;
      if( sva->node_a && get_resource_block_end( nm, sva->node_a ) )
        found = sva ;
      break ;
    case SE_goto_repetition:
      if( sva->exp && sva->exp->localvar_access && 
          find_lvar_expression( nm, sva->exp )       
        ) found = sva ;
      break ;
    case SE_nonconsective_repetition:
      // not supported
      break ;
    case SE_sequence_dcl:
      //if( sva->node_a && get_resource_block_end( nm, sva->node_a ) )
      //  found = sva ;
      break;
    case SE_sequence_instance:
      //if( sva->node_a && get_resource_block_end( nm, sva->node_a ) )
      //  found = sva ;
      break ;
    case SE_sequence_expr:
      //if( sva->node_a && get_resource_block_end( nm, sva->node_a ) )
      //  found = sva ;
      break ;
    case SE_sequence_item:
      if( sva->exp && sva->exp->localvar_access && 
          find_lvar_expression( nm, sva->exp )       
        ) found = sva ;
      break ;
    case SE_argument: // not used?
      break ;
    case SE_match_item_assign:
      break ;
    case SE_match_item_inc_or_dec_identifier:
      break ;
    case SE_match_item_identifier_inc_or_dec:
      break ;
    case PR_seq:
    case PR_not:
      if( get_resource_block_end( nm, sva->node_a )  )
      {
        found = sva ;
      }
      break ;
    case PR_or:
    case PR_and:
      break ;
    case PR_overlap_implication:
    case PR_non_overlap_implication:
      if( get_resource_block_end( nm, sva->node_a )  )
      {
        found = sva ;
      }
      break ;
    case PR_if_else_property:
      break ;
    case PR_clock_property:
      break ;
    case PR_property_instance:
      break ;
    case PR_property_dcl:
      break ;
    case PR_property_inst:
      break ;
    }
    sva = sva->next ;
  }
  return found ;
}

static void gen_dispatch_rtls ( sva_node *sva, int depth, int gen_error, int sub_proc ) {
  int i ;
  systemverilog_node *match_array[8] ;
  systemverilog_node *busy_array[8] ;
  systemverilog_node *error_array[8] ;
  systemverilog_node *q_array[8] ;
  systemverilog_node *e_array[8] ;
  systemverilog_node *fm_array[8] ;
  systemverilog_node *ovflw ;
  systemverilog_node *pm, *pb, *pe,  *tmp ;
  int pi = initial_check ;
  sva_node *ps = sva_stack ;
  pm = match_node ;  
  pb = busy_node ;
  pe = error_node ;
  for( i = 0 ; i < depth ; i++ ) {
    busy_array[i] = new_wire_node() ;
    match_array[i] = new_wire_node() ;
    if( gen_error ) {
      fm_array[i] = new_wire_node() ;
    }
  }
  ovflw = new_wire_node() ;
  fprintf(
    out, "ARV_DISPATCH_%d arv_dispatch_%d ( ", depth, label_num++
  ) ;
  connect_port( "Clk", clock_node, 1 ) ;
  fprintf( out, ".RN(%s), .E(%s),", ARV_RESET_, ARV_ENABLE ) ;
  connect_port( "D", match_node, 1 ) ;
  fprintf( out, " .C(%s", ARV_CLEAR ) ;
  if( !gen_error && fmatch_node ) {
    fprintf( out, " | " ) ;
    node_out( fmatch_node ) ;
  }
  fprintf( out, "), " ) ;
  for( i = 0 ; i < depth ; i++ ) {
    fprintf( out, ".B%d(", i+1 ) ;
    node_out(busy_array[i]) ;
    fprintf( out, ")," ) ;
    fprintf( out, ".Q%d(", i+1 ) ;
    node_out( match_array[i] ) ;
    fprintf( out, ")," ) ;
  }
  connect_port( "OW", ovflw, 0 ) ;
  
  fprintf( out, " ) ;\n" ) ;
    
  for( i = 0 ; i < depth ; i++ ) {
    busy_node = NULL ;
    error_node = NULL ;
    block_busy_node = NULL ;
    initial_check = pi ;
    sva_stack = ps ;
    match_node = match_array[i] ;
    if( gen_error ) fmatch_node = fm_array[i] ;
    prev_attrib = SVN_none ;
    rtl_generation( sva, sub_proc ) ;
    fprintf( out, "  assign " ) ;
    node_out( busy_array[i] ) ;
    fprintf( out, " = " ) ;
    if( block_busy_node ) {
      node_out( block_busy_node ) ;
    }
    else {
      if( busy_node ) node_out( busy_node ) ;
      else fprintf( out, " 1'b0 " ) ;
    }
    fprintf( out, "  ; /* connect block busy */\n" ) ;
    q_array[i] = match_node ;
    e_array[i] = error_node ; // possible local error 
  }
  
  // pop duplication stack
  prev_attrib = sva->p_attrib ;
  sva_stack = sva->p_stack ;
  
  match_node = q_array[0] ;
  for( i = 1 ; i < depth ; i++ ) {
    match_node = node_or( match_node, q_array[i] ) ;
  }

  if( overwrap_node ) overwrap_node = node_or( ovflw, overwrap_node ) ;
  else overwrap_node = ovflw ;
  
  if( gen_error ) {
    for( i = 0 ; i < depth ; i++ ) {
      // connect first match here
      fprintf( out, "  assign " ) ;
      node_out( fm_array[i] ) ;
      fprintf( out, " = " ) ;
      node_out( q_array[i] ) ;
      fprintf( out, "  ; /* connect first_match[%d] */ \n", i ) ;
      error_array[i] = new_wire_node() ;
      fprintf( out, "  ARV_ERROR_GEN arb_error_gen%d ( ", label_num++ ) ;
      connect_port( "Clk", clock_node, 1 ) ;
      fprintf( 
	out, ".RN(%s), .E(%s), .C(%s)," , ARV_RESET_, ARV_ENABLE, ARV_CLEAR 
	) ; 
      connect_port( "B", busy_array[i], 1 ) ;
      connect_port( "M", q_array[i], 1 ) ;
      connect_port( "ER", error_array[i], 0 ) ;
      fprintf( out, ") ;\n" ) ;
      number_of_ff += ARV_ERROR_GEN_FF ;
      number_of_and += ARV_ERROR_GEN_AND ;
      number_of_or += ARV_ERROR_GEN_OR ;            
      number_of_not += ARV_ERROR_GEN_NOT ; 
      if( e_array[i] ) error_array[i] = node_or( e_array[i], error_array[i] ) ;
    }
    prop_error_node = error_array[0] ;
    for( i = 1 ; i < depth ; i++ ) {
      prop_error_node = node_or( prop_error_node, error_array[i] ) ;
    }
  }
  else {
    if( pb ) busy_node = node_or( busy_array[0], pb ) ;
    else busy_node = busy_array[0] ;
    if( pe && e_array[0] ) error_node = node_or( e_array[0], pe ) ;
    else error_node = e_array[0] ;  
    for( i = 1 ; i < depth ; i++ ) {
      busy_node = node_or( busy_node, busy_array[i] ) ;
      if( error_node && e_array[i] ) {
        error_node = node_or( error_node, e_array[i] ) ;
      }
    }
    prop_error_node = error_node ;
  }
  
}

static int in_duplicate = 0 ;

static void rtl_generation( sva_node *sva, int sub_prop ) {
  systemverilog_node *pm, *tmp ;
  sva_node *tn ;
  
  int c_flag = 0 ;
  while( sva ) {
    tn = NULL ;
    if( !in_duplicate && sva->resource == RCS_block ) {
      in_duplicate = 1 ;
      tn = sva->act_var_node ;
    }
    else if( sva->type != PR_overlap_implication && 
        sva->type != PR_non_overlap_implication &&
        iovwp_depth > 1 && 
        prev_attrib == SVN_branch && sva->resource != RCS_free )
    {
      if( prev_branch_depth && ( prev_branch_depth < iovwp_depth ) ) 
        iovwp_depth = prev_branch_depth ;
      if( sva->next && sva->next->resource == RCS_block ) {
        in_duplicate = 1 ;
        tn = sva->next->act_var_node ;
      }
      else  tn = sva ;
    }
    if( tn ) {
      tn->p_attrib = prev_attrib ;
      tn->p_stack = sva_stack ;
      sva_stack = tn ;
      prev_attrib = SVN_none ;
      //if( sva->type == PR_seq ) 
      //  gen_dispatch_rtls( sva, iovwp_depth, 1, sub_prop ) ;
      //else
        gen_dispatch_rtls( sva, iovwp_depth, 0, sub_prop ) ;
      prev_branch_depth = 0 ;
      c_flag = 1 ;
    }
    if( !c_flag ) {
      if( sva->error_check ) error_check = 1 ;
      if( sva->initial_check ) initial_check = 1 ;
    }
    if ( !c_flag ) switch( sva->type ) {
    case SE_sequence_item:
      pm = match_node ;
      if( match_node ) {
        if( error_check ) {
          tmp = node_not( sva->exp ) ;
          tmp = node_and( match_node, tmp ) ;
          if( error_node ) {
            error_node = node_or( error_node, tmp ) ;
          }
          else {
            error_node = tmp ;
          }
        }
        match_node = node_and( match_node, sva->exp ) ;
      }
      else {
        match_node = sva->exp ;
        if( error_check ) {
          tmp = node_not( sva->exp ) ;
          if( error_node ) {
            error_node = node_or( error_node, tmp ) ;
          }
          else {
            error_node = tmp ;
          }
        }
      }
      if( sva->node_a ) {
        rtl_generation( sva->node_a, 1 ) ;
      }
      else {
        if( !busy_node ) busy_node = pm ;
      }
      if( sva->node_b ) { // sequence match item
        fprintf( out, "  assign %s%d = ", ARV_WIRE, sva->node_b->seq_match_id ) ;
        node_out( match_node ) ;
        fprintf( out, " ; /* assign sequence match trigger */\n" ) ;
      }
      break ;
    case SE_expression:
      if( match_node ) {
        if( error_check || initial_check ) {
          tmp = node_not( sva->exp ) ;
          tmp = node_and( match_node, tmp ) ;
          if( initial_check ) tmp = node_and( error_enable_node, tmp ) ;
          if( error_node ) {
            error_node = node_or( error_node, tmp ) ;
          }
          else {
            error_node = tmp ;
          }
        }
        match_node = node_and( match_node, sva->exp ) ;
      }
      else {
        match_node = sva->exp ;
        if( error_check || initial_check ) {
          tmp = node_not( sva->exp ) ;
          if( initial_check ) tmp = node_and( error_enable_node, tmp ) ;
          if( error_node ) {
            error_node = node_or( error_node, tmp ) ;
          }
          else {
            error_node = tmp ;
          }
        }
      }
      if( sva->node_b ) { // sequence match item
        fprintf( out, "  assign %s%d = ", ARV_WIRE, sva->node_b->seq_match_id ) ;
        node_out( match_node ) ;
        fprintf( out, " ; /* assign sequence match trigger */\n" ) ;
      }
      //if( get_busy_node && initial_check ) {
      //  if( busy_node ) busy_node = node_or( busy_node, match_node ) ;
      //  else busy_node = match_node ;
      //}
      initial_check = 0 ;
      // busy_node = enable_node ;
      break ;
    case SE_delay:
      gen_delay( sva ) ;
      initial_check = 0 ;
      break ;
    case SE_and:
      gen_seq_and( sva ) ;
      initial_check = 0 ;
      break ;
    case SE_or:
      gen_seq_or( sva ) ;
      initial_check = 0 ;
      break ;
    case SE_intersect:
      gen_intersect( sva ) ;
      initial_check = 0 ;
      break ;
    case SE_within:
      fprintf( 
        stderr, 
        "Error at %d in %s: Operator 'within' not supported yet.",
        sva->linenum, sva->filename
      ) ;
      exit(1) ;
      break ;
    case SE_throughout:
      gen_throughout( sva ) ;
      initial_check = 0 ;
      break ;
    case SE_first_match:
    { 
      systemverilog_node *tmp ;
      if( !fmatch_node && sva->tm_node->attrib == TMA_none ) {
        //int t = use_pipe_delay ;
        //use_pipe_delay = 1 ;
        rtl_generation( sva->node_a, 1 ) ;
        //use_pipe_delay = t ;
      }
      else {
        tmp = fmatch_node ;
        fmatch_node = new_wire_node() ;
        rtl_generation( sva->node_a, 1 ) ;
        connect_first_match() ;
        fmatch_node = tmp ;
      }
      if( sva->node_b ) { // sequence match item
        fprintf( out, "  assign %s%d = ", ARV_WIRE, sva->node_b->seq_match_id ) ;
        node_out( match_node ) ;
        fprintf( out, " ; /* assign sequence match trigger */\n" ) ;
      }
    }
      initial_check = 0 ;
      break ;
    case SE_clock:
      clock_node = sva->clock ;
      break ;
    case SE_consective_repetition:
    {
      if( sva->node_a == NULL ) {
	gen_con_rep_e( sva ) ;
      }
      else {
	gen_con_rep_s( sva ) ;
      }
      if( sva->node_b ) { // sequence match item
        fprintf( out, "  assign %s%d = ", ARV_WIRE, sva->node_b->seq_match_id ) ;
        node_out( match_node ) ;
        fprintf( out, " ; /* assign sequence match trigger */\n" ) ;
      }      
    } 
      initial_check = 0 ;
      break ;
    case SE_goto_repetition:
      if( sva->node_a != NULL ) {
        fprintf( 
          stderr, 
          "Error at %d in %s: GOTO repetition can't take sequence\n",
          sva->linenum, sva->filename
        ) ;
        exit( 1 ) ;
      }
     gen_goto_rep( sva ) ;
     if( sva->node_b ) { // sequence match item
        fprintf( out, "  assign %s%d = ", ARV_WIRE, sva->node_b->seq_match_id ) ;
        node_out( match_node ) ;
        fprintf( out, " ; /* assign sequence match trigger */\n" ) ;
      }
      initial_check = 0 ;
     break ;
    case SE_nonconsective_repetition:
      fprintf( 
        stderr, 
        "Error at %d in %s: Non Consective Repeat is not supported\n",
        sva->linenum, sva->filename
      ) ;
      exit( 1 ) ;
      break ;
    case SE_local_var_dcl:
      if( sva->var_list ) gen_local_var( sva->var_list ) ;
      break ;  
    case SE_sequence_dcl:
      if( sva->var_list ) gen_local_var( sva->var_list ) ;
      break;
    case SE_sequence_instance:
      break ;
    case SE_sequence_expr:
      break ;
    case SE_argument: // not used?
      break ;
    case SE_match_item_assign:
      fprintf( out, "  assign %s%d = ", ARV_WIRE, sva->seq_match_id ) ;
      node_out( match_node ) ;
      fprintf( out, " ; /* assign sequence match trigger */\n" ) ;
      break ;
    case SE_match_item_inc_or_dec_identifier:
      fprintf( out, "  assign %s%d = ", ARV_WIRE, sva->seq_match_id ) ;
      node_out( match_node ) ;
      fprintf( out, " ; /* assign sequence match trigger */\n" ) ;
      break ;
    case SE_match_item_identifier_inc_or_dec:
      fprintf( out, "  assign %s%d = ", ARV_WIRE, sva->seq_match_id ) ;
      node_out( match_node ) ;
      fprintf( out, " ; /* assign sequence match trigger */\n" ) ;
      break ;
    case PR_seq:
      // case a sequence is directly used as a property
      // evaluation will be done every cycle
      if( sub_prop ) {
        rtl_generation( sva->node_a, 1 ) ;         
      }
      else {
	// match_node = NULL ;  // evaluate everycycle
        if( enable_node ) {
          if( match_node ) match_node = node_and( enable_node, match_node ) ;
          else match_node = enable_node ;
	}
        if( disable_node ) {
          systemverilog_node *en = node_not( disable_node ) ;
          if( match_node ) match_node = node_and( en, match_node ) ;
          else match_node = en ;
        }
        if( is_zero_node( sva->node_a ) ) {
	  initial_check = 1 ;
	  rtl_generation( sva->node_a, 1 ) ; 
	  prop_error_node = error_node ;
	}
	else {
	  if( is_simple_delay( sva->node_a, 1 ) ) {
	    error_check = 1 ;
	    initial_check = 1 ;
	    simple_pipe = 1 ;
	    rtl_generation( sva->node_a, 1 ) ; 
	    prop_busy_node = busy_node ;          
	  }
	  else {
	    systemverilog_node *tmp, *tmp1 ;
	    int tby ;
	    initial_check = 1 ;  // error check if first node is expression     
	    // generating busy gate by connecting !busy as match_node
	    if( match_node == NULL ) match_node = tmp = new_wire_node() ;
	    else tmp = NULL ;
	    tby = get_busy_node ;
            get_busy_node = 1 ;
	    rtl_generation( sva->node_a, 1 ) ; 
            get_busy_node = tby ;
	    prop_busy_node = busy_node ;
	    // connecting match to busy
	    if( tmp ) {
	      if( busy_node ) {
	        tmp1 = node_not( busy_node ) ;
	        fprintf( out, "  assign " ) ;
	        node_out( tmp ) ;
	        fprintf( out, " = " ) ;
	        node_out( tmp1 ) ;
	        fprintf( out, " ;\n" ) ;	      
	      }
	      else {
	        fprintf( out, "  assign " ) ;
	        node_out( tmp ) ;
	        fprintf( out, " = 1'b1 ;\n" ) ;	      
	      }
	    }
	    if( overwrap_flag && tmp ) {
	      overwrap_node = prop_busy_node ;
	    }
    	  }
	  if( tmp ) gen_error(1, 1) ;
	  else gen_error( 0, 1 ) ;
	  error_check = 0 ;
	}
      }
      break ;
    case PR_not:
    {
      systemverilog_node *tmp ;
      rtl_generation( sva->node_a, 0 ) ; 
      tmp = prop_error_node ;
      if( antece_error_node ) {
        prop_error_node = node_or( antece_error_node, match_node ) ; 
      }
      else prop_error_node = match_node ;
      match_node = tmp ;
    }
      break ;
    case PR_or:
      gen_prop_or( sva ) ;
      break ;
    case PR_and:
      gen_prop_and( sva ) ;
      break ;
    case PR_overlap_implication:
    case PR_non_overlap_implication:
    {
      systemverilog_node *tmp, *tmp1 ;
      int err_gen = 0 ;
      if( sva->invert ) {
        if( !sva->antece_zero ) 
        {
          gen_error(0, 1) ;
          antece_error_node = prop_error_node ;
        }
        else {
          antece_error_node = node_sync( error_node ) ;        
        }
        prop_error_node = NULL ;
      }
      if( enable_node ) match_node = node_and( enable_node, match_node ) ;
      if( disable_node ) {
        systemverilog_node *en = node_not( disable_node ) ;
        match_node = node_and( en, match_node ) ;
      }
      prop_busy_node = busy_node ;
      if( sva->type == PR_non_overlap_implication ) {
	match_node = node_sync( match_node ) ;
	if( busy_node ) prop_busy_node = node_or( busy_node, match_node ) ;
	else prop_busy_node = match_node ;
	if( overwrap_depth > 1 && sva->resource == RCS_free ) {
           if( busy_node ) block_busy_node = node_or( busy_node, match_node ) ;
           else block_busy_node = match_node ;
        }
      }
      else {
	prop_busy_node = busy_node ;
      }
      error_node = NULL ;
      busy_node = NULL ;
      prop_error_node = NULL ;
      if( is_zero_node( sva->node_a ) ) {
        tmp = match_node ;
        rtl_generation( sva->node_a, 1 ) ; 
        tmp1 = node_not( match_node ) ;
        error_node = node_and( tmp, tmp1 ) ;
	gen_error_zero(1) ;
      }
      else {
        if( is_simple_delay( sva->node_a, 1 ) ) {
           error_check = 1 ;
           simple_pipe = 1 ;
	   //use_pipe_delay = 1 ;
           rtl_generation( sva->node_a, 1 ) ; 
	   if( prop_busy_node && busy_node ) {
             prop_busy_node = node_or( busy_node, prop_busy_node ) ;
           }
	   else {
             if( busy_node ) prop_busy_node = busy_node ;
           }
        }
        else {
          initial_check = 1 ;  // error check if first node is expression
          error_check = 0 ;  // clear error check flag
          if( overwrap_depth > 1 ) {
            if( sva->resource != RCS_free ) {
              if( internal_overwrap_flag ) {
                iovwp_depth = overwrap_depth ;
	      }
              else iovwp_depth = 0 ;
              prev_attrib = SVN_none ;
              gen_dispatch_rtls( sva->node_a, overwrap_depth, 1, 1 ) ;
              err_gen = 1 ;
            }
            else {
              // This means imply is contained in previous duplication
              if( internal_overwrap_flag ) iovwp_depth = overwrap_depth ;
              else iovwp_depth = 0 ;           
              prev_attrib = SVN_none ;
              fmatch_node = new_wire_node() ;
              gen_busy_gate() ;
              rtl_generation( sva->node_a, 1 ) ; 
              connect_busy_gate() ;
              connect_first_match() ; 
              if( block_busy_node ) 
		block_busy_node = node_or( busy_node, block_busy_node ) ;
              else block_busy_node = busy_node ;
	      if( prop_busy_node && busy_node ) 
		prop_busy_node = node_or( busy_node, prop_busy_node ) ;
              else {
                if( busy_node ) prop_busy_node = busy_node ;
	      }
            }
          }
          else {
            fmatch_node = new_wire_node() ;
            gen_busy_gate() ;
            rtl_generation( sva->node_a, 1 ) ; 
            connect_busy_gate() ;
            connect_first_match() ;
	    if( prop_busy_node && busy_node ) 
	      prop_busy_node = node_or( busy_node, prop_busy_node ) ;
            else prop_busy_node = busy_node ;          
	  }
        }
        if( !err_gen ) gen_error(1,0) ;
        error_check = 0 ;
        //use_pipe_delay = 0 ;
        simple_pipe = 0 ;
      }
    }
     break ;

    case PR_if_else_property:
    {
      systemverilog_node *tmp ;
      enable_node = sva->exp ;
      rtl_generation( sva->node_a, 0 ) ;
      tmp = match_node ;
      match_node = NULL ;
      if( sva->node_b ) {
        enable_node = node_not( sva->exp ) ;
        rtl_generation( sva->node_b, 0 ) ;
        match_node = node_or( tmp, match_node ) ;
      }
      else match_node = tmp ;
    }
      break ;
    case PR_clock_property:
      clock_node = sva->clock ;
      break ;
    case PR_property_instance:
      break ;
    case PR_property_dcl:
      if( sva->clock ) clock_node = sva->clock ;
      if( sva->disable_expression ) disable_node = sva->disable_expression ;
      if( sva->var_list ) gen_local_var( sva->var_list ) ;
      break ;
    case PR_property_inst:
      clock_node =  sva->clock ;
      disable_node = sva->disable_expression ;
      break ;
    }
    if( sva_stack == sva ) {
      //prev_attrib = sva->p_attrib ;
      //sva_stack = sva->p_stack ;
      return ;
    }
    if( c_flag ) {
      // skip to duplicate end point
      c_flag = 0 ;
      sva = tn ;
      in_duplicate = 0 ;
    }
    if( !internal_filter_flag ) {
      if( (prev_attrib == SVN_branch && sva->attrib == SVN_filter) || 
	  sva->attrib == SVN_brfilter ) 
      {
	prev_attrib = SVN_branch ;
      }
      else prev_attrib = sva->attrib ;
    }
    else prev_attrib = sva->attrib ;
    sva = sva->next ;
    //if( sva ) {
    //  if( enable_node ) enable_node = node_and( enable_node, match_node ) ;
    //  else enable_node = match_node ;
    //  match_node = NULL ;
    //}
  }
}


/* ANSI version port declaration */
static void additional_port_dcl_list_out() {
  fprintf( out, ",\n  input %s,\n", ARV_RESET_ ) ;
  fprintf( out, "  input %s,\n", ARV_CLEAR ) ;
  fprintf( out, "  input %s", ARV_ENABLE ) ;
  if( current_module->num_error_vector ) {
    if( current_module->num_error_vector > 1 ) {
      fprintf( 
	out, ",\n  output [%d:0] %s", current_module->num_error_vector-1, ARV_ERROR 
      ) ;
      if( match_flag ) {
        fprintf( 
  	  out, ",\n  output [%d:0] %s", current_module->num_error_vector-1, ARV_MATCH 
        ) ;      
      }
    }
    else {
      fprintf( out, ",\n  output %s", ARV_ERROR ) ;
      if( match_flag ) {
        fprintf( out, ",\n  output %s", ARV_MATCH ) ;      
      }
    }
  }
  if( current_module->num_cover_vector ) {
    if( current_module->num_cover_vector > 1 ) {
      fprintf(
        out, ",\n  output [%d:0] %s",
        current_module->num_cover_vector-1, ARV_COVER 
      ) ;
    }
    else {
      fprintf( out, ",\n  output %s", ARV_COVER ) ;
    }
  }
  if( overwrap_flag && (current_module->num_error_vector || current_module->num_cover_vector ) ) {
    if( (current_module->num_error_vector+current_module->num_cover_vector) > 1 ) {
      fprintf(
        out, ",\n  output [%d:0] %s",
        (num_error_vector + num_cover_vector)-1, ARV_OVERWRAP 
      ) ;    
    }
    else fprintf( out, ",\n  output %s", ARV_OVERWRAP ) ;
  }
  fprintf( out, "\n" ) ;
  
}

static void additional_port_list_out( int flag ) {
  if( flag ) fprintf( out, ",\n" ) ;
  fprintf( out, "  %s,\n", ARV_RESET_ ) ;
  fprintf( out, "  %s,\n", ARV_CLEAR ) ;
  fprintf( out, "  %s", ARV_ENABLE ) ;
  if( current_module->num_error_vector ) {
    fprintf( out, ",\n  %s", ARV_ERROR ) ;
    if( match_flag ) 
      fprintf( out, ",\n  %s", ARV_MATCH ) ;
  }
  if( current_module->num_cover_vector ) 
    fprintf( out, ",\n  %s", ARV_COVER ) ;
  if( overwrap_flag && ( current_module->num_cover_vector + current_module->num_error_vector ) > 0 ) {
    fprintf( out, ",\n  %s", ARV_OVERWRAP ) ;
  }
  fprintf( out, "\n" ) ;
}

additional_port_decl_out() {
  fprintf( out, "\n  input %s ;\n", ARV_RESET_ ) ;
  fprintf( out, "  input %s ;\n", ARV_CLEAR ) ;
  fprintf( out, "  input %s ;\n", ARV_ENABLE ) ;
  if( current_module->num_error_vector ) {
    // report number of vector
    fprintf( stderr, "Error Vector: %s %d\n", current_module->node[2]->name, current_module->num_error_vector ) ;
    if( current_module->num_error_vector > 1 ) {
      fprintf( 
	out, "  output [%d:0] %s ;\n", current_module->num_error_vector-1, ARV_ERROR 
      ) ;
      if( match_flag ) {
        fprintf( 
  	  out, "  output [%d:0] %s ;\n", current_module->num_error_vector-1, ARV_MATCH 
        ) ;
      }
    }
    else {
      fprintf( out, "  output %s ;\n", ARV_ERROR ) ;
      if( match_flag ) {
        fprintf( out, "  output %s ;\n", ARV_MATCH ) ;    
      }
    }
  }
  if( current_module->num_cover_vector ) {
    fprintf( stderr, "Cover Vector: %s %d\n", current_module->node[2]->name, current_module->num_cover_vector ) ;
    if( current_module->num_cover_vector > 1 ) {
      fprintf(
        out, "  output [%d:0] %s ;\n",
        current_module->num_cover_vector-1, ARV_COVER 
      ) ;
    }
    else {
      fprintf( out, "  output %s ;\n", ARV_COVER ) ;
    }
  }
  if( overwrap_flag && ( current_module->num_cover_vector + current_module->num_error_vector ) > 0 ) {
    fprintf( stderr, "Overwrap Vector: %s %d\n", current_module->node[2]->name, current_module->num_cover_vector + current_module->num_error_vector ) ;
    if( (current_module->num_cover_vector + current_module->num_error_vector) > 1 ) {
      fprintf(
        out, "  output [%d:0] %s ;\n",
        (current_module->num_error_vector + current_module->num_cover_vector)-1, ARV_OVERWRAP
      ) ;
    }
    else {
      fprintf( out, "  output %s ;\n", ARV_OVERWRAP ) ;
    }
  }
}

static parameter_decl_out()
{
  fprintf( out, "  parameter %s = %d ;\n", ARV_SYNC_FF_NUM, sync_ff_num ) ;
}

static systemverilog_node *gen_sync_input( systemverilog_node *node ) 
{
  int sync_id ;
  int bus_size ;
  int i ;
  systemverilog_node *nd  = node ;
  if( node == NULL ) return node ;
  switch( node->sva_type ) {
  case SV_par_expression:
    node->node[1] = gen_sync_input( node->node[1] ) ;
    break ;
  case SV_unary_expression:
    node->node[1] = gen_sync_input( node->node[1] ) ;
    break ;
  case SV_binary_expression:
    node->node[0] = gen_sync_input( node->node[0] ) ;
    node->node[2] = gen_sync_input( node->node[2] ) ;
    break ;
  case SV_select_expression:
    node->node[0] = gen_sync_input( node->node[0] ) ;
    node->node[2] = gen_sync_input( node->node[2] ) ;
    node->node[4] = gen_sync_input( node->node[4] ) ;  
    break ;
  // expr_primary 
  case SV_identifier:
    if( node->nm ) {
      switch( node->nm->type ) {
      case SV_port_name:
      case SV_reg_name:
      case SV_net_name:
	if( node->nm->sync_id ) {
	  sync_id = node->nm->sync_id ;
	}
	else {
	  sync_id = node->nm->sync_id = label_num++ ;
	  if( node->nm->bus_m == 0 && node->nm->bus_n == 0 ) {
	    fprintf( out, "  wire %s%d ; \n", ARV_WIRE, sync_id ) ;
	    fprintf( out,  "  ARV_DFF_E sync_dff%d ( ", label_num++ ) ;
	    connect_port ( "Clk", clock_node, 1 ) ;
	    fprintf( 
	      out, ".RN(%s), .E((~%s) && %s), ", 
	      ARV_RESET_, ARV_CLEAR, ARV_ENABLE 
	      ) ;
	    fprintf( out, ".D(%s),", node->nm->name ) ;
	    fprintf( out, ".Q(%s%d)", ARV_WIRE, sync_id ) ;
	    fprintf( out, " ) ;\n" ) ;
	    number_of_ff++ ;	          
	  }
	  else {
	    if( node->nm->bus_m > node->nm->bus_n ) {
	      bus_size = node->nm->bus_m - node->nm->bus_n + 1 ;
	    }
	    else {
	      bus_size = node->nm->bus_n - node->nm->bus_m + 1 ;
	    }
	    fprintf( 
	      out, "  reg [%d:%d] %s%d ; \n",
	      node->nm->bus_m, node->nm->bus_n, ARV_WIRE, sync_id
	      ) ;
	    number_of_ff += bus_size ;
	    fprintf( out, "  always @( negedge %s or posedge ", ARV_RESET_ ) ;
	    node_out( clock_node ) ;
	    fprintf( out, ") begin\n" ) ;
	    fprintf( out, "    if( !%s ) begin\n", ARV_RESET_ ) ;
	    fprintf( out, "      %s%d = 0 ;\n", ARV_WIRE, sync_id ) ;
	    fprintf( out, "    end\n" ) ;
	    fprintf( out, "    else begin \n" ) ;
	    fprintf(
	      out, "    %s%d <= %s ;\n",
	      ARV_WIRE, sync_id, node->nm->name 
	      ) ;	  
	    fprintf( out, "    end\n" ) ;
	    fprintf( out, "  end\n" ) ;

	  }
        }
        nd = ALLOC_SV_NODE ;
        nd->sva_type = SV_expression ;
        nd->exp_id = sync_id ;
        nd->name = calloc(1, strlen( ARV_WIRE ) + 10 ) ;      
        sprintf( nd->name, "%s%d", ARV_WIRE, nd->exp_id ) ;
      }
    }
    break ;
  case SV_identifier_singlesell:
    if( node->node[0]->nm ) {
      switch( node->node[0]->nm->type ) {
      case SV_port_name:
      case SV_reg_name:
      case SV_net_name:
	if(node->node[0]->nm->sync_id ) {
	  sync_id = node->node[0]->nm->sync_id ;
	}
	else {
	  sync_id = node->node[0]->nm->sync_id = label_num++ ;
	  if( node->node[0]->nm->bus_m == 0 && node->node[0]->nm->bus_n == 0 ) {
	    fprintf( out, "  wire %s%d ; \n", ARV_WIRE, sync_id ) ;
	    fprintf( out,  "  ARV_DFF_E sync_dff%d ( ", label_num++ ) ;
	    connect_port ( "Clk", clock_node, 1 ) ;
	    fprintf( 
	      out, ".RN(%s), .E((~%s) && %s), ", 
	      ARV_RESET_, ARV_CLEAR, ARV_ENABLE 
	      ) ;
	    fprintf( out, ".D(%s),", node->node[0]->nm->name ) ;
	    fprintf( out, ".Q(%s%d)", ARV_WIRE, sync_id ) ;
	    fprintf( out, " ) ;\n" ) ;
	    number_of_ff++ ;	          
	  }
	  else {
	    if( node->node[0]->nm->bus_m > node->node[0]->nm->bus_n ) {
	      bus_size = node->node[0]->nm->bus_m - node->node[0]->nm->bus_n + 1 ;
	    }
	    else {
	      bus_size = node->node[0]->nm->bus_n - node->node[0]->nm->bus_m + 1 ;
	    }
	    fprintf( 
	      out, "  reg [%d:%d] %s%d ; \n",
	      node->node[0]->nm->bus_m, node->node[0]->nm->bus_n, 
	      ARV_WIRE, sync_id
	      ) ;
	    number_of_ff += bus_size ;
	    fprintf( out, "  always @( negedge %s or posedge ", ARV_RESET_ ) ;
	    node_out( clock_node ) ;
	    fprintf( out, ") begin\n" ) ;
	    fprintf( out, "    if( !%s ) begin\n", ARV_RESET_ ) ;
	    fprintf( out, "      %s%d = 0 ;\n", ARV_WIRE, sync_id ) ;
	    fprintf( out, "    end\n" ) ;
	    fprintf( out, "    else begin \n" ) ;
	    fprintf(
	      out, "    %s%d <= %s ;\n",
	      ARV_WIRE, sync_id, node->node[0]->nm->name 
	      ) ;	  
	    fprintf( out, "    end\n" ) ;
	    fprintf( out, "  end\n" ) ;
	  }
        }
	nd = ALLOC_SV_NODE ;
	nd->sva_type = SV_expression ;
	nd->exp_id = sync_id ;
        nd->name = calloc(1, strlen( ARV_WIRE ) + 10 ) ;      
        sprintf( 
          nd->name, "%s%d[%s]", ARV_WIRE, nd->exp_id, node->node[2]->name 
        ) ;
	break ;
      }
    }
    break ;
  case SV_identifier_rangesell:
    if( node->node[0]->nm ) {
      int m, n, s ;
      switch( node->node[0]->nm->type ) {
      case SV_port_name:
      case SV_reg_name:
      case SV_net_name:
	if(node->node[0]->nm->sync_id ) {
	  sync_id = node->node[0]->nm->sync_id ;
	}
	else {
	  sync_id = node->node[0]->nm->sync_id = label_num++ ;    
	  m = get_constant( node->node[2] ) ;
	  n = get_constant( node->node[4] ) ;
	  fprintf(
	    out, "  reg [%d:%d] %s%d ; \n",
	    m, n, ARV_WIRE, sync_id
	    ) ;
	  number_of_ff += (m > n) ? ( m - n + 1 ) : ( n - m + 1 ) ;
	  fprintf( out, "  always @( posedge " ) ;
	  node_out( clock_node ) ;
	  fprintf( out, ") begin\n" ) ;      
	  fprintf( out, "    %s%d <= ", ARV_WIRE, sync_id ) ; 
	  rcv_node_out( node ) ;
	  fprintf( out, " ; \n" ) ;
	  fprintf( out, "  end \n" ) ;
	}
        nd = ALLOC_SV_NODE ;
        nd->sva_type = SV_expression ;
        nd->exp_id = sync_id ;
	nd->name = calloc(1, strlen( ARV_WIRE ) + 10 ) ;      
        sprintf( 
          nd->name, "%s%d[%s:%s]", ARV_WIRE, nd->exp_id, 
          node->node[2]->name, node->node[4]->name
        ) ;
	break ;
      }
    }
  case SV_expression:
  default:
    for ( i = 0 ; i < node->num_node ; i++ ) {
      node->node[i] = gen_sync_input( node->node[i] ) ;
    }    
    break ;
  }
  return nd ;
}

static int get_bitsize( systemverilog_node *node ) 
{
  int s0, s1 ;
  int i ;
  systemverilog_node *nd  = node ;
  if( node == NULL ) return 0 ;
  switch( node->sva_type ) {
  case SV_par_expression:
    return get_bitsize( node->node[1] ) ;
    break ;
  case SV_unary_expression:
    switch( node->node[0]->sva_type ) {
    case SV_unary_plus:
    case SV_unary_minus:
    case SV_unary_not:
    case SV_unary_tilda:
      return get_bitsize( node->node[1] ) ;
    case SV_unary_and:
    case SV_unary_nand:
    case SV_unary_or:
    case SV_unary_nor:
    case SV_unary_xor:
    case SV_unary_nxor:
    case SV_unary_xorn:
      return 1 ;
    default:
      return get_bitsize( node->node[1] ) ;
    }
    break ;
  case SV_binary_expression:
    s0 = get_bitsize( node->node[0] ) ;
    s1 = get_bitsize( node->node[2] ) ;
    if( s0 > s1 ) return s0 ;
    else return s1 ;
    break ;
  case SV_select_expression:
    s0 = get_bitsize( node->node[2] ) ;
    s1 = get_bitsize( node->node[4] ) ;  
    if( s0 > s1 ) return s0 ;
    else return s1 ;
    break ;
  // expr_primary 
  case SV_identifier:
    if( node->nm ) {
      switch( node->nm->type ) {
      case SV_port_name:
      case SV_reg_name:
      case SV_net_name:
        if( node->nm->bus_m == 0 && node->nm->bus_n == 0 ) {
	  return 1 ;	          
        }
        else {
	  if( node->nm->bus_m > node->nm->bus_n ) {
	    return node->nm->bus_m - node->nm->bus_n + 1 ;
	  }
	  else {
	    return node->nm->bus_n - node->nm->bus_m + 1 ;
	  } 
        }
	break ;
      default:
        return 1 ;
      }
    }
    else return 1 ;
    break ;
  case SV_identifier_singlesell:
    if( node->node[0]->nm ) {
      switch( node->node[0]->nm->type ) {
      case SV_port_name:
      case SV_reg_name:
      case SV_net_name:
	return 1 ;
      default:
	return 1 ;
      }
    }
    else return 1 ;
    break ;
  case SV_identifier_rangesell:
    if( node->node[0]->nm ) {
      switch( node->node[0]->nm->type ) {
      case SV_port_name:
      case SV_reg_name:
      case SV_net_name:
	s0 = get_constant( node->node[2] ) ;
	s1 = get_constant( node->node[4] ) ;
	return (s0 > s1) ? (s0 - s1 + 1 ) : ( s1 - s0 + 1 ) ;
      default:
	s0 = get_constant( node->node[2] ) ;
	s1 = get_constant( node->node[4] ) ;
	return (s0 > s1) ? (s0 - s1 + 1 ) : ( s1 - s0 + 1 ) ;      
      }
    }
    else return 1 ;
    break ;
  case SV_expression:
  default:
    s0 = 1 ;
    for ( i = 0 ; i < node->num_node ; i++ ) {
      s1 = get_bitsize( node->node[i] ) ;
      if( s1 > s0 ) s0 = s1 ;
    }
    return s0 ;
    break ;
  }
}

static void  internal_net_decl_out() {
  systemverilog_node *tmp ;
  systemverilog_node *s_tmp ;
  systemverilog_node *plane_node ;
  int bit_size ;
  
  kill_line_adjust = 1 ;
  fprintf( out, "\n" ) ;
  tmp = exp_clock_node ;
  while( tmp ) {
    if( tmp->clk_negedge ) {
      fprintf( out, "  wire %s%d = !(", ARV_WIRE, tmp->exp_id ) ;
    }
    else {
      fprintf( out, "  wire %s%d = ", ARV_WIRE, tmp->exp_id ) ;
    }
    rcv_node_out( tmp ) ;
    
    if( tmp->clk_negedge ) fprintf( out, ") ;\n" ) ;
    else fprintf( out, " ;\n" ) ;
    tmp = tmp->exp_list ;
  }
  
  // enable for initial check
  error_enable_node = new_wire_node() ;
  fprintf( out, "  assign " ) ;
  node_out( error_enable_node ) ;
  fprintf( out, " = 1'b1 ;\n"  ) ;
  error_enable_node = node_sync( error_enable_node ) ;
  
  tmp = exp_node ;
  while( tmp ) {
    bit_size = get_bitsize( tmp ) ;
    if( sync_input ) {
      if( tmp->sync_input_node ) s_tmp = tmp->sync_input_node ;
      else s_tmp = tmp->sync_input_node = gen_sync_input( tmp ) ;
    }
    else s_tmp = NULL ;
    if( sync_expression && !tmp->no_sync) {
      systemverilog_node *node = plane_node = new_wire_node() ;
      fprintf( out, "  assign " ) ;
      node_out( node ) ;
      if( tmp->clk_negedge ) {
	fprintf( out, " = !("  ) ;
      }
      else {
	fprintf( out, " = " ) ;
      }
      if( s_tmp ) rcv_node_out( s_tmp ) ;
      else rcv_node_out( tmp ) ;
    
      if( tmp->clk_negedge ) fprintf( out, ") ;\n" ) ;
      else fprintf( out, " ;\n" ) ;
      
      fprintf( out, "  wire %s%d ; \n", ARV_WIRE, tmp->exp_id ) ;
      fprintf( out,  "  ARV_DFF_ES #(%s) sync_dff%d ( ", ARV_SYNC_FF_NUM, label_num++ ) ;
      connect_port ( "Clk", tmp->clock_node, 1 ) ;
      fprintf( 
        out, ".RN(%s), .E( (~%s) && %s), ", ARV_RESET_, ARV_CLEAR, ARV_ENABLE 
      ) ;
      connect_port( "D", node , 1) ;
      connect_port( "Q", tmp, 0 ) ;
      fprintf( out, " ) ;\n" ) ;
      number_of_ff++ ;
    }
    else {
      if( tmp->clk_negedge ) {
        fprintf( out, "  wire %s%d = !(", ARV_WIRE, tmp->exp_id ) ;
      }
      else {
	fprintf( out, "  wire %s%d = ", ARV_WIRE, tmp->exp_id ) ;
      }
      if( s_tmp ) rcv_node_out( s_tmp ) ;
      else rcv_node_out( tmp ) ;
      if( tmp->clk_negedge ) fprintf( out, ") ;\n" ) ;
      else fprintf( out, " ;\n" ) ;
      
      plane_node = tmp ;
    }
    
    if( tmp->sysfunc_block ) {
      systemverilog_node *fc = tmp->sysfunc_block ;
      fprintf( out, "  wire %s%d ;\n", ARV_WIRE, fc->rose_id ) ;
      fprintf( out, "  wire %s%d ;\n", ARV_WIRE, fc->fell_id ) ;
      fprintf( out, "  wire %s%d ;\n", ARV_WIRE, fc->past_id ) ;
      fprintf( out, "  wire %s%d ;\n", ARV_WIRE, fc->stable_id ) ;
      fprintf( out, "  wire %s%d ;\n", ARV_WIRE, fc->sampled_id ) ;
      fprintf( 
	out, "  %s %s%d (\n", ARV_SYSFUNK_BLK, ARV_SF_INST, tmp->exp_id
	) ;
      fprintf(
	out, ARV_SYSFNK_ARG, 
	fc->clock_node->exp_id, plane_node->exp_id,
	fc->rose_id, fc->fell_id, fc->stable_id, fc->past_id, fc->sampled_id
	) ;
      fprintf( out, "\n  ) ;\n" ) ;
    }
    if( tmp->sysfunc_past_block) {
      systemverilog_node *fc = tmp->sysfunc_past_block ;
      while( fc ) {
        if( bit_size == 1 ) {
	  fprintf( out, "  wire %s%d ;\n", ARV_WIRE, fc->past_id ) ;
	  fprintf( 
	    out, "  %s %s%d #(%d) (\n", ARV_SYSFUNK_PAST_BLK, ARV_SF_INST, plane_node->exp_id, fc->past_num
	    ) ;
	  fprintf(
	    out, ARV_SYSFNK_PAST_ARG, 
	    fc->clock_node->exp_id, plane_node->exp_id,
	    fc->past_id
	    ) ;
	  fprintf( out, "\n  ) ;\n" ) ;   
	}
	else {
	  int base_id, i ;
	  base_id = label_num ;
	  if( fc->past_num > 1 ) {
	    for( i = 0 ; i < fc->past_num ; i++ ) {
	      fprintf( 
		out, "  reg [%d:0] %s%d ;\n", bit_size-1, ARV_WIRE, label_num++
		) ;	     
	    }	  
	    fprintf(
	      out, 
	      "  always @(posedge %s%d ) begin\n", 
	      ARV_WIRE,fc->clock_node->exp_id
	      ) ;
	    for( i = 0 ; i < fc->past_num ; i++ ) {
	      if( i == 0 ) {
	        fprintf(
		  out, "    %s%d <= %s%d ;\n", 
		  ARV_WIRE, base_id,  ARV_WIRE, plane_node->exp_id
		  ) ;
	      }
	      else {
	        fprintf(
		  out, "    %s%d <= %s%d ;\n", 
		  ARV_WIRE, base_id+i,  ARV_WIRE, base_id+i-1 
		  ) ;
              }
	    }
	    fprintf( out, "  end\n" ) ;
	    fprintf( 
	      out, "  wire [%d:0] %s%d = %s%d;\n", 
	      bit_size-1, ARV_WIRE, fc->past_id, 
	      ARV_WIRE, base_id + fc->past_num - 1
	      ) ; 
	  }
	  else {
	    fprintf( 
	      out, "  reg [%d:0] %s%d ;\n", bit_size-1, ARV_WIRE, fc->past_id
	      ) ;
	    fprintf(
	      out, 
	      "  always @(posedge %s%d ) begin\n", 
	      ARV_WIRE,fc->clock_node->exp_id
	      ) ;
	    fprintf(
	      out, "    %s%d <= %s%d ;\n", 
	      ARV_WIRE, fc->past_id,  ARV_WIRE, plane_node->exp_id
	      ) ;
	    fprintf( out, "  end\n" ) ;
	  }
	}
	fc = fc->sysfunc_past_block ;
      }
    }
    tmp = tmp->exp_list ;
  }
  tmp = onehot_node ;
  while( tmp ) {
    gen_onehot( tmp ) ;
    tmp = tmp->onehot_list ;
  }
  internal_net_decl_done = 1 ;
  kill_line_adjust = 0 ;
}

static int assertion_code_out( systemverilog_node *node ) {
  switch( node->sva_type) {
  case SV_concurrent_assertion:
  {
    if( !internal_net_decl_done ) {
      internal_net_decl_out() ;
    }
    if( node->node[0] ) {
      cur_name = node->node[0]->node[0]->name ;
      last_lin = node->node[0]->node[0]->debug_linenum ;
      // fprintf( out, "/* concurrent assertion %s: */", cur_name ) ;
    }
    else {
      cur_name = calloc( 1, strlen( ARV_INST_TMP ) + 10 ) ;
      sprintf( cur_name, ARV_INST_TMP, label_num++ ) ;
      last_lin = node->debug_linenum ;
    }
    assertion_code_out( node->node[1] ) ;
    return 1 ;
  }
  break ;
  case SV_sequence_dcl:
  {
    if( !internal_net_decl_done ) {
      internal_net_decl_out() ;
    }
    fprintf( 
      out, "\n  /* sequence_dcl %s @ %d */\n", 
      node->node[1]->name, node->node[1]->debug_linenum
      ) ;
    return 1 ;
  }
  break ;
  case SV_property_dcl:
  {
    if( !internal_net_decl_done ) {
      internal_net_decl_out() ;
    }
    fprintf( 
      out, "\n  /* property_dcl %s @ %d */\n", 
      node->node[1]->name, node->node[1]->debug_linenum
      ) ;  
    return 1 ;
  }
  break ;
  case SV_assert_property:
  {
    if( !internal_net_decl_done ) {
      internal_net_decl_out() ;
    }
    total_number_of_ff += number_of_ff ;
    total_number_of_and += number_of_and ;
    total_number_of_or += number_of_or ;
    total_number_of_not += number_of_not ;
    number_of_ff = 0 ;
    number_of_and = 0 ;
    number_of_or = 0 ;
    number_of_not = 0 ;
    fprintf( 
      out, "\n  /* assert_property %s.%s @ %d */\n", current_module->node[2]->name, cur_name, last_lin 
      ) ;
    cur_tm = ALLOC_TM_NODE ;
    error_check = 0 ;
    time_analysis( node->assertion_node ) ;
    clock_node = NULL ;
    disable_node = NULL ;
    enable_node = NULL ;   
    init_nodes() ;
    prev_attrib = SVN_none ;
    iovwp_depth = overwrap_depth ;
    if( overwrap_depth > 1 ) gen_var_block( node->assertion_node ) ;
    rtl_generation( node->assertion_node, 0 ) ;
    if( prop_error_node == NULL && match_node ) {
      prop_error_node = node_not( match_node ) ;
      prop_error_node = node_and( prop_error_node, error_enable_node ) ; 
      //if( disable_node ) {
      //  systemverilog_node *en = node_not( disable_node ) ;
      //  prop_error_node = node_and( en, prop_error_node ) ;
      //}
    }
    if( current_module->num_error_vector > 1 ) {
      fprintf( 
	out, "  assign %s[%d] = ", ARV_ERROR, assert_count 
        ) ;
    }
    else {
      fprintf( 
	out, "  assign %s = ", ARV_ERROR
        ) ;      
    }
    if( prop_error_node ) {
      node_out( prop_error_node ) ;
    }
    else {
      fprintf( out, " 1'b0 " ) ;    
    }
    fprintf( out, " ;\n" ) ;
    if( match_flag ) {
      if( current_module->num_error_vector > 1 ) {
        fprintf( 
  	  out, "  assign %s[%d] = ", ARV_MATCH, assert_count 
        ) ;
      }
      else {
       fprintf( 
  	  out, "  assign %s = ", ARV_MATCH
        ) ;     
      }
      node_out( match_node ) ;
      fprintf( out, " ;\n" ) ;
    }      
    if( overwrap_flag ) {
      if( overwrap_node == NULL ) {
        if( (current_module->num_error_vector + current_module->num_cover_vector) > 1 ) {
 	  fprintf( 
	    out, "  assign %s[%d] = 1'b0 ; \n", ARV_OVERWRAP, assert_count 
          ) ;
        }
        else {
      	  fprintf( 
	    out, "  assign %s = 1'b0 ; \n", ARV_OVERWRAP
          ) ;
        }
      }
      else {
        if( (current_module->num_error_vector + current_module->num_cover_vector) > 1 ) {
  	  fprintf( 
	    out, "  assign %s[%d] = ", ARV_OVERWRAP, assert_count 
          ) ;
	}
	else {
  	  fprintf( 
	    out, "  assign %s = ", ARV_OVERWRAP 
          ) ;
	}
	node_out( overwrap_node ) ;
	fprintf( out, " ;\n" ) ;
      }
    }
    assert_count++ ;
   fprintf( 
     stderr, "Assert Property: %s.%s line: %d\n", current_module->node[2]->name, cur_name, last_lin 
    ) ;   
    fprintf( stderr, "  number of FF  : %d \n", number_of_ff ) ;
    fprintf( stderr, "  number of AND : %d \n", number_of_and ) ;
    fprintf( stderr, "  number of OR  : %d \n", number_of_or ) ;
    fprintf( stderr, "  number of NOT : %d \n", number_of_not ) ;
    total_number_of_ff += number_of_ff ;
    total_number_of_and += number_of_and ;
    total_number_of_or += number_of_or ;
    total_number_of_not += number_of_not ;
    number_of_ff = 0 ;
    number_of_and = 0 ;
    number_of_or = 0 ;
    number_of_not = 0 ;
      return 1 ;
  }
  break ;
  case SV_cover_property:
  {
    if( !internal_net_decl_done ) {
      internal_net_decl_out() ;
    }
    total_number_of_ff += number_of_ff ;
    total_number_of_and += number_of_and ;
    total_number_of_or += number_of_or ;
    total_number_of_not += number_of_not ;
    number_of_ff = 0 ;
    number_of_and = 0 ;
    number_of_or = 0 ;
    number_of_not = 0 ;
    fprintf(
      out, "\n  /* cover_property %s.%s @ %d */\n", current_module->node[2]->name, cur_name, last_lin 
    ) ;      
    cur_tm = ALLOC_TM_NODE ;
    error_check = 0 ;
    time_analysis( node->assertion_node ) ;
    clock_node = NULL ;
    disable_node = NULL ;
    enable_node = NULL ;   
    init_nodes() ;
    prev_attrib = SVN_none ;
    iovwp_depth = overwrap_depth ;
    if( overwrap_depth > 1 ) gen_var_block( node->assertion_node ) ;
    rtl_generation( node->assertion_node, 0 ) ;
    // generate cover and assign to the vector
    // generate overwap if flag set
    if( match_node ) {
      if( current_module->num_cover_vector > 1 ) {
        fprintf( 
  	  out, "  assign %s[%d] = ", ARV_COVER, cover_count 
        ) ;
      }
      else {
       fprintf( 
  	  out, "  assign %s = ", ARV_COVER 
        ) ;
      }
      node_out( match_node ) ;
      fprintf( out, " ;\n" ) ;
    }
    if( overwrap_flag ) {
      if( (current_module->num_error_vector + current_module->num_cover_vector) > 1 ) {
        fprintf( 
	out, "  assign %s[%d] = ", ARV_OVERWRAP, assert_count + cover_count
        ) ;
      }
      else {
       fprintf( 
	out, "  assign %s = ", ARV_OVERWRAP
        ) ;     
      }
      node_out( overwrap_node ) ;
      fprintf( out, " ;\n" ) ;
    }     
    cover_count++ ;
   fprintf( 
     stderr, "Cover Property: %s.%s line: %d\n", current_module->node[2]->name, cur_name, last_lin 
    ) ;   
    fprintf( stderr, "  number of FF  : %d \n", number_of_ff ) ;
    fprintf( stderr, "  number of AND : %d \n", number_of_and ) ;
    fprintf( stderr, "  number of OR  : %d \n", number_of_or ) ;
    fprintf( stderr, "  number of NOT : %d \n", number_of_not ) ;
    total_number_of_ff += number_of_ff ;
    total_number_of_and += number_of_and ;
    total_number_of_or += number_of_or ;
    total_number_of_not += number_of_not ;
    number_of_ff = 0 ;
    number_of_and = 0 ;
    number_of_or = 0 ;
    number_of_not = 0 ;
    return 1 ;
  }
  break ;
  case SV_assume_property:
  {
    if( !internal_net_decl_done ) {
      internal_net_decl_out() ;
    }
    fprintf(
      out, "\n  /* assume_property %s @ %d */\n", cur_name, last_lin
      ) ;        
    return 1 ;
  }
  break ;
  case SV_port_list:
    if( current_module->num_error_vector || current_module->num_cover_vector )   
    {
      if( node->num_node == 0 ) {
	fprintf( out, "(  " ) ;
	additional_port_list_out(0) ;
	fprintf( out, ") \n" ) ;
      }
      else {
	rcv_node_out( node->node[0] ) ;
	rcv_node_out( node->node[1] ) ;
	additional_port_list_out(1) ;
	rcv_node_out( node->node[2] ) ;
      }
      return 1 ;
    }
    break ;
  case SV_port_dcl_list:
    if( current_module->num_error_vector || current_module->num_cover_vector )   
    {
      rcv_node_out( node->node[0] ) ;
      rcv_node_out( node->node[1] ) ;
      additional_port_dcl_list_out() ;
      rcv_node_out( node->node[2] ) ;
      port_decl_done = 1 ;  /* ANSI style doesn't need port dcl afterward */
    }
    break ;
  case SV_module_item_begin:
  {
    if( node->name ) {
      fprintf( out, " %s", node->name ) ;
    }
    if( !port_decl_done ) {
      additional_port_decl_out() ;
      parameter_decl_out() ;
      port_decl_done = 1 ;
    }
    return 1 ;
  }
  break ;
  case SV_module_top:
  {
    current_module = node ;
    return 0 ;
  }
  break ;
  }
  return 0 ;
  
}

static void rcv_node_out( systemverilog_node *node ) {
  int i ;
  if( node == NULL ) return ;
  if( node->sva_type && assertion_code_out( node) ) {
    flag = 0 ;
    if( node->next ) rcv_node_out( node->next ) ;
    return ;
  }
  level++ ;
    // if( level > 500) *p  = 0 ;
  
  if( node->name ) {
    /* last_lin = node->linenum ; */
    if( !kill_line_adjust ) {
      last_loc = node->location ;
      last_name = node->name ;
      while( cur_lin < node->linenum ) {
        if( flag ) {
          if( debug_line ) fprintf( out, "\t/* %d */", pline ) ;
          fprintf( out, "\n" ) ;
          pline = node->debug_linenum ;
        }
        cur_lin++ ;
        cur_loc = 0 ;
      }
      if( cur_loc < node->location ) {
        while( cur_loc < node->location ) {
          fprintf( out, " " ) ;
          cur_loc++ ;
        }
      }
      else {
         fprintf( out, " " ) ;
         cur_loc++ ; 
      }
    }
    else fprintf( out, " " ) ;
    // detect if this is local var access
    //   and modify the name for localized access
    if( node->exp_id && use_exp_id_node) {
      node_out( node ) ;
    }
    else if( node->nm && node->nm->type == SV_localvar_name ) {
      fprintf( out, "%s_%d", node->nm->name, node->nm->var_index ) ;
      cur_loc += strlen(node->name) + 3 ;    
    }
    else {
      fprintf( out, "%s", node->name ) ;
      cur_loc += strlen(node->name) ;
    }
    if( pline == 0 ) pline = node->debug_linenum ;
    flag = 1 ;
  }
  for ( i = 0 ; i < node->num_node ; i++ ) {
    rcv_node_out( node->node[i] ) ;
  }
  if( node->next ) {
    //fprintf( out, "->next\n" ) ;
    rcv_node_out( node->next ) ;
   }
 level -- ;
}

void codegen() {
  cur_lin = 0 ;
  cur_loc = 0 ;
  level = 0 ;
  
  rcv_node_parse( root_node ) ;
  fprintf( out, "%s", version_string ) ;
  rcv_node_out( root_node ) ;
  
  fprintf( stderr, "Estimated total gate usage: \n" ) ;
  fprintf( stderr, "  number of FF  : %d \n", total_number_of_ff ) ;
  fprintf( stderr, "  number of AND : %d \n", total_number_of_and ) ;
  fprintf( stderr, "  number of OR  : %d \n", total_number_of_or ) ;
  fprintf( stderr, "  number of NOT : %d \n", total_number_of_not ) ;
  
}
