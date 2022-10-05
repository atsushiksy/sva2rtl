/***************************************************************************
 *
 *  symtab.c: symbol table functions for the compiler parse tree
 *
 *  Author: Atsushi Kasuya
 *
 *   Copyright (C) 2011 Atsushi Kasuya 
 *
 ***************************************************************************/
#include <stdio.h>
#include "systemverilog_node.h"
#include "symtab.h"

 named_node *top_scope = NULL ;
 named_node *current_scope = NULL ;
 named_node *local_scope = NULL ;
 
 int scope_id = 0 ;
 int first_verilog_block ;

extern int compile_pass ;

void init_scope() {
  top_scope = ALLOC(named_node) ;
  top_scope->name = "" ;
  top_scope->type = SV_name_dummy ;
  top_scope->scope_id = scope_id++ ;
  current_scope = top_scope ;

  first_verilog_block = 1 ;
}


/* rewind the scope state */
void rewind_scope() {
  current_scope = top_scope ;
  scope_id = 1 ;
  first_verilog_block = 1 ;
}

void enter_scope( named_node *parent ) {
  named_node *tmp ;
  PASS1 {
    /* during pass 0, constructing scope tree structure */
    /* JD_name_dummy type is used to construct the scope tree */
    tmp = ALLOC(named_node) ;
    tmp->name = (char *)strdup("") ;
    tmp->type = SV_name_dummy ;
    if(parent) tmp->parent_scope = parent ;
    else tmp->parent_scope = current_scope ;  /* save current as parent */
    tmp->prev_scope = current_scope ;  /* this is where to exit */
    tmp->scope_id = scope_id++ ;
    current_scope = tmp ; /* new scope as current */
    
    /* link as parent's child_scope */
    tmp = current_scope->parent_scope->child_scope ;
    if( tmp ) {
      while( tmp->next_brother ) tmp = tmp->next_brother ;
      tmp->next_brother = current_scope ;
    }
    else current_scope->parent_scope->child_scope = current_scope ;
  }
  PASS2{
    if( parent ) tmp = parent->child_scope ;
    else tmp = current_scope->child_scope ;
    while( tmp ) {
      if( tmp->scope_id == scope_id ) break ;
      tmp = tmp->next_brother ;
    }
    if( tmp == NULL ) {
      fprintf( stderr, "Symbol Stack broken. Can't continue, exiting..\n" ) ;
      exit(1) ;
    }
    tmp->prev_scope = current_scope ;  /* this is where to exit */
    current_scope = tmp ;
    scope_id++ ;
  }
}

void exit_scope () {
  if( current_scope == NULL ) {
   fprintf( stderr, "Symbol Stack broken. Can't continue, exiting..\n" ) ;
   exit(1) ;
  }
  else current_scope = current_scope->prev_scope ;
}

void push_scope( named_node *parent, named_node *child ) {
  named_node *tmp ;
  PASS0_1 {
    if( child == NULL ) {
      child = ALLOC(named_node) ;
      child->name = (char *)strdup("") ;
      child->type = SV_name_dummy ;
    }
    child->parent_scope = parent ;
    child->scope_id = scope_id++ ;
    child->prev_scope = current_scope ; /* to pop scope */
    current_scope = child ; /* new scope as current */
    
    /* link as parent's child_scope */
    tmp = parent->child_scope ;
    if( tmp ) {
      while( tmp->next_brother ) tmp = tmp->next_brother ;
      tmp->next_brother = current_scope ;
    }
    else current_scope->parent_scope->child_scope = current_scope ;
  }
}

void pop_scope() {
  PASS0_1 {
    if( current_scope->prev_scope ) current_scope = current_scope->prev_scope ;
    else {
     fprintf( stderr, "Symbol Stack broken. Can't continue, exiting..\n" ) ;
     exit(1) ;
   }
  }
}

void addname_to_scope( named_node *scope, named_node *new )
{
  named_node *tmp ;
  
  /* append the new name at the end of next_in_scope link */
  tmp = scope ;
  while( tmp->next_in_scope ) tmp = tmp->next_in_scope ;
  tmp->next_in_scope = new ;

}

void addname( named_node *new )
{
  named_node *tmp ;
  
  if( current_scope == NULL ) {
   /*  ERROR_VARIABLE_SCOPE_STRUCTURE_IS_BROKEN ; */
    fprintf( stderr, "Error: varible scope structure is broken!\n" ) ;
    exit(1) ;
  }
  else {
    if( findname_in_scope(current_scope, new->name)) {
      fprintf( stderr, "Error: Name %s redefined!\n", new->name  ) ;
      exit(1) ;
    }
    /* append the new name at the end of next_in_scope link */
    tmp = current_scope ;
    while( tmp->next_in_scope ) tmp = tmp->next_in_scope ;
    tmp->next_in_scope = new ;
  }

}

named_node *findname_in_scope( named_node *scope, char *name ) {
  named_node *tmp ;
  
  tmp = scope ;
  while( tmp ) {
    /* search the name within the next_in_scope link */
    if( tmp->name && !strcmp(tmp->name, name ) ) return tmp ;
    tmp = tmp->next_in_scope ;
  }
  return NULL ;
}

named_node *findname( char *name ) {
  named_node *scope, *tmp ;
  
  scope = current_scope ;
  while( scope ) {
    tmp = scope ;
    while( tmp ) {
      if( tmp->name && !strcmp(tmp->name, name ) ) return tmp ;
      tmp = tmp->next_in_scope ;
    }
    /*
    if( scope->parent_scope && scope->prev_scope != scope->parent_scope &&
        scope->parent_scope->type == JD_class_name  )
    {
      tmp = findname_in_class( scope->parent_scope, name ) ;
      if( tmp ) return tmp ;
    }
    */
    scope = scope->prev_scope ;
  }
  return NULL ;
}

named_node *new_node(
  char *name, SV_name_type type, int add_to_scope 
) 
{
  named_node *new_node = ALLOC(named_node) ;
  new_node->name = name ;
  new_node->type = type ;
  if( add_to_scope ) {
    addname( new_node ) ;
  }
  return new_node ;
}
