/***************************************************************************
 *
 *  main.c: main function for SystemVerilog Assertion compler
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

#if defined(_MSC_VER)
#define popen _popen
#define pclose _pclose
#define PATH_SEP "\\"
#else
#define PATH_SEP "/"
#endif

extern unsigned int lex_line_num  ;
extern unsigned int debug_line_num  ;
extern unsigned int lex_location  ;

extern char *input_file_name  ;
extern char *last_text ;
extern int yydebug;

void codegen()  ;

systemverilog_node *root_node = NULL ;

int compile_pass ;
int error_flag = 0 ;
int error_count = 0 ;
int max_error = 0 ;
int match_flag = 0 ;
int overwrap_depth = 1 ;
int overwrap_flag = 0 ;
int sync_expression = 0 ;  // was 1
int sync_ff_num = 0 ;      // was 1
int sync_input = 1 ;       // was 0
int ise_flag = 1 ;
int debug_line = 0 ;
int internal_overwrap_flag = 0 ;
int internal_filter_flag = 1 ;

int arv_use_counter = ARV_USE_COUNTER ;
int arv_use_flat_rep = ARV_USE_FLAT_REP ;

extern int yydebug;
extern FILE *yyin;  /* for lex input */

char *out_fname = NULL ;
char *in_fname = NULL ;

char *version_string ;

FILE *out ;

void compile_pipe()  ;
void parse_init() ;

main ( int argc, char **argv ) {
  int i ;
  yydebug = 0 ;
  
  fprintf( stderr, "sva2rtl version: %s\n", ARV_VERSION ) ;
  fprintf( stderr, "  compiled date: %s %s\n", __DATE__, __TIME__ ) ;
  char *form = "// sva2rtl version: %s \n// compiled date: %s %s\n" ;
  version_string = calloc( sizeof(char), strlen(form)+50) ;
  sprintf( version_string, form, ARV_VERSION,  __DATE__, __TIME__ ) ;
  
  for( i = 1 ; i < argc ; i++ ) {
  
    if( argv[i][0] != '-' ) {
      if( out_fname != NULL ) {
        fprintf( stderr, "Usage: %s [switches] input [output]\n", "sva2rtl"  ) ;
        exit(1) ;
      }  
      else if( in_fname != NULL ) {
        out_fname = argv[i] ;
      }
      else {
        in_fname = argv[i] ;
      }
    }
    else {
      // handle options 
       switch( argv[i][1] ) {
         case 'v': 
           yydebug = 1 ;
           break ;
         case 'l':
	   debug_line = 1 ;
	   break ;
         case 'a':
	   sync_input = 0 ;
    	   break ;
          case 't': 
         {
           int dp ;
           if( argv[i][2] ) {
             dp = atoi( &argv[i][2] ) ;
           }
           else {
             i++ ;
             dp = atoi( argv[i] ) ;
           }
           if( dp == 0 ) {
	     sync_expression = 0 ;
           }
           else {
	     sync_expression = 1 ;
             sync_ff_num = dp ;
           }
         }
         break ;
        case 'd': 
         {
           int dp ;
           if( argv[i][2] ) {
             dp = atoi( &argv[i][2] ) ;
           }
           else {
             i++ ;
             dp = atoi( argv[i] ) ;
           }
           if( dp == 0 ) {
             fprintf( 
               stderr, 
               "Error argment: %s -d<depth> must be proper integer \n", argv[i]  
             ) ;
             exit(1) ;
           }
           if( dp > 8 ) {
             fprintf( 
               stderr, 
               "Error argment: %s -d<depth> must be less than 8.\n", argv[i]  
             ) ;
             exit(1) ;           
           }
           overwrap_depth = dp ;
         }
         break ;
         case 'i': 
	   internal_overwrap_flag = 1 ;
         break ;        
         case 'f': 
	   internal_filter_flag = 0 ;
         break ;    
         case 'p': 
         {
           int dp ;
           if( argv[i][2] ) {
             dp = atoi( &argv[i][2] ) ;
           }
           else {
             i++ ;
             dp = atoi( argv[i] ) ;
           }
           if( dp == 0 ) {
             fprintf( 
               stderr, 
               "Error argment: %s -p<pipe_length> must be proper integer \n", argv[i]  
             ) ;
             exit(1) ;
           }
           arv_use_counter = dp ;
         }
         break ;
         
         case 'r': 
         {
           int dp ;
           if( argv[i][2] ) {
             dp = atoi( &argv[i][2] ) ;
           }
           else {
             i++ ;
             dp = atoi( argv[i] ) ;
           }
           if( dp == 0 ) {
             fprintf( 
               stderr, 
               "Error argment: %s -r<flat_rep_length> must be proper integer \n", argv[i]  
             ) ;
             exit(1) ;
           }
           arv_use_flat_rep = dp ;
         }
         break ;
                  
         case 'o': 
	   overwrap_flag = 1 ;
         break ;
	 
         case 'm':
	   match_flag = 1 ;
	   break ;
         case 'n':
	   ise_flag = 0 ;
	   break ;      
       }
     }
  }
  if( in_fname == NULL ) {
    fprintf( stderr, "Usage: sva2rtl [switches] input [output]\n"   ) ;
    exit(1) ;
  }
  if( out_fname == NULL ) {
    char *p = in_fname;
    out_fname = (char *)calloc( strlen(p)+10, sizeof(char) ) ;
    strcpy( out_fname, p ) ;

    p = strrchr( out_fname, '.' );
    if( p != NULL ) *p = '\0' ;

    strcat( out_fname, ".arv" ) ;
    printf( "OUT_FILE: %s\n", out_fname ) ;
  }
  
  compile_pipe() ;
  
}


void compile_pipe() {
  char *command ;
  int len ;
  
 // need to set proper application home 
 char *homedir = (char *)getenv( "SVA2RTL_HOME" ) ;
  
  if( homedir == NULL ) {
    fprintf( 
      stderr, 
      "Environment Variable $%s is not set. Using current dir\n", "SVA2RTL_HOME" 
    ) ;
    homedir = "." ;
  }

  len = strlen(in_fname) + 256 + strlen( homedir ) ;

  command = (char *)calloc( len, sizeof(char) ) ;
  strcpy( command, homedir ) ;
  strcat( command, PATH_SEP ) ;
  strcat( command, "ivlpp" ) ;
  strcat( command, " -L " ) ;
  strcat( command, in_fname ) ;
  yyin = popen( command, "r" ) ;
  fprintf( stderr, "Pipe command:%s\n", command ) ;
  /* yyin = fopen( in_fname, "r") ; */
  if( !yyin ) {
    fprintf( stderr, "Error: Can't open pipe on \"%s\"\n", command ) ;
    exit(1);
  } 
  input_file_name = in_fname ;

#ifdef YYRESTART
       yyrestart( yyin ) ;  
       /* without calling this, # at the begining is not handled correctly. */
#endif
  compile_pass = 0 ;
  init_scope() ;

  fprintf( stderr, "Compile pass 0 starting..\n" ) ;

  yyparse() ;
  
  last_text = NULL ;
  pclose( yyin ) ;

 if( error_count == 0 ) {
  
    fprintf( stderr, "Compile pass 1 starting..\n" ) ;

    compile_pass = 1 ;
    parse_init() ;
    rewind_scope() ;
    lex_line_num = 0 ;
    debug_line_num = 0 ;

    yyin = popen( command, "r" ) ;
    
    if( !yyin ) {
      fprintf( stderr, "Error: Can't open pipe on \"%s\"\n", command ) ;
      exit(1);
    } 
    
    yyparse() ;
    pclose( yyin ) ;
  }
  last_text = NULL ;

  if( error_count == 0 ) {
    fprintf( stderr, "Compile pass 2 starting..\n" ) ;

    out = fopen( out_fname, "w" ) ;
    if( out == NULL ) {
      fprintf( 
        stderr, "%s : cannot open output file %s\n", "sva2rtl", out_fname
      );
      exit(1) ;
    }
    compile_pass = 2 ;
    lex_line_num = 0 ;
    debug_line_num = 0 ;

    rewind_scope() ;
    yyin = popen( command, "r" ) ;
    if( !yyin ) {
      fprintf( stderr, "Error: Can't open pipe on \"%s\"\n", command ) ;
      exit(1);
    } 
    yyparse() ;
    pclose( yyin ) ;
  }
  
 if( error_count == 0 ) {
     /* code generation here */
     codegen() ;
     fprintf( stderr, "%d compile errors\n", error_count ) ;  
  }

 if( error_count == 0 ) exit(0) ;
 else exit(1) ;
 
}
  
int yyerror( char *message ) 
{
  int last = 0 ;
  
  if( last_text == NULL ) {
    last_text = "UNKNOWN" ;
    last = 1 ;
  }
  
  fprintf(
    stderr, "File: \"%s\", line %d near %s : ", 
    input_file_name, debug_line_num, last_text
  );
    
  fprintf(
    stderr, "%s\n", 
    message
  );
  error_count++ ;
  
  error_flag = 1 ;
  
  if( max_error && error_count > max_error ) {
    exit(1) ;
  }
  if( last ) last_text = NULL ;
  
}

int yywarning( char *message ) 
{
  int last = 0 ;
  
  if( last_text == NULL ) {
    last_text = "UNKNOWN" ;
    last = 1 ;
  }

  fprintf(
    stderr, "File: \"%s\", line %d near %s : ", 
    input_file_name, lex_line_num, last_text
  );

  fprintf(
    stderr, "%s\n", 
    message
  );

  if( last ) last_text = NULL ;
  
}

void free_node( systemverilog_node *node ) {
  int i ;
  systemverilog_node *child ;
  for( i = 0 ; i < 20 ; i++ ) {
    child = node->node[i] ;
    if( child) free_node( child ) ;
  }
  child = node->next ;
  if( child ) free_node( child ) ;
  free(node) ;
}

void parse_init() {
 if( root_node ) {
    free_node( root_node ) ;
    root_node = NULL ;
  }
}
