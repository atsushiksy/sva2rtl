%{
/**************************************************************************
 *
 *  System Verilog Lexical Analizer prep file
 *
 *  Author: Atsushi Kasuya
 *
 *
**************************************************************************/
/* 
   
   Copyright (C) 2011 Atsushi Kasuya

   
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#include "systemverilog_node.h"
#include "symtab.h"

#include "y_tab.h"

extern int compile_pass ;
extern int parsing_assertion ;

static void scan_v_decimal( char *number, systemverilog_node *node ) ;
static void scan_v_octal( char *number, systemverilog_node *node ) ;
static void scan_v_hex( char *number, systemverilog_node *node ) ;
static void scan_v_binary( char *number, systemverilog_node *node ) ;

static lex_error() ;

typedef struct s_keyword_entry {
  char *pattern ;
  int  token ;
} keyword_entry ;

/* automaticall generated keyword table */
#include "SystemVerilog_keyword_table.h"

#define INITIAL_LINE_SIZE 256 

unsigned int lex_line_num = 0 ;
unsigned int debug_line_num = 0 ;
char *input_file_name ;
int  in_file_used = 0 ;
unsigned int lex_location = 0 ;

static int flag = 0 ;

char *last_text = NULL ;

static unsigned search_keyword(char *pattern) ;

static void set_last( char *type, char *token ) ;

static char *last_string = NULL ;

%}

white		[ \t\f]+
newline		\n
identifier	[a-zA-Z_][a-zA-Z0-9_$]*
sys_identifier	\$[a-zA-Z_$][a-zA-Z0-9_$]*
numeric		[0-9]
decimal		[0-9_]
integerval	[1-9][0-9]*
hex		[a-fA-F0-9xXzZ_]
octal		[0-7_xXzZ]
binary		[01_xXzZ]

%%

\`line.*$  {
  /* preprocessor comment line must have the following format:
    `line  <line_num>  "<file_name>" <level>
  */
  
  char *p, *q, *r, *lnum ;
  
  p = q = (char *)strdup( yytext ) ;
  q+= 5 ;
  while( isspace(*q) ) q++ ;
  r = q ;
  while( isdigit(*r) ) r++ ;
  if( q != r ) {
    *r = '\0' ;
    lnum = q ;
    q = r+1 ;
    while( isspace(*q) )q++ ;
    if( *q == '"' ) {
      q++ ;
      r = q ;
      while( *r != '"' ) r++ ;
      *r = '\0' ;
      if( strlen(q) ) {
        debug_line_num = atoi(lnum)-1 ; 
        /* lex_debug_line_num = atoi(lnum)-1 ; */
        /* Don't release if we share it for debug info */
        /* if( input_file_name && !in_file_used ) free( input_file_name ) ;
        */
        input_file_name = (char *)strdup(q) ;
        // add_file_to_list(q) ; /* func in parse_tree.c */
        in_file_used = 0 ;
      }
      else if( input_file_name == NULL ) input_file_name = "???" ;
    }
  }
  free( p ) ;
  lex_location = 0 ;
}
\`timescale.*$ {
  /* skip timescale declaration */
  debug_line_num++ ;
  lex_location = 0 ;
}
{white}   {
    lex_location += strlen(yytext) ;         
  }
{newline}  {
      if( flag ) 
        lex_line_num++ ;
      debug_line_num++ ;
      lex_location = 0 ;
      /* fprintf( stderr, "Line:%d\n", lex_line_num ) ; */
      flag = 0 ;
  }
<<EOF>>  { lex_line_num-- ;  debug_line_num-- ; return 0 ; }
\"[^"\n]* {    
    /* begining of string */
    int c ;
    
    c = input() ;
    if( c == '\n' ) {
      lex_line_num++ ;
      debug_line_num++ ;
      if( yytext[yyleng-1] == '\\' ) {
        if( last_string ) {
          char *p ;
          int len ;
          p = last_string ;
          len = strlen(p) ;
          last_string = (char *)calloc(len+yyleng+1, sizeof(char) ) ;
          strcat( last_string, p ) ;
          yytext[yyleng-1] = '\0' ;
          strcat( last_string, yytext ) ;
          free(p) ;
        }
        else {
          last_string = (char *)calloc(yyleng+1, sizeof(char) ) ;
          yytext[yyleng-1] = '\0' ;
          strcat( last_string, yytext ) ;
        }
        /* yymore() ;  * set flag to append input to the end of yytext */
        unput( '\"' ) ;  /* next search goes to string again */
        /* CONTINUE */
      }
      else {
        lex_location = 0 ;
        fprintf(
          stderr,
          "lex scan error: CR found in a string at %d in %s\n",
          debug_line_num, input_file_name
        ) ;
        /*
        c = input() ;
        while( c != '\"' ) {
          if( c == '\n' ) {
            lex_line_num++ ;
            debug_line_num++ ;
          }
          c = input() ;
        }
        unput(c) ;
        */
        flag = 1 ;
        return String_literal ; 
      }
    }
    else {
      /* detect " */
      if( yytext[yyleng-1] == '\\' ) {
        /* got excaped ", so need to continue scanning string */
        /* avoid yymore due to a flex problem?? */
        /* yymore() ;  * set flag to append input to the end of yytext */
        if( last_string ) {
          char *p ;
          int len ;
          p = last_string ;
          len = strlen(p) ;
          last_string = (char *)calloc(len+yyleng+1, sizeof(char) ) ;
          strcat( last_string, p ) ;
          yytext[yyleng] = '\0' ;
          strcat( last_string, yytext ) ;
          free(p) ;
        }
        else {
          last_string = (char *)calloc(yyleng+1, sizeof(char) ) ;
          yytext[yyleng] = '\0' ;
          strcat( last_string, yytext ) ;
        }
        unput( c ) ;  /* unput ", so next search goes to string again */
        /* CONTINUE */
      }
      else {
        if( last_string ) {
          char *p ;
          int len ;
          char t ;
          t = yytext[yyleng-1] ; /* this is " */
          yytext[yyleng-1] = '\0' ;
          len = strlen(last_string) ;
          p = (char *)calloc(len+yyleng+3,sizeof(char)) ;
          strcat(p, last_string) ;
          strcat(p, yytext) ;
          len = strlen(p) ;
          p[len] = t ;
          p[len+1] = c ;
          yylval.sv_node = ALLOC_SV_NODE ;
          yylval.sv_node->name = p ;
          yylval.sv_node->location = lex_location ;
          lex_location += strlen(yytext) ;
          free(last_string) ;
          last_string = NULL ;
        }
        else {
          char *p ;
          int len ;
          char t ;
          t = yytext[yyleng-1] ; /* this is " */
          yytext[yyleng-1] = '\0' ;
          p = (char *)calloc(yyleng+3,sizeof(char)) ;
          strcat(p, yytext) ;
          len = strlen(p) ;
          p[len] = t ;
          p[len+1] = c ;
          yylval.sv_node = ALLOC_SV_NODE ;
          yylval.sv_node->name = p ;
        }
        yylval.sv_node->linenum = lex_line_num ;
        yylval.sv_node->debug_linenum = debug_line_num ;
        yylval.sv_node->filename = input_file_name ;
        flag = 1 ;
        return String_literal ;
      }
    }
  }
{sys_identifier} {
   yylval.sv_node = ALLOC_SV_NODE ;
   yylval.sv_node->name = 
      (char *)calloc( strlen(yytext)+100, sizeof(char) ) ;
   strcat( yylval.sv_node->name, yytext ) ;
   yylval.sv_node->linenum = lex_line_num ;
   yylval.sv_node->debug_linenum = debug_line_num ;
   yylval.sv_node->filename = input_file_name ;
   yylval.sv_node->location = lex_location ;
   lex_location += strlen(yytext) ;
   set_last( "identifier", yytext ) ;
   /*
   if( !strcmp( "$root", yytext) ) {
     yylval.sv_node->type = DollerRoot ; 
     return DollerRoot ;
   }
   if( !strcmp( "$rose", yytext) ) {
     yylval.sv_node->type = DollerRose ; 
     return DollerRose ;
   }
   if( !strcmp( "$fell", yytext) ) {
     yylval.sv_node->type = DollerFell ; 
     return DollerFell ;
   }
   if( !strcmp( "$onehot", yytext) ) {
     yylval.sv_node->type = DollerOnehot ; 
     return DollerOnehot ;
   }
   if( !strcmp( "$onehot0", yytext) ) {
     yylval.sv_node->type = DollerOnehot0 ; 
     return DollerOnehot0 ;
   }
   if( !strcmp( "$stable", yytext) ) {
     yylval.sv_node->type = DollerStablel ; 
     return DollerStablel ;
   }
   if( !strcmp( "$past", yytext) ) {
     yylval.sv_node->type = DollerPast ; 
     return DollerPast ;
   }
   if( !strcmp( "$sampled", yytext) ) {
     yylval.sv_node->type = DollerSampled ; 
     return DollerSampled ;
   }
   if( !strcmp( "$countones", yytext) ) {
     yylval.sv_node->type = DollerCountones ; 
     return DollerCountones ;
   }
   if( !strcmp( "$isunknown", yytext) ) {
     yylval.sv_node->type = DollerCountones ; 
     return DollerIsunknown ;
   }
   */
   yylval.sv_node->type = Sys_identifier ; 
   flag = 1 ;
   return Sys_identifier ;
}

"<<<="  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = ULSHIFT_EQ ;
  return ULSHIFT_EQ ;
}
"::"  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = DBL_CLN ;
  return DBL_CLN ;
}
"++"  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = D_PLUS ;
  return D_PLUS ;
}
"&="  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = AND_EQ ;
  return AND_EQ ;
}
"<<"  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = LSHIFT ;
  return LSHIFT ;
}
"!?="  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = Q_NEQ ;
  return Q_NEQ ;
}
">>>="  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = URSHIFT_EQ ;
  return URSHIFT_EQ ;
}
"|="  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = OR_EQ ;
  return OR_EQ ;
}
":/"  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = C_DIV ;
  return C_DIV ;
}
">="  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = GE ;
  return GE ;
}
"=="  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = EQEQ ;
  return EQEQ ;
}
"-:"  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = MNS_CLN ;
  return MNS_CLN ;
}
"^~"  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = EORTILDA ;
  return EORTILDA ;
}
"<="  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = LE ;
  return LE ;
}
"||"  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = LOR ;
  return LOR ;
}
"&&&"  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = TRPL_AND ;
  return TRPL_AND ;
}
"!=="  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = NEQEQ ;
  return NEQEQ ;
}
"<<="  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = LSHIFT_EQ ;
  return LSHIFT_EQ ;
}
"/="  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = SLSH_EQ ;
  return SLSH_EQ ;
}
"**"  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = DOUBLE_STAR ;
  return DOUBLE_STAR ;
}
"+:"  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = PLS_CLN ;
  return PLS_CLN ;
}
"->"  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = ARROW ;
  return ARROW ;
}
":="  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = C_EQ ;
  return C_EQ ;
}
"~&"  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = TILDAAND ;
  return TILDAAND ;
}
">>="  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = RSHIFT_EQ ;
  return RSHIFT_EQ ;
}
"=?="  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = Q_EQ ;
  return Q_EQ ;
}
"+="  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = PLUS_EQ ;
  return PLUS_EQ ;
}
"*)"  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = STAR_RPAR ;
  return STAR_RPAR ;
}
"--"  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = D_MINUS ;
  return D_MINUS ;
}
"*>"  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = STAR_GT ;
  return STAR_GT ;
}
"|->"  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = BAR_ARROW ;
  return BAR_ARROW ;
}
"##"  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = DBL_SHARP ;
  return DBL_SHARP ;
}
"*="  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = STAR_EQ ;
  return STAR_EQ ;
}
"|=>"  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = BAR_FATARROW ;
  return BAR_FATARROW ;
}
"!="  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = NE ;
  return NE ;
}
"==="  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = EQEQEQ ;
  return EQEQEQ ;
}
"-="  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = MINUS_EQ ;
  return MINUS_EQ ;
}
"<<<"  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = LTLTLT ;
  return LTLTLT ;
}
"~^"  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = TILDAEOR ;
  return TILDAEOR ;
}
"~|"  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = TILDAOR ;
  return TILDAOR ;
}
"%="  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = MOD_EQ ;
  return MOD_EQ ;
}
"&&"  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = LAND ;
  return LAND ;
}
">>"  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = RSHIFT ;
  return RSHIFT ;
}
"=>"  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = EQ_GT ;
  return EQ_GT ;
}
">>>"  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = URSHIFT ;
  return URSHIFT ;
}
"^="  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = EOR_EQ ;
  return EOR_EQ ;
}
"(*"  {
  yylval.sv_node = ALLOC_SV_NODE ;
  yylval.sv_node->linenum = lex_line_num ;
  yylval.sv_node->filename = input_file_name ;
  yylval.sv_node->name = 
    (char *)calloc( strlen(yytext)+10, sizeof(char) ) ;
  strcat( yylval.sv_node->name, yytext ) ;
  yylval.sv_node->type = LPAR_STAR ;
  return LPAR_STAR ;
}
{identifier} {
    int token ;
    /*
    if( parsing_assertion && !strcmp( "and", yytext ) ) {
      yylval.sv_node = ALLOC_SV_NODE ;
      yylval.sv_node->location = lex_location ;
      lex_location += strlen(yytext) ;
      yylval.sv_node->name = 
        (char *)calloc( strlen(yytext)+100, sizeof(char) ) ;
      strcat( yylval.sv_node->name, yytext ) ;
      yylval.sv_node->linenum = lex_line_num ;
      yylval.sv_node->debug_linenum = debug_line_num ;
      yylval.sv_node->filename = input_file_name ;
      set_last( "identifier", yytext ) ;
      flag = 1 ; 
      return SV_Ass_And ;   
    }
    if( parsing_assertion && !strcmp( "or", yytext ) ) {
      yylval.sv_node = ALLOC_SV_NODE ;
      yylval.sv_node->location = lex_location ;
      lex_location += strlen(yytext) ;
      yylval.sv_node->name = 
        (char *)calloc( strlen(yytext)+100, sizeof(char) ) ;
      strcat( yylval.sv_node->name, yytext ) ;
      yylval.sv_node->linenum = lex_line_num ;
      yylval.sv_node->debug_linenum = debug_line_num ;
      yylval.sv_node->filename = input_file_name ;
      set_last( "identifier", yytext ) ;
      flag = 1 ; 
      return SV_Ass_Or ;   
    }    
    */
    if( token = search_keyword( yytext ) ) {
      yylval.sv_node = ALLOC_SV_NODE ;
      yylval.sv_node->location = lex_location ;
      lex_location += strlen(yytext) ;
      yylval.sv_node->name = 
        (char *)calloc( strlen(yytext)+100, sizeof(char) ) ;
      strcat( yylval.sv_node->name, yytext ) ;
      yylval.sv_node->linenum = lex_line_num ;
      yylval.sv_node->debug_linenum = debug_line_num ;
      yylval.sv_node->filename = input_file_name ;
      set_last( "identifier", yytext ) ;
      flag = 1 ;
      return token ;
    }
    else {
       int c ;
       /* yylval.string_value.name = (char *)strdup(yytext) ; */
       yylval.sv_node = ALLOC_SV_NODE ; 
       yylval.sv_node->location = lex_location ;
       lex_location += strlen(yytext) ;
       yylval.sv_node->name = 
         (char *)calloc( strlen(yytext)+100, sizeof(char) ) ;
       strcat( yylval.sv_node->name, yytext ) ;
       yylval.sv_node->linenum = lex_line_num ;
       yylval.sv_node->debug_linenum = debug_line_num ;
       yylval.sv_node->filename = input_file_name ;
       yylval.sv_node->sva_type = SV_identifier ;
       set_last( "identifier", yytext ) ;
       /*
       if( !strcmp( "scan_distribution", yytext ) ) {
         lex_catch_it() ;
       }
       */
       flag = 1 ;
       PASS1_2 {
         named_node *nm = findname( yytext ) ;
         if( nm ) {
           if( nm->type == SV_property_name ) return Property_Name ;
         }
       }
       return Identifier ;
    } 
}
0 {
    yylval.sv_node = ALLOC_SV_NODE ;
    yylval.sv_node->name = (char *)strdup(yytext) ;
    yylval.sv_node->linenum = lex_line_num ;
    yylval.sv_node->debug_linenum = debug_line_num ;
    yylval.sv_node->filename = input_file_name ;
    yylval.sv_node->location = lex_location ;
    lex_location += strlen(yytext) ;
    yylval.sv_node->type = Decimal_number ; 
    yylval.sv_node->const_flag = 1 ; 
    yylval.sv_node->const_value = 0 ; 
    set_last( "decimal number", yytext ) ;
    flag = 1 ;
    return Decimal_number ;
  }
{integerval} {
    yylval.sv_node = ALLOC_SV_NODE ;
    yylval.sv_node->name = (char *)strdup(yytext) ;
    yylval.sv_node->linenum = lex_line_num ;
    yylval.sv_node->debug_linenum = debug_line_num ;
    yylval.sv_node->filename = input_file_name ;
    yylval.sv_node->location = lex_location ;
    lex_location += strlen(yytext) ;
    yylval.sv_node->type = Decimal_number ; 
    yylval.sv_node->const_flag = 1 ; 
    yylval.sv_node->const_value = atoi(yytext) ; 
    set_last( "integer number", yytext ) ;
    flag = 1 ;
    return Unsigned_number ;
  }
{integerval}\'[sS]?[dD]{decimal}+   {
    yylval.sv_node = ALLOC_SV_NODE ;
    yylval.sv_node->name = (char *)strdup(yytext) ;
    yylval.sv_node->linenum = lex_line_num ;
    yylval.sv_node->debug_linenum = debug_line_num ;
    yylval.sv_node->filename = input_file_name ;
    yylval.sv_node->location = lex_location ;
    lex_location += strlen(yytext) ;
    yylval.sv_node->type = Decimal_number ; 
    scan_v_decimal( yytext, &yylval.sv_node ) ;
    set_last( "decimal number", yytext ) ;
    flag = 1 ;
    return Decimal_number ;
  }
\'[sS]?[dD]{decimal}+   {
    yylval.sv_node = ALLOC_SV_NODE ;
    yylval.sv_node->name = (char *)strdup(yytext) ;
    yylval.sv_node->linenum = lex_line_num ;
    yylval.sv_node->debug_linenum = debug_line_num ;
    yylval.sv_node->filename = input_file_name ;
    yylval.sv_node->location = lex_location ;
    lex_location += strlen(yytext) ;
    yylval.sv_node->type = Decimal_number ; 
    scan_v_decimal( yytext, &yylval.sv_node ) ;
    set_last( "decimal number", yytext ) ;
    flag = 1 ;
    return Decimal_number ;
  }
{integerval}\'[sS]?[oO]{octal}+  {
    yylval.sv_node = ALLOC_SV_NODE ;
    yylval.sv_node->name = (char *)strdup(yytext) ;
    yylval.sv_node->linenum = lex_line_num ;
    yylval.sv_node->debug_linenum = debug_line_num ;
    yylval.sv_node->filename = input_file_name ;
    yylval.sv_node->location = lex_location ;
    lex_location += strlen(yytext) ;
    yylval.sv_node->type = Octal_number ; 
    scan_v_octal( yytext, &yylval.sv_node ) ;
    set_last( "octal number", yytext ) ;
    flag = 1 ;
    return Octal_number ;
  }
\'[sS]?[oO]{octal}+  {
    yylval.sv_node = ALLOC_SV_NODE ;
    yylval.sv_node->name = (char *)strdup(yytext) ;
    yylval.sv_node->linenum = lex_line_num ;
    yylval.sv_node->debug_linenum = debug_line_num ;
    yylval.sv_node->filename = input_file_name ;
    yylval.sv_node->location = lex_location ;
    lex_location += strlen(yytext) ;
    yylval.sv_node->type = Octal_number ; 
    scan_v_octal( yytext, &yylval.sv_node ) ;
    set_last( "octal number", yytext ) ;
    flag = 1 ;
    return Octal_number ;
  }
{integerval}\'[sS]?[hH]{hex}+  {
    yylval.sv_node = ALLOC_SV_NODE ;
    yylval.sv_node->name = (char *)strdup(yytext) ;
    yylval.sv_node->linenum = lex_line_num ;
    yylval.sv_node->debug_linenum = debug_line_num ;
    yylval.sv_node->filename = input_file_name ;
    yylval.sv_node->location = lex_location ;
    lex_location += strlen(yytext) ;
    yylval.sv_node->type = Hex_number ; 
    scan_v_hex( yytext, &yylval.sv_node ) ;
    set_last( "hex number", yytext ) ;
    flag = 1 ;
    return Hex_number ;
  }
\'[sS]?[hH]{hex}+  {
    yylval.sv_node = ALLOC_SV_NODE ;
    yylval.sv_node->name = (char *)strdup(yytext) ;
    yylval.sv_node->linenum = lex_line_num ;
    yylval.sv_node->debug_linenum = debug_line_num ;
    yylval.sv_node->filename = input_file_name ;
    yylval.sv_node->location = lex_location ;
    lex_location += strlen(yytext) ;
    yylval.sv_node->type = Hex_number ; 
    scan_v_hex( yytext, &yylval.sv_node ) ;
    set_last( "hex number", yytext ) ;
    flag = 1 ;
    return Hex_number ;
  }
{integerval}\'[sS]?[bB]{binary}+  {
    yylval.sv_node = ALLOC_SV_NODE ;
    yylval.sv_node->name = (char *)strdup(yytext) ;
    yylval.sv_node->linenum = lex_line_num ;
    yylval.sv_node->debug_linenum = debug_line_num ;
    yylval.sv_node->filename = input_file_name ;
    yylval.sv_node->location = lex_location ;
    lex_location += strlen(yytext) ;
    yylval.sv_node->type = Binary_number ; 
    scan_v_binary( yytext, &yylval.sv_node ) ;
    set_last( "binary number", yytext ) ;
    flag = 1 ;
    return Binary_number ;
  }
\'[sS]?[bB]{binary}+  {
    yylval.sv_node = ALLOC_SV_NODE ;
    yylval.sv_node->name = (char *)strdup(yytext) ;
    yylval.sv_node->linenum = lex_line_num ;
    yylval.sv_node->debug_linenum = debug_line_num ;
    yylval.sv_node->filename = input_file_name ;
    yylval.sv_node->location = lex_location ;
    lex_location += strlen(yytext) ;
    yylval.sv_node->type = Binary_number ; 
    scan_v_binary( yytext, &yylval.sv_node ) ;
    set_last( "binary number", yytext ) ;
    flag = 1 ;
    return Binary_number ;
  }
\'[01xXzZ] {
    yylval.sv_node = ALLOC_SV_NODE ;
    yylval.sv_node->name = (char *)strdup(yytext) ;
    yylval.sv_node->linenum = lex_line_num ;
    yylval.sv_node->debug_linenum = debug_line_num ;
    yylval.sv_node->filename = input_file_name ;
    yylval.sv_node->location = lex_location ;
    lex_location += strlen(yytext) ;
    yylval.sv_node->type = Decimal_number ; 
    set_last( "Unbased unsized literal", yytext ) ;
    flag = 1 ;
    return Unbased_unsized_literal ;
  }
{integerval}\.([0-9]+)?([eE][+-]?[0-9]+)?  {
    yylval.sv_node = ALLOC_SV_NODE ;
    yylval.sv_node->name = (char *)strdup(yytext) ;
    yylval.sv_node->linenum = lex_line_num ;
    yylval.sv_node->debug_linenum = debug_line_num ;
    yylval.sv_node->filename = input_file_name ;
    yylval.sv_node->location = lex_location ;
    lex_location += strlen(yytext) ;
    yylval.sv_node->type = Real_number ; 
    set_last( "real number", yytext ) ;
    flag = 1 ;
    return Real_number;
  }
0\.([0-9]+)?([eE][+-]?[0-9]+)?  {
    yylval.sv_node = ALLOC_SV_NODE ;

    yylval.sv_node->name = (char *)strdup(yytext) ;
    yylval.sv_node->linenum = lex_line_num ;
    yylval.sv_node->debug_linenum = debug_line_num ;
    yylval.sv_node->filename = input_file_name ;
    yylval.sv_node->location = lex_location ;
    lex_location += strlen(yytext) ;
    yylval.sv_node->type = Real_number ; 
    set_last( "real number", yytext ) ;
    flag = 1 ;
    return Real_number;
  }  
\.[0-9]+ {
    /* special case, both used for depth and floar */
    yylval.sv_node = ALLOC_SV_NODE ;
    yylval.sv_node->name = (char *)strdup(yytext) ;
    yylval.sv_node->linenum = lex_line_num ;
    yylval.sv_node->debug_linenum = debug_line_num ;
    yylval.sv_node->filename = input_file_name ;
    yylval.sv_node->location = lex_location ;
    lex_location += strlen(yytext) ;
    yylval.sv_node->type = Real_number ; 
    set_last( "real number", yytext ) ;
    flag = 1 ;
    return Real_number ;
}
\.[0-9]+[eE][+-]?[0-9]+  {
    yylval.sv_node = ALLOC_SV_NODE ;

    yylval.sv_node->name = (char *)strdup(yytext) ;
    yylval.sv_node->linenum = lex_line_num ;
    yylval.sv_node->debug_linenum = debug_line_num ;
    yylval.sv_node->filename = input_file_name ;
    yylval.sv_node->location = lex_location ;
    lex_location += strlen(yytext) ;
    yylval.sv_node->type = Real_number ; 
    set_last( "real number", yytext ) ;
    flag = 1 ;
    return Real_number ;
  }
{integerval}[eE][+-]?[0-9]+  {
    yylval.sv_node = ALLOC_SV_NODE ; 
    yylval.sv_node->name = (char *)strdup(yytext) ;
    yylval.sv_node->linenum = lex_line_num ;
    yylval.sv_node->debug_linenum = debug_line_num ;
    yylval.sv_node->filename = input_file_name ;
    yylval.sv_node->location = lex_location ;
    lex_location += strlen(yytext) ;
    yylval.sv_node->type = Real_number ; 
    set_last( "real number", yytext ) ;
    flag = 1 ;
    return Real_number ;
  }  
.  {
    yylval.sv_node = ALLOC_SV_NODE ;
    yylval.sv_node->name = (char *)strdup(yytext) ;
    yylval.sv_node->linenum = lex_line_num ;
    yylval.sv_node->debug_linenum = debug_line_num ;
    yylval.sv_node->filename = input_file_name ;
    yylval.sv_node->location = lex_location ;
    lex_location += strlen(yytext) ;
    yylval.sv_node->type = yytext[0] ;    
    set_last( "token", yytext ) ;
    flag = 1 ;
    return( yytext[0] ) ;
  }



%%

static void scan_v_decimal( char *number, systemverilog_node *node ) {
  char *cp = number ;
  char save ;
  int  size ;
  int tmp, prev ;
  
  if( *cp == '\'' ) {
    size = 32 ;
    cp++ ; /* skip ' */
  }
  else {
    while( isdigit(*cp) ) cp++ ;
    save = *cp ;
    *cp = '\0' ;  /* this location must be ' */
    size = atoi(number) ;
    *cp++ = save ;
    if( size == 0 ) {
      /* not valid number */
      return ;
    }
  }
  
  
  cp++ ; /* skip d/D */
  
  tmp = prev = 0 ;
  while( cp ) {
    prev = tmp ;
    tmp = ( tmp * 10 ) + (*cp - '0') ;
    if( tmp < prev ) return ; /* overflow */
    cp++ ;
  }
  node->const_flag = 1 ;
  node->const_value = tmp ;
  
}

static void scan_v_octal( char *number, systemverilog_node *node ) {
  char *cp = number ;
  char save ;
  int  size ;
  int tmp, prev ;
  
  if( *cp == '\'' ) {
    size = 32 ;
    cp++ ; /* skip ' */
  }
  else {
    while( isdigit(*cp) ) cp++ ;
    save = *cp ;
    *cp = '\0' ;  /* this location must be ' */
    size = atoi(number) ;
    *cp++ = save ;
    if( size == 0 ) {
      return ;
    }
  }
  
  cp++ ; /* skip o/O */
  
  tmp = prev = 0 ;
  while( cp ) {
    if( *cp != '_' ) {
      prev = tmp ;
      tmp = ( tmp * 8 ) + (*cp - '0') ;
      if( tmp < prev ) return ; /* overflow */
    }
    cp++ ;
  }
  node->const_flag = 1 ;
  node->const_value = tmp ;
  
}

static void scan_v_hex( char *number, systemverilog_node *node ) {
  char *cp = number ;
  char save ;
  int  size ;
  int tmp, prev ;
  
  if( *cp == '\'' ) {
    size = 32 ;
    cp++ ; /* skip ' */
  }
  else {
    while( isdigit(*cp) ) cp++ ;
    save = *cp ;
    *cp = '\0' ;  /* this location must be ' */
    size = atoi(number) ;
    *cp++ = save ;
    if( size == 0 ) {
      return ;
    }
  }
  
  cp++ ; /* skip o/O */
  
  tmp = prev = 0 ;
  while( cp ) {
    if( *cp != '_' ) {
      prev = tmp ;
      if( *cp >= '0' && *cp <= '9' ) 
        tmp = ( tmp * 16 ) + (*cp - '0') ;
      if( *cp >= 'A' && *cp <= 'F' )
        tmp = ( tmp * 16 ) + (*cp - 'A') ;
      if( *cp >= 'a' && *cp <= 'f' )
        tmp = ( tmp * 16 ) + (*cp - 'a') ;
      if( tmp < prev ) return ; /* overflow */
    }
    cp++ ;
  }
  node->const_flag = 1 ;
  node->const_value = tmp ;
  
}

static void scan_v_binary( char *number, systemverilog_node *node ) {
  char *cp = number ;
  char save ;
  int  size ;
  int tmp, prev ;
  
  if( *cp == '\'' ) {
    size = 32 ;
    cp++ ; /* skip ' */
  }
  else {
    while( isdigit(*cp) ) cp++ ;
    save = *cp ;
    *cp = '\0' ;  /* this location must be ' */
    size = atoi(number) ;
    *cp++ = save ;
    if( size == 0 ) {
      return ;
    }
  }
  
  cp++ ; /* skip o/O */
  
  tmp = prev = 0 ;
  while( cp ) {
    if( *cp != '_' ) {
      prev = tmp ;
      tmp = ( tmp * 2 ) + (*cp - '0') ;
      if( tmp < prev ) return ; /* overflow */
    }
    cp++ ;
  }
  node->const_flag = 1 ;
  node->const_value = tmp ;
  
}


static void set_last( char *type, char *token ){
  /* if( last_text ) free(last_text) ; */
  
  last_text = (char *)calloc( strlen(type)+strlen(token)+10, sizeof(char) ) ;
  
  strcat( last_text, type ) ;
  strcat( last_text, " \"" ) ;
  strcat( last_text, token ) ;
  strcat( last_text, "\"" ) ;
}


static unsigned search_keyword(char *pattern)
{
  int i ;
  
  i = 0 ;
  while(keyword_table[i].pattern != NULL ) {
    if( !strcmp( pattern, keyword_table[i].pattern ) ) {
      return keyword_table[i].token ;
    }
    i++ ;
  }
  return( 0 ) ;
}

int yywrap(void) { return 1; }

static lex_error() {
  printf( "Lex error detected!!\n" ) ;
}

int lex_catch_it() {
  printf( "Lex catch %s!\n", yytext ) ;
}
