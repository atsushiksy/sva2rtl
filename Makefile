
MK = gmake

CC = gcc -lang-c-c++-comments -g -DYYRESTART -DEVALEXP -DYYDEBUG=1 -fnested-functions

CMP_SRC = main.c symtab.c codegen.c
CMP_OBJ = ${CMP_SRC:.c=.o}

CMP_INC = systemverilog_node.h symtab.h code_def.h
 
LEX_INC =  y_tab.h \
           SystemVerilog_keyword_table.h 

LEX_SRC = lex.yy.c
LEX_OBJ = ${LEX_SRC:.c=.o}

YACC_OUT = y_tab.c y_tab.h y.output
YACC_SRC = y_tab.c
YACC_OBJ = ${YACC_SRC:.c=.o}
YACC_HDR = y_tab.h
YACC_DBGOBJ = y_tab_dbg.o

PARSE_INC = systemverilog_node.h

PARSE_IN = Verilog.y.pp SystemVerilogOperators.data

PARSE_OUT = SystemVerilog.y.prep SV_token_table.h \
            SystemVerilog_keyword_table.h SystemVerilog_operator_lex.h \
            SV_keywords.data

TARGET = sva2rtl

all: ${TARGET}

clean:
	rm *.o ${PARSE_OUT}

$CMP_OBJ}: ${CMP_SRC} ${CMP_INC}

sva2rtl: ${YACC_OBJ} ${LEX_OBJ} ${CMP_OBJ}
	gcc -o $@ -dn ${YACC_OBJ} ${LEX_OBJ} ${CMP_OBJ} -lfl -lm -ll -lc -lpthread -ltermcap

${YACC_OUT}: SystemVerilog.y
	btyacc -d -l -v SystemVerilog.y

SystemVerilog.y: gen_action.pl SV_parser_action.data SystemVerilog.y.prep SV_keywords.data
	./gen_action.pl < SystemVerilog.y.prep > $@

${PARSE_OUT}: parse_yacc.pl ${PARSE_IN} Verilog.y.pp
	./parse_yacc.pl < Verilog.y.pp

${YACC_OBJ}: ${YACC_SRC} ${PARSE_INC}

## lex generation

SystemVerilog.l: gen_lfile.pl SystemVerilog.l.pp SystemVerilog_operator_lex.h
	./gen_lfile.pl > $@


${LEX_SRC}: SystemVerilog.l
	flex -L SystemVerilog.l

${LEX_OBJ}: ${LEX_INC}