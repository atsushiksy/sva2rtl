/***************************************************************************
 *
 *  code_def.h: various definitions for RTL code
 *
 *  Author: Atsushi Kasuya
 *
 *   Copyright (C) 2011 Atsushi Kasuya 
 *
 ***************************************************************************/

#define ARV_VERSION "0.3"

#define ARV_RESET_ "ARV_resetN"
#define ARV_CLEAR  "ARV_clear"
#define ARV_ENABLE "ARV_enable"
#define ARV_ERROR  "ARV_error"
#define ARV_MATCH  "ARV_match"
#define ARV_COVER  "ARV_cover"
#define ARV_OVERWRAP "ARV_overwrap"
 
#define ARV_CLOCK "ARV_clock"

 
#define ARV_INST_TMP "No_Label_%d"

#define ARV_CYC_COUNTER_W 32
 
#define ARV_WIRE "ARV_wire_" 
#define ARV_REG  "ARV_reg_%d"
 
#define ARV_SYSFUNK_BLK  "ARV_SYSFUNC_BLK"
#define ARV_SF_INST  "ARV_SF_INST_" 
#define ARV_SYSFNK_ARG   "    .Clk(ARV_wire_%d), .RN(ARV_resetN), .E(ARV_enable), .C(ARV_clear), .D(ARV_wire_%d), .ROSE(ARV_wire_%d), .FELL(ARV_wire_%d), .STBL(ARV_wire_%d), .PAST(ARV_wire_%d), .SMPL(ARV_wire_%d)"

#define ARV_SYSFUNK_PAST_BLK  "ARV_SYSFUNC_PAST_BLK"
#define ARV_SYSFNK_PAST_ARG   "    .Clk(ARV_wire_%d), .RN(ARV_resetN), .E(ARV_enable), .C(ARV_clear), .D(ARV_wire_%d), .PAST(ARV_wire_%d)"

#define ARV_SYNC_FF_NUM "ARV_SYNC_FF_NUM"

#define ARV_USE_COUNTER 10
#define ARV_USE_FLAT_REP 4

#define ARV_DELAY_COUNTER_FF 1
#define ARV_DELAY_COUNTER_AND 4
#define ARV_DELAY_COUNTER_OR 4
#define ARV_DELAY_COUNTER_NOT 4

#define ARV_DELAY_PIPE_FF 1
#define ARV_DELAY_PIPE_AND 4
#define ARV_DELAY_PIPE_OR 4
#define ARV_DELAY_PIPE_NOT 4

#define ARV_DELAY_EVER_FF 1
#define ARV_DELAY_EVER_AND 4
#define ARV_DELAY_EVER_OR 4
#define ARV_DELAY_EVER_NOT 4

#define ARV_SEQ_AND_FF 2
#define ARV_SEQ_AND_AND 3
#define ARV_SEQ_AND_OR 8
#define ARV_SEQ_AND_NOT 3

#define ARV_C_REP_E_FF 1
#define ARV_C_REP_E_AND 4
#define ARV_C_REP_E_OR 4
#define ARV_C_REP_E_NOT 4

#define ARV_C_REP_S_FF 1
#define ARV_C_REP_S_AND 4
#define ARV_C_REP_S_OR 4
#define ARV_C_REP_S_NOT 4

#define ARV_G_REP_FF 1
#define ARV_G_REP_AND 4
#define ARV_G_REP_OR 4
#define ARV_G_REP_NOT 4

#define ARV_THROUGHOUT_FF 1
#define ARV_THROUGHOUT_AND 8
#define ARV_THROUGHOUT_OR 8
#define ARV_THROUGHOUT_NOT 8

#define ARV_ERROR_GEN_FF 1
#define ARV_ERROR_GEN_AND 6
#define ARV_ERROR_GEN_OR 6
#define ARV_ERROR_GEN_NOT 6

#define ARV_PRP_AND_FF 4
#define ARV_PRP_AND_AND 18
#define ARV_PRP_AND_OR 10
#define ARV_PRP_AND_NOT 12

#define ARV_PRP_OR_FF 5
#define ARV_PRP_OR_AND 19
#define ARV_PRP_OR_OR 13
#define ARV_PRP_OR_NOT 6
