Hol=/usr/groups/hol/HOL21/bin/hol
#
#                   intermediate     wordn                                 integer
#                        |            |                          .-----------+    
#                ,-------|------------+-----+--------------+-----|----------.|    
#                |       |            |     |              | modulo_ops      |     
#                |       |         val_defs |              |     |`---------.|    
# DATA           |       |            |     |       bus_theorems |           |     
# TYPES:      cu_types   |            |  dp_types          |     |     abstract_mem_type
#                |       |            |     |`-------------|-----|----------.|   
#                |       |            |     |              |     |           |       
# MISC:          |       |  interface |     |              |     |      .---'|   
#                |       |      |     |,----|--------------|-----'      |    |    
#                |`-----.|------|-----|-----|--------------|------------|---.|  
#                |       |      |     |     |              |            |    |        
# D              |   microcode  |`---.|,----^----.         |            |    |   
# E              |       |      |     |          |         |            |    |  
# F              |     rt_CU    |   rt_DP     rt_PADS      |            |    | 
# I              |       |      |     |          |         |            |    | 
# N              |       |`-----|-----|`---v----'          |            |    | 
# I              |       |      |     |    |               |            |    |    
# T              |       |      |     | rt_SECD            |            |    |  
# I              |       |      |     |    |`---.          |            |    |    
# O              |       |      |     |    |  rt_SYS       |            | top_SECD
# N              |       |      |     |    |    |          |            |    |   
# S              |       |      |     |    |    |`--------.|            |    |`-------.
#                |       |      |     |    |    |      val_theorems     |    |        |          
#                |       |      |     |    |    |          `-----------.|----|-------.|
#       .-------'|       |      |     |    |    |`----v-----------------|----'        |          
#      |         |       |      |     |    |    |     |                 |             |          
# U Inc9_proofs  |       |      |     |    |    | constraints           |      when   |     
# N    | CU_wordn_proofs |      |     |    |    |     |                 |        |    |          
# W    |         |       |      |     |    |    |     |                 |        |    |          
# I     `--------`------.|,----'------|,---|----|----'|`---------------.|        |    |          
# N                      |            |    |    |     |                 |        |    |          
# D                  CU_proofs   DP_proofs |    |`----|----------------.|        |    |          
#                        |            `---.|    |     |                 |        |    |          
#                         `---------------.|    |     |                 |        |    |          
#                                   SECD_proofs |     |              mem_abs     |    |          
#                                          |    |     |                 |        |    |          
#                                          `---.|     |                 |        |    |          
#                                          SYS_proofs |                 |        |    |          
#                             phase_template    |     |                 |        |    |          
# P                                `-----------.|     |                 |        |    |          
# H                                   phase_proof_fcn |                 |        |    |          
# A                                             |     |                 |`-------|----|-------.  
# S                                      phase_lemmas |                 |        |    |       |  
# E                                           1 - 7   |                 |        |    |       |  
#                                               |     |                 |        |    |       |  
#                                               |,---'|-----------------'--------'    |       |  
#                                               |     |                               |       |  
#                                               |     |                               |       |  
#                                               | mu-prog_level                       |       |  
#                                               |     |                               |       |  
#                                               |,----'                          loop_proofs  |  
# M                                             |                                     |       |  
# I                   ,------------------+-----'|                                     |       |  
# C                   |                  | mu-prog_proof_fcn.ml                       |       |  
# R                   |                  |      |                                     |       |  
# O                   |                  |      `---------.                           |       |  
# P                   |                  |                |                           |       |  
# R            mu-prog_proof0   mu-prog_sr_proofs  mu-prog_init_proofs                |       |  
# O                   |                  |                |                           |       |  
# G                   |                  |                |                           |       |  
# R                   |                  `---------v------'                           |       |  
# A                   |                            |                                  |       |  
# M                   |                            +--------------------------v-------'       |  
# M                   |                            |                          |               |  
# I                   |                mu-prog_LDC, ..., mu-prog_STOP    mu-prog_LD1          |  
# N                   |                            |                          |               |  
# G                   |                            |                      mu-prog_LD2         |  
#                     |                            |                          |               |  
#                     |                            |                      mu-prog_LD          |  
#                     `---------------------------.|,-------------------------'               |  
#                                                  |                                          |  
#                                                  |`-----.                                   |  
#                                                  |  simplify                                |  
#                                                  |                                          |  
# LIVENESS                                      liveness                               correctness_misc 
#                                                  |                                          |  
#                                                  |,-----------------------------------------'  
#                                                  |                     
#                                                  |                                
# ABSTR                   correctness_init, correctness_LD, ... correctness_STOP
#                                                  |
#                                             correctness
#

all: definitions unwind phase mu-prog liveness correct
definitions: mem_abs.th
unwind: SYS_proofs.th
phase: phase_lemmas1.th phase_lemmas2.th phase_lemmas3.th phase_lemmas4.th phase_lemmas5.th phase_lemmas6.th phase_lemmas7.th
mu-prog: simplify.th
liveness: liveness.th
correct: correctness.th

.SUFFIXES: .th .ml

# .ml.th:;	/bin/rm -f $*.th $*.log ; nice /usr/groups/hol/CL_hol/Sparc/hol < $*.ml > $*.log 2>&1
# .ml.th:;	/bin/rm -f $*.th $*.log ; ${Hol} < $*.ml > $*.log 2>&1

.ml.th:;	/bin/rm -f $*.th $*.log
		echo 'loadt `$*`;;'\
                     'quit();;' | ${Hol} > $*.log 2>&1


# wordn data type library and auxiliaries:
# ----------------------------------------
wordn/wordn_ml.o: wordn/mk_bus.ml   wordn/bus.ml   wordn/bus.th wordn/bus_ml.o
wordn/wordn_ml.o: wordn/mk_wordn.ml wordn/wordn.ml wordn/wordn.th
		(cd wordn; $(MAKE) Hol=${Hol} all; cd ..)

buses/bus_theorems.th: wordn/wordn_ml.o
		(cd buses; $(MAKE) bus_theorems.th; cd ..)

# data type definition files:
# ---------------------------
cu_types.th:  wordn/wordn_ml.o

dp_types.th:  wordn/wordn_ml.o

abstract_mem_type.th: modulo_ops.th
abstract_mem_type.th: wordn/wordn_ml.o

# miscellaneous relations, definitions, theorems:
# -----------------------------------------------
modulo_ops.th:

interface.th:

mem_abs.th:   abstract_mem_type.th
mem_abs.th:   rt_SYS.th
mem_abs.th:   val_theorems.th
mem_abs.th:   constraints.th

val_defs.th:

val_theorems.th: rt_SYS.th
val_theorems.th: buses/bus_theorems.th

when.th:

constraints.th: top_SECD.th
constraints.th: rt_SYS.th

# rt_level specification:
# -----------------------
intermediate:

microcode.th: intermediate
microcode.th: io.ml
microcode.th: cu_types.th

rt_CU.th:     microcode.th

rt_DP.th:     dp_types.th
rt_DP.th:     interface.th
rt_DP.th:     modulo_ops.th
rt_DP.th:     val_defs.th

rt_PADS.th:   dp_types.th

rt_SECD.th:   rt_CU.th
rt_SECD.th:   rt_DP.th
rt_SECD.th:   rt_PADS.th

rt_SYS.th:    rt_SECD.th

# top level specification:
# ------------------------
top_SECD.th:     dp_types.th
top_SECD.th:     cu_types.th
top_SECD.th:     abstract_mem_type.th

# PROOFS:
# =======

# unwinding the system rt level definitions:
# ------------------------------------------
Inc9_proofs.th:   cu_types.th

CU_wordn_proofs.th: cu_types.th

CU_proofs.th:   rt_CU.th
CU_proofs.th:   interface.th
CU_proofs.th:   constraints.th
CU_proofs.th:   Inc9_proofs.th
CU_proofs.th:   CU_wordn_proofs.th

DP_proofs.th:	rt_DP.th
DP_proofs.th:   constraints.th

SECD_proofs.th:	rt_SECD.th
SECD_proofs.th:	CU_proofs.th
SECD_proofs.th:	DP_proofs.th

SYS_proofs.th:	rt_SYS.th
SYS_proofs.th:	SECD_proofs.th

# phase level:
# ------------
phase_lemmas1.th: SYS_proofs.th
phase_lemmas1.th: phase_proof_fcn.ml phase_template.ml
phase_lemmas2.th: SYS_proofs.th
phase_lemmas2.th: phase_proof_fcn.ml phase_template.ml
phase_lemmas3.th: SYS_proofs.th
phase_lemmas3.th: phase_proof_fcn.ml phase_template.ml
phase_lemmas4.th: SYS_proofs.th
phase_lemmas4.th: phase_proof_fcn.ml phase_template.ml
phase_lemmas5.th: SYS_proofs.th
phase_lemmas5.th: phase_proof_fcn.ml phase_template.ml
phase_lemmas6.th: SYS_proofs.th
phase_lemmas6.th: phase_proof_fcn.ml phase_template.ml
phase_lemmas7.th: SYS_proofs.th
phase_lemmas7.th: phase_proof_fcn.ml phase_template.ml

# microprogramming level:
# -----------------------
mu-prog_level.th: constraints.th

loop_proofs.th: val_theorems.th
loop_proofs.th: top_SECD.th

# the initial state correctness proof :
mu-prog_proof0.th:  constraints.th
mu-prog_proof0.th:  mem_abs.th
mu-prog_proof0.th:  when.th
mu-prog_proof0.th:  phase_lemmas1.th

# this proves the subroutine correctness theorems ...
mu-prog_sr_proofs.th:  mem_abs.th
mu-prog_sr_proofs.th:  when.th
mu-prog_sr_proofs.th:  phase_lemmas7.th

# this proves the major state transitions, and start of all
# the machine instruction transitions ...
mu-prog_init_proofs.th:  mem_abs.th
mu-prog_init_proofs.th:  when.th
mu-prog_init_proofs.th:  phase_lemmas1.th
mu-prog_init_proofs.th:  mu-prog_proof_fcn.ml mu-prog_level.th

# the individual instruction sequences
mu-prog_LD1.th:   phase_lemmas2.th mu-prog_sr_proofs.th mu-prog_init_proofs.th loop_proofs.th
mu-prog_LD2.th:	mu-prog_LD1.th

mu-prog_LD.th:	mu-prog_LD2.th
mu-prog_LDC.th:   phase_lemmas2.th mu-prog_sr_proofs.th mu-prog_init_proofs.th 
mu-prog_LDF.th:   phase_lemmas3.th mu-prog_sr_proofs.th mu-prog_init_proofs.th 
mu-prog_AP.th:    phase_lemmas3.th mu-prog_sr_proofs.th mu-prog_init_proofs.th 
mu-prog_RTN.th:   phase_lemmas3.th mu-prog_sr_proofs.th mu-prog_init_proofs.th 
mu-prog_DUM.th:   phase_lemmas4.th mu-prog_sr_proofs.th mu-prog_init_proofs.th 
mu-prog_RAP.th:   phase_lemmas4.th mu-prog_sr_proofs.th mu-prog_init_proofs.th 
mu-prog_SEL.th:   phase_lemmas4.th mu-prog_sr_proofs.th mu-prog_init_proofs.th 
mu-prog_JOIN.th:  phase_lemmas5.th mu-prog_sr_proofs.th mu-prog_init_proofs.th 
mu-prog_CAR.th:   phase_lemmas5.th mu-prog_sr_proofs.th mu-prog_init_proofs.th 
mu-prog_CDR.th:   phase_lemmas5.th mu-prog_sr_proofs.th mu-prog_init_proofs.th 
mu-prog_ATOM.th:  phase_lemmas5.th mu-prog_sr_proofs.th mu-prog_init_proofs.th 
mu-prog_CONS.th:  phase_lemmas6.th mu-prog_sr_proofs.th mu-prog_init_proofs.th 
mu-prog_EQ.th:    phase_lemmas6.th mu-prog_sr_proofs.th mu-prog_init_proofs.th 
mu-prog_ADD.th:   phase_lemmas6.th mu-prog_sr_proofs.th mu-prog_init_proofs.th 
mu-prog_SUB.th:   phase_lemmas6.th mu-prog_sr_proofs.th mu-prog_init_proofs.th 
mu-prog_LEQ.th:   phase_lemmas6.th mu-prog_sr_proofs.th mu-prog_init_proofs.th 
mu-prog_STOP.th:  phase_lemmas6.th mu-prog_sr_proofs.th mu-prog_init_proofs.th 

# liveness:
# ---------
liveness.th: mu-prog_LD.th mu-prog_LDC.th mu-prog_LDF.th mu-prog_AP.th
liveness.th: mu-prog_RTN.th mu-prog_DUM.th mu-prog_RAP.th mu-prog_SEL.th
liveness.th: mu-prog_JOIN.th mu-prog_CAR.th mu-prog_CDR.th mu-prog_ATOM.th 
liveness.th: mu-prog_CONS.th mu-prog_EQ.th mu-prog_ADD.th mu-prog_SUB.th 
liveness.th: mu-prog_LEQ.th mu-prog_STOP.th mu-prog_proof0.th mu-prog_init_proofs.th 

# simplifications reduce term size only:
# --------------------------------------
simplify.th: mu-prog_LD.th mu-prog_LDC.th mu-prog_LDF.th mu-prog_AP.th
simplify.th: mu-prog_RTN.th mu-prog_DUM.th mu-prog_RAP.th mu-prog_SEL.th
simplify.th: mu-prog_JOIN.th mu-prog_CAR.th mu-prog_CDR.th mu-prog_ATOM.th 
simplify.th: mu-prog_CONS.th mu-prog_EQ.th mu-prog_ADD.th mu-prog_SUB.th 
simplify.th: mu-prog_LEQ.th mu-prog_STOP.th mu-prog_proof0.th mu-prog_init_proofs.th 

# the proofs of correspondence at the top level:
# ----------------------------------------------
correctness_misc.th: mem_abs.th
correctness_LD.th:	liveness.th correctness_misc.th
correctness_LDC.th:	liveness.th correctness_misc.th
correctness_LDF.th:	liveness.th correctness_misc.th
correctness_AP.th:	liveness.th correctness_misc.th
correctness_RAP.th:	liveness.th correctness_misc.th 
correctness_DUM.th:	liveness.th correctness_misc.th 
correctness_RTN.th:	liveness.th correctness_misc.th 
correctness_SEL.th:	liveness.th correctness_misc.th 
correctness_JOIN.th:	liveness.th correctness_misc.th 
correctness_CAR.th:	liveness.th correctness_misc.th 
correctness_CDR.th:	liveness.th correctness_misc.th 
correctness_CONS.th:	liveness.th correctness_misc.th 
correctness_ATOM.th:	liveness.th correctness_misc.th 
correctness_ADD.th:	liveness.th correctness_misc.th 
correctness_SUB.th:	liveness.th correctness_misc.th 
correctness_EQ.th:	liveness.th correctness_misc.th 
correctness_LEQ.th:	liveness.th correctness_misc.th 
correctness_STOP.th:	liveness.th correctness_misc.th 
correctness_init.th:	liveness.th correctness_misc.th 

# the top level theory:
# ---------------------
correctness.th:	liveness.th
correctness.th:	correctness_init.th 
correctness.th:	correctness_LD.th 
correctness.th:	correctness_LDC.th 
correctness.th:	correctness_LDF.th 
correctness.th:	correctness_AP.th 
correctness.th:	correctness_RTN.th 
correctness.th:	correctness_DUM.th 
correctness.th:	correctness_RAP.th 
correctness.th:	correctness_SEL.th 
correctness.th:	correctness_JOIN.th 
correctness.th:	correctness_CAR.th 
correctness.th:	correctness_CDR.th 
correctness.th:	correctness_ATOM.th 
correctness.th:	correctness_CONS.th 
correctness.th:	correctness_ADD.th 
correctness.th:	correctness_SUB.th 
correctness.th:	correctness_EQ.th 
correctness.th:	correctness_LEQ.th 
correctness.th:	correctness_STOP.th 
