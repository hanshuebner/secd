Hol=/usr/groups/hol/HOL21/bin/hol
# =====================================================================
#
# 		 MAKEFILE FOR THE HOL LIBRARY: wordn
#
# =====================================================================

# =====================================================================
#
# MAIN ENTRIES:
#
# make all	    : create theories and compile code
#
# make clean	    : remove theories and compiled code
#	
# =====================================================================

# =====================================================================
# MACROS:
#
# Hol	    : the pathname of the version of hol used
# =====================================================================

# =====================================================================
#                                 mk_bus.ml
#                                     |
#             mk_wordn.ml           bus.th        bus.ml
#                 |                   |             |
#                 +------------------'|`----+-------'
#                 |                   |     |
#              wordn.th    wordn.ml   |  bus_ml.o
#                 |           |       |     |
#                 `-----------+-------+-----'
#                             |      
#                             |
#                          wordn_ml.o
# =====================================================================


clean:
	rm -f *_ml.o *_ml.l *.th 
	@echo "===> library wordn: all object code and theory files deleted"

bus.th: mk_bus.ml
	rm -f bus.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_bus`;;'\
             'quit();;' | ${Hol} 

wordn.th: mk_wordn.ml bus.th
	rm -f wordn.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_wordn`;;'\
             'quit();;' | ${Hol} 

bus_ml.o: bus.ml bus.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_theory `bus`;;'\
	     'compilet `bus`;;'\
	     'quit();;' | ${Hol}

wordn_ml.o: wordn.ml wordn.th bus_ml.o bus.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_theory `wordn`;;'\
	     'compilet `wordn`;;'\
	     'quit();;' | ${Hol}

all:	wordn_ml.o
	@echo "===> library wordn rebuilt"

