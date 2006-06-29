Hol=/usr/groups/hol/HOL21/bin/hol
#
#              wordn_ml.o
#		   |		
#           mk_bus_theorems.ml
#		   |		
#            bus_theorems.th      
#		   |        
#            bus_theorems.ml
#		   |        
#           bus_theorems_ml.o

all: bus_theorems_ml.o

clean:
	rm -f *_ml.o *_ml.l *.th 
	@echo "===> bus_theorems: all object code and theory files deleted"

bus_theorems.th: mk_bus_theorems.ml 
	rm -f bus_theorems.th
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'loadt `mk_bus_theorems`;;'\
             'quit();;' | ${Hol} 

bus_theorems_ml.o: bus_theorems.th bus_theorems.ml
	echo 'set_flag(`abort_when_fail`,true);;'\
	     'load_theory `bus_theorems`;;'\
	     'compilet `bus_theorems`;;'\
	     'quit();;' | ${Hol}

