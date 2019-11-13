GHDL ?= ghdl
GHDL_FLAGS ?= --ieee=synopsys -Wno-hide --std=08 -fexplicit
WORKDIR=work

MODULES=secd_defs clock_gen ../secd-microcode control_unit secd_ram_defs datapath secd_ram secd_toplevel

.PHONY: all clean

all:
	$(GHDL) -a $(GHDL_FLAGS) --work=unisim --workdir=$(WORKDIR) $(MODULES:=.vhd)

clean:
	rm -f $(WORKDIR)/*
