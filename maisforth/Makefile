
all:	$(TARGET).vhd $(TARGET).bin $(TARGET).bit

$(TARGET).bin:
	gforth -i

$(TARGET).mem:
	perl ../tools/bin-to-mem.pl an601.bin

$(TARGET).bit:
	data2mem -bm maisforth_rom_bd.bmm -bt my_system09.bit -bd an601.mem -o b final.bit

$(TARGET).vhd:
	perl ../tools/bin-to-ramb16.pl an601.bin