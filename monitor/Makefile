CC	= /usr/local/m6809/bin/gcc-3.4.5
AS	= /usr/local/m6809/bin/as6809
LINK	= /usr/local/m6809/bin/aslink
S192VHD = ../tools/s19-to-vhdl.pl

CFLAGS	= -std=c99 # -O

ASFLAGS	= -gloaxsff

.SUFFIXES: .c .asm .rel .s19 .vhd .bin

all: secd-app.s19

secd-app.s19: secd-app.rel app-start.rel secd-app.lnk
	$(LINK) -f secd-app

secd-mon.s19: secd-mon.rel vec.rel secd-mon.lnk
	$(LINK) -f secd-mon

secd-mon.vhd: secd-mon.s19
	$(S192VHD) -s 2048 -n mon_rom $<

clean:
	rm -f *.rel *.s19 *.map *.lst *.rel *.rst *.sym *.noi *.vhd

.c.asm:
	$(CC) $(CFLAGS) -o $*.asm -S $<

.asm.rel:
	$(AS) $(ASFLAGS) $<

.s19.vhd:
	$(S192VHD) $<