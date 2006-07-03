
#include "system09.h"

extern void outc(char c);
extern char inch();

void
delay()
{
  volatile unsigned i, j;

  for (i = 0; i < 254; i++) {
    for (j = 0; j < 254; j++) {
    }
  }
}

void
acia_putchar(char c)
{
  while (!(acia_control & 2)) {
  }
  acia_data = (unsigned char) c;
}

char
acia_getchar()
{
  while (!(acia_control & 1)) {
  }
  return (char) acia_data;
}

void
putstring(const char* s)
{
  while (*s) {
    outc(*s++);
  }
}

void
puthex(unsigned short x)
{
  const char* table = "0123456789ABCDEF";
  outc(table[(x & 0xF0) >> 4]);
  outc(table[x & 0x0F]);
}

void
dump_page(unsigned page)
{
  secd_address_high = page;
  secd_address_low = 0;
  putstring("\x16\x1A");
  do {
    puthex(secd_address_high);
    puthex(secd_address_low);
    do {
      outc(' ');
      puthex(secd_data);
    } while (++secd_address_low & 0x0F);
    outc('\r');
    outc('\n');
  } while (secd_address_low);
}

void
blink()
{
  unsigned char c = 0;
  for (;;) {
    led = 0;
    led = 1;
  }
}

void
clear_secd_memory(unsigned value)
{
  unsigned long high, low;

  for (high = 0; high < 256; high++) {
    secd_address_high = high;
    for (low = 0; low < 256; low++) {
      secd_address_low = low;
      secd_data = value;
      if (secd_data != value) {
        putstring("Failed to set "); puthex(secd_address_high); puthex(secd_address_low); putstring("\r\n");
        break;
      }
    }
  }
}

void
pattern_secd_memory()
{
  unsigned long high, low;

  for (high = 0; high < 256; high++) {
    secd_address_high = high;
    for (low = 0; low < 256; low++) {
      secd_address_low = low;
      secd_data = low;
      if (secd_data != low) {
        putstring("Failed to set "); puthex(secd_address_high); puthex(secd_address_low); putstring("\r\n");
        break;
      }
    }
  }
}

void
lcd_init()
{
}

void
lcd_putc(char c)
{
  lcd = c;
}

void
lcd_puts(const char* s)
{
  while (*s) {
    lcd_putc(*s++);
  }
}

const unsigned short program[] = {
0x0, 0x0, 0x0, 0x20, 
0x1, 0x0, 0x0, 0x20, 
0x2, 0x0, 0x0, 0x20, 
0xD, 0x0, 0x0, 0x30, 

0x15, 0x0, 0x0, 0x30, 
0x0, 0x0, 0x1, 0x0, 
0x5, 0xC0, 0x0, 0x0, 
0x1, 0x0, 0x0, 0x30, 

0x2, 0x0, 0x0, 0x30, 
0x0, 0x0, 0x2, 0x0, 
0x9, 0xC0, 0x1, 0x0, 
0x0, 0x80, 0x2, 0x0, 

0x0, 0xC0, 0x2, 0x0, 
0xC, 0x80, 0x1, 0x0
};

void
setup_secd_program()
{
  unsigned short i;

  secd_address_high = 0x00;

  for (i = 0; i < sizeof program; i++) {
    short buf = program[i];
    secd_address_low = i;
    secd_data = buf;
  }

  secd_address_high = 0xff;

  secd_address_low = 0xfc;
  secd_data = 0xff;
  secd_address_low = 0xfd;
  secd_data = 0x7f;
  secd_address_low = 0xfe;
  secd_data = 0x03;
  secd_address_low = 0xff;
  secd_data = 0x00;
}

void screen_funk()
{
  vdu_voffset = 0;
  vdu_vcursor = 0;
  for (vdu_hcursor = 0; vdu_hcursor < 80; vdu_hcursor++) {
    vdu_color = vdu_hcursor ^ vdu_vcursor;
    vdu_char = "SECD"[vdu_hcursor & 0x3];
  }
  vdu_color = 0x07;
}

int
main()
{
  secd_status = SECD_CONTROL_STOP;

  putstring("\n\n\rSECD Monitor V1.0\r\n");

  putstring("Clearing memory\r\n");
  clear_secd_memory(0);

  for (;;) {
    dump_page(secd_address_high);
    for (;;) {
      if (~joystick & JOYSTICK_RIGHT_MASK) {
        secd_address_high++;
        break;
      }
      if (~joystick & JOYSTICK_LEFT_MASK) {
        secd_address_high--;
        break;
      }
      if (~joystick & JOYSTICK_FIRE_MASK) {
        putstring("Setting memory pattern\r\n");
        pattern_secd_memory(0);
      }
      if (~joystick & JOYSTICK_DOWN_MASK) {
        putstring("Overwriting memory\r\n");
        clear_secd_memory(secd_data + 1);
      }
    }
  }
  
  putstring("Polling memory\r\n");
  while (1) {
    long foo;
    unsigned long high, low;

    for (high = 0; high < 256; high++) {
      secd_address_high = high;
      for (low = 0; low < 256; low++) {
        secd_address_low = low;
        foo += secd_data;
        puthex(high); puthex(low); outc(' '); puthex(secd_data); outc('\r'); outc('\n');
      }
    }
  }

#if 0
/*   clear_secd_memory(); */

  setup_secd_program();

  secd_status = SECD_CONTROL_BUTTON;
#endif
  blink();
}

