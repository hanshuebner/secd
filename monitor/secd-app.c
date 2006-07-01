
#include "system09.h"

extern void outc(char c);

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
blink()
{
  unsigned char c = 0;
  for (;;) {
    led = 0;
    led = 1;
  }
}

void
clear_secd_memory()
{
  unsigned long high, low;

  for (high = 0; high < 256; high++) {
    secd_address_high = high;
    for (low = 0; low < 256; low++) {
      secd_address_low = low;
      secd_data = 0;
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

void
delay()
{
  volatile unsigned i, j;

  for (i = 0; i < 254; i++) {
    for (j = 0; j < 254; j++) {
    }
  }
}

int
main()
{
  int x = 0;
  
  putstring("SECD Monitor V1.0\r\n");
  secd_status = SECD_CONTROL_STOP;

  for (;;) {
    putstring("doit");
    delay();
    led = x;
    delay();
    led = x;
    x = ++x & 0xF;
  }

#if 0
/*   clear_secd_memory(); */

  setup_secd_program();

  secd_status = SECD_CONTROL_BUTTON;
#endif
  blink();
}

