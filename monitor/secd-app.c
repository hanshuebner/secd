
#include "system09.h"

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
acia_puts(const char* s)
{
  while (*s) {
    acia_putchar(*s++);
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
      secd_mem[low] = 0;
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
    secd_mem[i] = buf;
  }

  secd_address_high = 0xff;
  secd_mem[0xfc] = 0xff;
  secd_mem[0xfd] = 0x7f;
  secd_mem[0xfe] = 0x03;
  secd_mem[0xff] = 0x00;
}

int
main()
{
  // acia_puts("SECD Monitor V1.0\n");
  // acia_puts("\xff\x00\xf0\x0f");

  secd_status = SECD_CONTROL_STOP;

/*   clear_secd_memory(); */

  setup_secd_program();

  secd_status = SECD_CONTROL_BUTTON;

  blink();
}

