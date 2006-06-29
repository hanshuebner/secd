
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
blink()
{
  for (;;) {
    led = 0;
    led = 1;
  }
}

int
main()
{
  const char* string = "\r\n\nHello world!\r\n";

  for (const char* p = string; *p; p++) {
    acia_putchar(*p);
  }
  
  acia_putchar(acia_getchar());
}
