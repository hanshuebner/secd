
extern volatile unsigned short acia_control;
extern volatile unsigned short acia_data;

extern volatile unsigned short led;

extern volatile unsigned short secd_status;

#define SECD_CONTROL_STOP	0x01
#define SECD_CONTROL_BUTTON	0x02

#define SECD_STATUS_STOPPED		0x01
#define SECD_STATUS_RUNMODE_MASK	0x06
#define SECD_STATUS_RUNMODE_RUNNING	0x00
#define SECD_STATUS_RUNMODE_HALTED	0x02
#define SECD_STATUS_RUNMODE_GC		0x04

extern volatile unsigned short secd_address_high;
extern volatile unsigned short secd_mem[256];

extern volatile unsigned short lcd;

#define LCD_DATA_MASK		0x0F
#define LCD_E			0x10
#define LCD_RW			0x20
#define LCD_RS			0x40
