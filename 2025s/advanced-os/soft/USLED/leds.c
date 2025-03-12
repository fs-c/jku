#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/ioctl.h>
#include <linux/kd.h>

// No parameter --> use file number "0"
// Any number/kind of parameter --> use "/dev/console"
int main(int argc,char *argv[]) {
	int f;
	int res;
	(void)argv;
	printf("Blink keyboard LEDS\n\n");
	if(argc>1) {
		f=0;
		printf("Using file descriptor 0 - only works on a real console (i.e. not within an X terminal)!\n");
	} else {
		// Note: "open", not "fopen" -> we needs an integer file descriptor, not a FILE*
		// "open" is a Linux SysCall, while "fopen" is a C library call
		// "fopen" also performs a few other things (line end translation, buffering etc)
		f=open("/dev/console",O_WRONLY);
		if(!f) {
			printf("Could not open console\n");
			return -1;
		}
		printf("File descriptor: %d\n",f);
	}
	// Set all three leds to on
	res=ioctl(f,(unsigned long)KDSETLED,LED_CAP|LED_NUM|LED_SCR);
	if(res) {
		printf("Could not set LEDs: %d\n",res);
		return res;
	}
	// Wait for two seconds
	sleep(2);
	// Set all three leds to "as status"
	res=ioctl(f,(unsigned long)KDSETLED,0xff);
	if(res) {
		printf("Could not reset LEDs: %d\n",res);
		return res;
	}
	// If we opened the console, we should also close it again
	if(argc>1) {
		close(f);
	}
	return 0;
}
