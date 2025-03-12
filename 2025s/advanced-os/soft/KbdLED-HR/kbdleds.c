/*
 *  kbleds.c - Blink keyboard leds until the module is unloaded.
 *  Source: https://tldp.org/LDP/lkmpg/2.6/html/lkmpg.html#AEN1194
 *  Adapted by Michael Sonntag (comments; new kernel interfaces for timer, ioctl etc)
 */

#include <linux/module.h>
#include <linux/tty.h>				/* For tty_port in console_struct.h */
#include <uapi/linux/kd.h>			/* For KDSETLED */
#include <linux/console_struct.h>	/* For vc_cons */
#include <linux/vt_kern.h>			/* For fg_console */
#include <linux/hrtimer.h>			/* For high-resolution timer */
#include <linux/tty_driver.h>		/* Not actually needed: this defines the ioctl function */

MODULE_DESCRIPTION("Example module illustrating the use of Keyboard LEDs with high-resolution timers.");
MODULE_AUTHOR("Daniele Paolo Scarpazza, Michael Sonntag");
MODULE_LICENSE("GPL");

/* We want to blink 2 times per second, so the delay is one-fourth (half of that time the LEDs are on and half off)
 * of a second, but with high-resolution timers in nanoseconds.
 */
#define BLINK_DELAY   1000000000/4
// See man 2 ioctl_console / uapi/linux/kd.h: Turn on CapsLock 0x04, NumLock 0x02 and ScrollLock 0x01 LEDs
#define ALL_LEDS_ON   0x07
// See man 2 ioctl_console / uapi/linux/kd.h: If any higher bit (0xf8) is set, the LEDs revert to the keyboard state
#define RESTORE_LEDS  0xFF

// The timer to use: We cannot do busy waiting, so we need some "scheduling"
static struct hrtimer led_timer;
// The keyboard - for controlling the LEDs
static  struct tty_struct *my_tty;
// Current state of the LEDs
static unsigned char kbdledstatus=RESTORE_LEDS;


/*
 * Function led_timer_func blinks the keyboard LEDs periodically by invoking
 * command KDSETLED of ioctl() on the keyboard driver. To learn more on virtual
 * terminal ioctl operations, please see file:
 *     linux/drivers/tty/vt/vt_ioctl.c, functions vt_ioctl and vt_k_ioctl.
 * Helpful link: https://elixir.bootlin.com/linux/latest/A/ident/vt_k_ioctl
 * (but take care which version you are inspecting!)
 *
 * The argument to KDSETLED is alternatively set to 7 (thus causing the led
 * mode to be set to LED_SHOW_IOCTL; the leds will be set by the user) and
 * to 0xFF (any value above 7 switches the led mode back to LED_SHOW_FLAGS,
 * thus the LEDs reflect the actual keyboard status).  To learn more on this,
 * see the function setledstate in linux/drivers/tty/vt/keyboard.c
 */
static enum hrtimer_restart led_timer_func(struct hrtimer *ptr) {
	// Calculate new state
	if(kbdledstatus==ALL_LEDS_ON) {
		kbdledstatus=RESTORE_LEDS;
	} else {
		kbdledstatus=ALL_LEDS_ON;
	}
	// Set LED state: get the ioctl function to use, then call it with the console and the LED parameters
	(my_tty->driver->ops->ioctl) (my_tty,KDSETLED,kbdledstatus);
	// Reset timer to next event: our delay after whatever it is now
	hrtimer_forward_now(ptr,ktime_set(0,BLINK_DELAY));
	// Reschedule ourselves with new expiry time
	return HRTIMER_RESTART;
}

static int __init kbleds_init(void) {
	ktime_t delay;
	printk(KERN_INFO "kbleds-hr: loading\n");
	/* Get the driver for the console keyboard
	 * vc_cons -> all virtual consoles; global list of consoles (console_struct.h)
	 * fg_console -> index in the list of the console keyboard (vt_kern.h); the current console
	 *            -> We will blink the console in use when the module is loaded
	 * .d -> vc_data structure inside the console (console_struct.h)
	 * port.tty -> tty port of that console
	 */
	if(!vc_cons[fg_console].d) {
		printk(KERN_ERR "kbdleds-hr_init: Console not found\n");
		return -EFAULT;
	}
	my_tty=vc_cons[fg_console].d->port.tty;
	if(!my_tty|| !my_tty->driver || !my_tty->driver->ops || !my_tty->driver->ops->ioctl) {
		printk(KERN_ERR "kbdleds-hr_init: tty/driver is null\n");
		return -EFAULT;
	}

	/* Set up the LED blink timer the first time.
	 * We don't need absolute time/setting wall clock time should not disturb us
	 * We set relative timeouts: from the start that amount of time should elapse
	 */
	hrtimer_init(&led_timer,CLOCK_MONOTONIC,HRTIMER_MODE_REL);
	// Which function to call when the timer fires
	led_timer.function=led_timer_func;
	// Could also be put directly into the next function call
	delay=ktime_set(0,BLINK_DELAY);
	hrtimer_start(&led_timer,delay,HRTIMER_MODE_REL);
	return 0;
}

static void __exit kbleds_cleanup(void) {
	printk(KERN_INFO "kbleds-hr_cleanup: unloading...\n");
	/* No need for stop flag: This guarantees that the timer function has finished and the timer is canceled
	 * We don't care about the return value: whether the timer was active (=not executing the callback) or not
	 * (=executing the function)
	 */
	hrtimer_cancel(&led_timer);
	// Reset LEDs to normal state in any case
	(my_tty->driver->ops->ioctl) (my_tty,KDSETLED,RESTORE_LEDS);
}

// Module initialization/finalization functions
module_init(kbleds_init);
module_exit(kbleds_cleanup);
