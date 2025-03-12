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
#include <linux/timer.h>			/* For timer */
#include <linux/tty_driver.h>		/* Not actually needed: this defines the ioctl function */

MODULE_DESCRIPTION("Example module illustrating the use of Keyboard LEDs.");
MODULE_AUTHOR("Daniele Paolo Scarpazza, Michael Sonntag");
MODULE_LICENSE("GPL v2");

/* The kernel software clock works in "jiffies", which is arbitrary/configurable between 100 and 1000 times per second.
 * HZ is the reverse, i.e. if HZ is 100 then a jiffie is 0.01 second. See man 7 time!
 * We want to blink 2 times per second, so the delay is one-fourth (half of that time the LEDs are on and half off)
 */
#define BLINK_DELAY   HZ/4
// See man 2 ioctl_console / uapi/linux/kd.h: Turn on CapsLock 0x04, NumLock 0x02 and ScrollLock 0x01 LEDs
#define ALL_LEDS_ON   0x07
// See man 2 ioctl_console / uapi/linux/kd.h: If any higher bit (0xf8) is set, the LEDs revert to the keyboard state
#define RESTORE_LEDS  0xFF

// The timer to use: We cannot do busy waiting, so we need some "scheduling"
static struct timer_list led_timer;
// The keyboard - for controlling the LEDs
static struct tty_struct *my_tty;
// Current state of the LEDs
static unsigned char kbdledstatus=RESTORE_LEDS;
// Flag to tell the callback function to NOT reschedule itself
static bool stop_timer=false;


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
static void led_timer_func(struct timer_list *ptr) {
	// Calculate new state
	if(kbdledstatus==ALL_LEDS_ON) {
		kbdledstatus=RESTORE_LEDS;
	} else {
		kbdledstatus=ALL_LEDS_ON;
	}
	// Set LED state: get the ioctl function to use, then call it with the console and the LED parameters
	(my_tty->driver->ops->ioctl) (my_tty, KDSETLED, kbdledstatus);
	// Print message whether we are within an interrupt context
	// If yes, we can't: sleep, relinquish CPU, acquire mutex, access user-space memory, take a long time...
	printk(KERN_INFO "Within interrupt: %s\n", (in_interrupt() ? "Yes" : "No"));
	// Reset timer to next event
	if(!stop_timer) {
		led_timer.expires=jiffies+BLINK_DELAY;
		add_timer(&led_timer);
	}
}

static int __init kbleds_init(void) {
	printk(KERN_INFO "kbleds: loading\n");
	/* Get the driver for the console keyboard
	 * vc_cons -> all virtual consoles; global list of consoles (console_struct.h)
	 * fg_console -> index in the list of the console keyboard (vt_kern.h); the current console
	 *            -> We will blink the console in use when the module is loaded
	 * .d -> vc_data structure inside the console (console_struct.h)
	 * port.tty -> tty port of that console
	 */
	if(!vc_cons[fg_console].d) {
		printk(KERN_ERR "kbdleds_init: Console not found\n");
		return -EFAULT;
	}
	my_tty=vc_cons[fg_console].d->port.tty;
	// Note: older examples use vc_cons[fg_console].d->vc_tty->driver
	// Kernel-internal changes made a modification necessary
	if(!my_tty || !my_tty->driver || !my_tty->driver->ops || !my_tty->driver->ops->ioctl) {
		printk(KERN_ERR "kbdleds_init: tty/driver is null\n");
		return -EFAULT;
	}

	/* Set up the LED blink timer the first time
	 * 0 = flags; we don't want anything fancy (pinned, deferrable, IRQ-safe...)
	 */
	timer_setup(&led_timer,led_timer_func,0);
	led_timer.expires=jiffies+BLINK_DELAY;
	add_timer(&led_timer);
	// Everything ok, send success
	return 0;
}

static void __exit kbleds_cleanup(void) {
	printk(KERN_INFO "kbleds_cleanup: unloading...\n");
	// Signal the function to not reschedule itself
	stop_timer=true;
	/* Prevents: timer callback is started -> timer deletion begins -> timer callback adds itself
	 * again and terminates -> del_timer_sync completes (while the callback is no longer running,
	 * but already rescheduled!) */
	// Remove timer to stop blinking
	del_timer_sync(&led_timer);
	// Reset LEDs to normal state in any case
	(my_tty->driver->ops->ioctl) (my_tty,KDSETLED,RESTORE_LEDS);
}

// Module initialization/finalization functions
module_init(kbleds_init);
module_exit(kbleds_cleanup);
