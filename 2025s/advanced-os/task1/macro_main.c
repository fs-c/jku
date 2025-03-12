#include "macro.h"
#include <linux/slab.h>	
#include <linux/module.h>
#include <linux/random.h>

MODULE_DESCRIPTION("Macro replacer.");
MODULE_AUTHOR("lw");
MODULE_LICENSE("GPL");

#define DEVICE_NAME "AT Translated Set 2 keyboard" // --> Produces solely EV_ABS events (no clicks, absolute positioning)

// See https://elixir.bootlin.com/linux/v6.13.6/source/include/uapi/linux/input-event-codes.h#L64 for numbers
// The caodes are #define'd, so here we have to translate this MANUALLY!
struct macro macro_list[]={
	{35,"\x23\x12\x26\x26\x18\x39\x11\x18\x13\x26\x20"},	// h -> "hello world"; note: "H" is difficult, as it requires 
						// four "keys": Shift-Down + h-down + h-up + shift-up
	{30,"\x05"}, 	// a -> 4
	{18,"\x04"},	// e -> 3
	{23,"\x02"},	// i -> 1
	{24,"\x0b"},	// o -> 0
	{0,""}		// code 0 means end of list!
};

/* What kind of device ids this filter handles
 * input_register_device will only try to connect us to devices
 * which match this filter, i.e. provide these kinds of events.
 * Lots of filtering possible: see linux/include/linux/mod_devicetable.h
 * We are only interested in things that produce mouse events.
 */
static const struct input_device_id idsOfInterest[] = {
	{
		.flags = INPUT_DEVICE_ID_MATCH_EVBIT,
		.evbit = { BIT_MASK(EV_KEY) },	// Keypresses
	},
	{ },
};

/* Used to generate information used for hot-plugging and map files.
 * Not strictly needed here, as we don't do any of these things: manual
 * loading only. The mouse wiggler also works without.
 */
MODULE_DEVICE_TABLE(input,idsOfInterest);


// Module initialization
static int __init macro_init(void) {
	
}

// Module cleanup; we simply unregister our handler
static void __exit macro_cleanup(void) {
	...
}

// Module initialization/finalization functions
module_init(macro_init);
module_exit(macro_cleanup);

