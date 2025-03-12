#ifndef MACRO_H
#define MACRO_H

#include <linux/kernel.h>
#include <linux/string.h>
#include <linux/ktime.h>
#include <linux/kobject.h>
#include <linux/input.h>

struct macro {
	// The key to press for replacement
	// Take care: this is the keyboard position code, not the key printed on it!
	// E.g. 'a' is 30
	char replacer;

	// The replacement string; for simplicity a fixed-length array
	char replacement[20];
};

// Note: No '\n' at the end. You must therefore use 'echo -n "Off" > ...' instead of 'echo "Off" > /sys/kernel/macro/state'
#define ON "On"
#define OFF "Off"

#endif /* MACRO_H */
