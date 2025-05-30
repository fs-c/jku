#ifndef MACRO_H
#define MACRO_H

#include <linux/input.h>
#include <linux/kernel.h>
#include <linux/kobject.h>
#include <linux/ktime.h>
#include <linux/string.h>

struct macro {
    // keypress to replace, see https://elixir.bootlin.com/linux/v6.13.6/source/include/uapi/linux/input-event-codes.h#L64
    char to_replace;
    // replacement string
    char replacement[20];
};

enum timer_work_state {
    TIMER_WORK_KEYDOWN,
    TIMER_WORK_KEYUP,
};

struct timer_work_unit {
    enum timer_work_state state;
    int index;
    struct macro* macro;
    struct input_handle* handle;
};

#define ON "On"
#define OFF "Off"

#endif /* MACRO_H */
