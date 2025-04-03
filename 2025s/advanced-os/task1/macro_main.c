#include <linux/kobject.h>
#include <linux/module.h>
#include <linux/proc_fs.h>
#include <linux/random.h>
#include <linux/slab.h>
#include <linux/sysfs.h>
#include <linux/workqueue.h>

#include "macro.h"

MODULE_DESCRIPTION("macro replacer");
MODULE_AUTHOR("K11804751");
MODULE_LICENSE("GPL");

#define DEVICE_NAME "AT Translated Set 2 keyboard"

static struct hrtimer timer;
static struct timer_work_unit timer_work_unit;

static int event_delay = 50;

static bool replacement_enabled = true;

[[maybe_unused]]
static ssize_t state_show(struct kobject* kobj, struct kobj_attribute* attr, char* buf)
{
    if (replacement_enabled) {
        return sprintf(buf, "%s", ON);
    } else {
        return sprintf(buf, "%s", OFF);
    }
}

[[maybe_unused]]
static ssize_t state_store(struct kobject* kobj, struct kobj_attribute* attr, const char* buf, size_t count)
{
    if (!strncmp(buf, ON, count)) {
        replacement_enabled = true;
    } else if (!strncmp(buf, OFF, count)) {
        replacement_enabled = false;
    } else {
        printk(KERN_ERR "macro: state_store: invalid state: '%s' (expected '%s' or '%s')\n", buf, ON, OFF);
        return -1;
    }

    return count;
}

static const struct kobj_attribute state_attribute = __ATTR(state, 0660, state_show, state_store);

static ssize_t procfs_delay_read(struct file* file, char __user* user_buf, size_t user_buf_len, loff_t* prev_pos)
{
    return sprintf(user_buf, "%d", event_delay);
}

static ssize_t procfs_delay_write(struct file* file, const char* user_buf, size_t user_buf_len, loff_t* ppos)
{
    printk(KERN_DEBUG "macro: procfs_delay_write: '%s'\n", user_buf);

    int new_delay;
    if (kstrtoint(user_buf, 10, &new_delay) < 0) {
        return -EINVAL;
    }

    printk(KERN_DEBUG "macro: procfs_delay_write: parsed to %d\n", new_delay);

    if (new_delay < 10 || new_delay > 500) {
        return -EINVAL;
    }

    event_delay = new_delay;
    return user_buf_len;
}

static const struct proc_ops procfs_delay_ops = {
    .proc_read = procfs_delay_read,
    .proc_write = procfs_delay_write,
};

static enum hrtimer_restart timer_work_callback(struct hrtimer* timer)
{
    if (timer_work_unit.macro == NULL || timer_work_unit.handle == NULL) {
        printk(KERN_ERR "macro: timer_work_callback: macro or handle is NULL (%p, %p)\n", timer_work_unit.macro, timer_work_unit.handle);
        return HRTIMER_NORESTART;
    }

    char key = timer_work_unit.macro->replacement[timer_work_unit.index];
    if (!key) {
        printk(KERN_DEBUG "macro: finished sending macro\n");
        return HRTIMER_NORESTART;
    }

    if (timer_work_unit.state == TIMER_WORK_KEYDOWN) {
        // send fake keydown
        input_report_key(timer_work_unit.handle->dev, key, 1);
        input_sync(timer_work_unit.handle->dev);
        printk(KERN_DEBUG "macro: sent fake keydown %d\n", key);

        // schedule keyup
        timer_work_unit.state = TIMER_WORK_KEYUP;
        hrtimer_forward_now(timer, ms_to_ktime(event_delay));
    } else if (timer_work_unit.state == TIMER_WORK_KEYUP) {
        // send fake keyup
        input_report_key(timer_work_unit.handle->dev, key, 0);
        input_sync(timer_work_unit.handle->dev);
        printk(KERN_DEBUG "macro: sent fake keyup %d\n", key);

        // move to next key
        timer_work_unit.index++;
        timer_work_unit.state = TIMER_WORK_KEYDOWN;
        hrtimer_forward_now(timer, ms_to_ktime(event_delay));
    }

    return HRTIMER_RESTART;
}

struct macro macro_list[] = {
    // // "hello world"
    // { 35, "\x23\x12\x26\x26\x18\x39\x11\x18\x13\x26\x20" },
    // // "a"
    // { 30, "\x05" },
    // // "e"
    // { 18, "\x04" },
    // // "i"
    // { 23, "\x02" },
    // // "o"
    // { 24, "\x0b" },
    { 8, "\x23\x12\x26\x26\x18\x39\x11\x18\x13\x26\x20" },
    // sentinel
    { 0, "" }
};

static struct macro* get_macro_for_key(unsigned int code)
{
    for (int i = 0; macro_list[i].to_replace != 0; i++) {
        if (macro_list[i].to_replace == code) {
            return &macro_list[i];
        }
    }

    return NULL;
}

static struct input_handle keyboard_handle;

static int on_connect(struct input_handler* handler, struct input_dev* dev,
    const struct input_device_id* id)
{
    printk(KERN_DEBUG "macro: got on_connect to %s (%p, %p)\n", dev->name, handler, id);

    if (strcasecmp(dev->name, DEVICE_NAME)) {
        return 0;
    }

    keyboard_handle.dev = dev;
    keyboard_handle.handler = handler;
    keyboard_handle.name = "macro";

    int res = input_register_handle(&keyboard_handle);
    if (res) {
        printk(KERN_ERR "macro: failed to register input handle: %d\n", res);
        return res;
    }

    res = input_open_device(&keyboard_handle);
    if (res) {
        printk(KERN_ERR "macro: failed to open input device: %d\n", res);
        input_unregister_handle(&keyboard_handle);
        return res;
    }

    printk(KERN_INFO "macro: connected to %s\n", dev->name);

    return 0;
}

static void on_disconnect(struct input_handle* handle)
{
    if (handle == NULL) {
        printk(KERN_ERR "macro: on_disconnect: handle is NULL\n");
        return;
    }

    printk(KERN_INFO "macro: disconnecting from %s\n", handle->dev->name);

    input_close_device(handle);
    input_unregister_handle(handle);
    handle->dev = NULL;
    handle->handler = NULL;
}

static bool on_filter(struct input_handle* handle, unsigned int type,
    unsigned int code, int value)
{
    printk(KERN_DEBUG "macro: on_filter %d %d %d\n", type, code, value);

    if (!replacement_enabled) {
        return false;
    }

    if (type != EV_KEY) {
        // todo: this happens pretty often but i don't see why, since we set the filter to only EV_KEY
        return false;
    }

    // if we are currently sending a macro, don't start a new one
    if (hrtimer_active(&timer)) {
        printk(KERN_DEBUG "macro: timer is active, skipping\n");
        return false;
    }

    struct macro* macro = get_macro_for_key(code);
    if (macro == NULL) {
        printk(KERN_DEBUG "macro: no macro found for key %d\n", code);
        return false;
    }

    printk(KERN_DEBUG "macro: found macro for key %d: '%s'\n", code, macro->replacement);

    switch (value) {
    case 0:
        // keyup, start sending the macro and swallow the event
        timer_work_unit.index = 0;
        timer_work_unit.state = TIMER_WORK_KEYDOWN;
        timer_work_unit.macro = macro;
        timer_work_unit.handle = handle;
        hrtimer_start(&timer, ms_to_ktime(0), HRTIMER_MODE_REL);
        return true;
    case 1:
        // keydown, swallow the event, we will send the macro on keyup
        return true;
    }

    return false;
}

static const struct input_device_id inputs_to_handle[] = {
    // EV_KEY = keypress, 1 on keydown, 0 on keyup
    // see https://www.kernel.org/doc/Documentation/input/event-codes.txt
    {
        .flags = INPUT_DEVICE_ID_MATCH_EVBIT,
        .evbit = { BIT_MASK(EV_KEY) },
    },
    {},
};

static struct input_handler input_handler = {
    .name = "macro-input-handler",
    .connect = on_connect,
    .disconnect = on_disconnect,
    .filter = on_filter,
    .id_table = inputs_to_handle,
};

static struct proc_dir_entry* proc_dir = NULL;
static struct kobject* state_kobj = NULL;

static int __init macro_init(void)
{
    // register handler
    int res = input_register_handler(&input_handler);
    if (res) {
        printk(KERN_ERR "macro: failed to register input handler: %d\n", res);
        return res;
    }

    // initialize work "scheduler"
    hrtimer_init(&timer, CLOCK_MONOTONIC, HRTIMER_MODE_REL);
    timer.function = timer_work_callback;

    proc_dir = proc_mkdir("macro", NULL);
    if (!proc_dir) {
        printk(KERN_ERR "macro: failed to create proc/macro directory\n");
        return -1;
    }

    if (!proc_create("delay", 0666, proc_dir, &procfs_delay_ops)) {
        remove_proc_entry("macro", NULL);
        return -1;
    }

    state_kobj = kobject_create_and_add("macro", kernel_kobj);
    if (!state_kobj) {
        printk(KERN_ERR "macro: failed to create sysfs/macro kobject\n");
        return -1;
    }

    if (sysfs_create_file(state_kobj, &state_attribute.attr)) {
        printk(KERN_ERR "macro: failed to create sysfs/macro/state file\n");
        return -1;
    }

    printk(KERN_INFO "macro: init done\n");
    return 0;
}

static void __exit macro_cleanup(void)
{
    input_unregister_handler(&input_handler);
    hrtimer_cancel(&timer);

    remove_proc_entry("delay", proc_dir);
    remove_proc_entry("macro", NULL);

    kobject_put(state_kobj);

    printk(KERN_INFO "macro: cleanup done\n");
}

module_init(macro_init);
module_exit(macro_cleanup);
