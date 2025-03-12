#include <linux/module.h>
#include <linux/fs.h>
#include <linux/kd.h>

MODULE_DESCRIPTION("Example module illustrating the use of Keyboard LEDs.");
MODULE_AUTHOR("Michael Sonntag");
MODULE_LICENSE("GPL");


static int __init kbleds_init(void) {
	struct file *f;
	int res;
	printk(KERN_INFO "kmleds: loading...\n");
	// Open file using internal API
	f=filp_open("/dev/console",O_WRONLY,0);
	if(IS_ERR(f)) {
		printk(KERN_INFO "Could not open console\n");
		return -1;
	}
	// Directly get to the function pointer for ioctl
	// Use unlocked version (modern, no kernel lock)
	res=f->f_op->unlocked_ioctl(f,KDSETLED,0x7);
	// Close file (even in case of error in ioctl!)
	filp_close(f,NULL);
	if(res) {
		printk(KERN_INFO "Could not set LEDs: %d\n",res);
		return res;
	}
	return 0;
}

static void __exit kbleds_cleanup(void) {
	struct file *f;
	int res;
	printk(KERN_INFO "kmleds: unloading...\n");
	// Open file
	f=filp_open("/dev/console",O_WRONLY,0);
	if(IS_ERR(f)) {
		printk(KERN_INFO "Could not open console\n");
		return;
	}
	res=f->f_op->unlocked_ioctl(f,KDSETLED,0xff);
	// Close file (even in case of error in ioctl!)
	filp_close(f,NULL);
	if(res) {
		printk(KERN_INFO "Could not reset LEDs: %d\n",res);
		return;
	}
}

// Module initialization/finalization functions
module_init(kbleds_init);
module_exit(kbleds_cleanup);
