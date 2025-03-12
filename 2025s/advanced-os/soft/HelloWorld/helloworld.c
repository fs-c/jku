/*
 * helloworld.c
 * Extremely trivial kernel module doing actually nothing.
 * Only prints a (kernel debug) message on loading and unloading
 */

#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/init.h>

/* Declare this code as GPL, so we don't get a "tainted" complaint on loading. */
MODULE_LICENSE("GPL v2");
//MODULE_LICENSE("Private");

/* Provide author/contact information */
MODULE_AUTHOR("Michael Sonntag <michael.sonntag@ins.jku.at>");

/* Some information about this module */
MODULE_DESCRIPTION("Simple demonstration module");

static int __init module_initialization(void) {
	printk(KERN_INFO "Hello, world\n");
	return 0;
}

static void __exit module_finalization(void) {
	printk(KERN_INFO "So long, and thanks for all the fish!\n");
}

module_init(module_initialization);
module_exit(module_finalization);
