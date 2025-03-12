/*
 * kallsyms_lookup_name undefined and finding not exported functions in the linux kernel
 *
 * zizzu 2020
 *
 * On kernels 5.7+ kallsyms_lookup_name is not exported anymore, so it is not usable in kernel modules.
 * The address of this function is visible via /proc/kallsyms
 * but since the address is randomized on reboot, hardcoding a value is not possible.
 * A kprobe replaces the first instruction of a kernel function
 * and saves cpu registers into a struct pt_regs *regs and then a handler
 * function is executed with that struct as parameter.
 * The saved value of the instruction pointer in regs->ip, is the address of probed function + 1. 
 * A kprobe on kallsyms_lookup_name can read the address in the handler function.
 * Internally register_kprobe calls kallsyms_lookup_name, which is visible for this code, so,
 * planting a second kprobe, allow us to get the address of kallsyms_lookup_name without waiting
 * and then we can call this address via a function pointer, to use kallsyms_lookup_name in our module.
 *
 * Example for x86-64
 *
 * Source: https://github.com/zizzu0/LinuxKernelModules/blob/main/FindKallsymsLookupName.c
 *
 * Adapted, documented, and extended by Michael Sonntag
 */

#include <linux/kernel.h>
#include <linux/module.h>
#include <linux/kprobes.h>

MODULE_LICENSE("GPL");


// Helper to define a handler function for kprobes
// "__kprobes" is used to move them to a special code segment (".kprobes.text")
// These will NOT be able to be kprobe'd themselves!
#define KPROBE_PRE_HANDLER(fname) static int __kprobes fname(struct kprobe *p, struct pt_regs *regs)

// The kallsyms_lookup_name as a function pointer (returns an address - unsigned long - and takes a string as parameter) - obtained via kprobe handler
static unsigned long (*kln_pointer_handler)(const char *name)=NULL;

// The kallsyms_lookup_name as a function pointer - obtained via the kprobe address
static unsigned long (*kln_pointer_addr)(const char *name)=NULL;

// Used only within a function, but must be global (EINVAL on registering the probe otherwise)
static struct kprobe kp_getAddr,kp_forceLookup;

KPROBE_PRE_HANDLER(handler_getAddr) {
	/* The saved value of the instruction pointer in regs->ip is the address of the probed function+1.
	 * So store it in our variable!
	 * -1 because the first instruction byte is replaced by a breakpoint instruction 
	 * INT3 --> Opcode 0xCC (NOT "INT 3" --> "0xCD 0x03"!)
	 */
	kln_pointer_handler=(unsigned long (*)(const char *name)) (regs->ip-1);
	// We did not change the instruction pointer; continue normally
	return 0;
}

KPROBE_PRE_HANDLER(handler_forceLookup) {
	/* The second handler is only used to force use of kallsyms_lookup_name, so the first
	 * handler is called and stores the pointer. We don't do anything here...
	 */
	return 0;
}

static int registerKProbePreHandler(struct kprobe *kp, char *symbol_name, void *handler) {
	int res;
	// Fill in probe data
	kp->symbol_name=symbol_name;
	// We solely do a pre-handler, no post-handler
	kp->pre_handler=handler;  
	// Register probe
	res=register_kprobe(kp);
	if(res) {
		return res;
	}  
	pr_debug("Planted kprobe pre-handler for \"%s\" at 0x%px\n",symbol_name,kp->addr);  
	return 0;
}

static int getKLNAddress(void) {
	int res; 
	// Register the kprobe which will - when called - store the address of the function
	res=registerKProbePreHandler(&kp_getAddr,"kallsyms_lookup_name",handler_getAddr);
	if(res) {
		pr_err("Failed to register kprobe for address lookup: %d\n",res);
		return res;
	}
	// We can also get the address directly from the kprobe data as soon as it was registered (if successful)
	kln_pointer_addr=(unsigned long (*)(const char *name))kp_getAddr.addr;
	// Call a second time - this will internally perform a call to kallsyms_lookup_name, so we trigger the first probe
	// We don't need a correct symbol - it only matters to provide something that will be looked up (but then the logic 
	// with the error handling needs to be adapted, as register_kprobe will obviously fail)!
	res=registerKProbePreHandler(&kp_forceLookup,"kallsyms_lookup_name",handler_forceLookup);
	if(res) {
		pr_err("Failed to register kprobe for forcing lookup: %d\n",res);
		// Cleanup
		unregister_kprobe(&kp_getAddr);
		return res;
	}
	// Cleanup
	unregister_kprobe(&kp_getAddr);
	unregister_kprobe(&kp_forceLookup);
	return 0;
}

static int moduleInit(void) {
	int res;
	pr_info("kallsyms_lookup_name discovery module loaded\n");

	res=getKLNAddress();
	if(res) {
		pr_err("Could not get address of kallsyms_lookup_name function: %d\n",res);
		return res;
	}

	// Print information: the address of the lookup function, the syscall table, and a non-existing symbol
	pr_info("\"kallsyms_lookup_name\" address 1 (retrieved directly from planted kProbe)         = 0x%px\n",kln_pointer_addr);
	pr_info("\"kallsyms_lookup_name\" address 2 (forcing the kProbe to be hit via second kProbe) = 0x%px\n",kln_pointer_handler);
	pr_info("\"kallsyms_lookup_name\" address 3 (via looking it up through kallsyms_lookup_name) = 0x%016lx\n",kln_pointer_handler("kallsyms_lookup_name"));
	pr_info("\"sys_call_table\" address       = 0x%016lx\n",kln_pointer_handler("sys_call_table"));
	pr_info("\"xyz_???_nosuchsymbol\" address = 0x%016lx\n",kln_pointer_handler("xyz_???_nosuchsymbol"));
  
	return 0;
}

static void moduleExit(void) {
	pr_info("kallsyms_lookup_name discovery module unloaded\n");
}

module_init(moduleInit);
module_exit(moduleExit);

