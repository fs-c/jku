#include <linux/input.h>	/* We use input handlers for hooking */
#include <linux/string.h>	/* Cannot use C library... */
#include <linux/kernel.h>	/* We're doing kernel work */
#include <linux/module.h>	/* Specifically, a module */
#include <linux/gfp.h>		/* Memory management */
#include <linux/kprobes.h>	/* KProbes to get at addresses */

// Cannot easily be a "normal" program instead of a module: we don't get access to any kernel function and would have to use syscalls only...
MODULE_DESCRIPTION("TSR (un)installed via kernel module.");
MODULE_AUTHOR("Michael Sonntag <michael.sonntag@ins.jku.at>");
MODULE_LICENSE("GPL");


#define HOST_HANDLER "sysrq"	// Does not use the private data (or any of the others on my system, but this is probably present everywhere)

// Spinlock: we may not install & uninstall the old pointer simultaneously (probably a bit overkill!)
static DEFINE_SPINLOCK(filter_lock);

// Address/function kallsyms_lookup_name
static unsigned long (*kln_pointer_addr)(const char *name)=NULL;

// Functions we need for page modification; no longer exported by kernel so must be specially "retrieved"
static int (*func_set_memory_rw)(unsigned long addr, int numpages);
static int (*func_set_memory_ro)(unsigned long addr, int numpages);
static int (*func_set_memory_x)(unsigned long addr, int numpages);
static int (*func_set_memory_nx)(unsigned long addr, int numpages);


// Necessary; cannot be NULL in structure when registering
static int myConnect(struct input_handler *handler, struct input_dev *dev,const struct input_device_id *id) {
	return 0;
}

// Necessary; cannot be NULL in structure when registering
static void myDisconnect(struct input_handle *handle) {
}

// We are only looking for key event handlers
static const struct input_device_id idsOfInterest[] = {
	{
		.flags = INPUT_DEVICE_ID_MATCH_EVBIT,
		.evbit = { BIT_MASK(EV_KEY) },
	},
	{ },    /* Terminating entry */
};

MODULE_DEVICE_TABLE(input,idsOfInterest);

static struct input_handler inputHandler={
	.name		= "TSR",
	.connect	= myConnect,
	.disconnect	= myDisconnect,
	.id_table	= idsOfInterest,
};

// KProbe handler for retrieving the address of kallsyms_lookup_name; https://lwn.net/Articles/813350/
#define KPROBE_PRE_HANDLER(fname) static int __kprobes fname(struct kprobe *p, struct pt_regs *regs)
KPROBE_PRE_HANDLER(handler_getAddr) {
	return 0;
}

static int getKAllSymsLookupName(void) {
	// MUST be static or registering it won't work!
	static struct kprobe kp_getAddr;
	int res;
	// Get address of kallsyms_lookup_name
	kp_getAddr.symbol_name="kallsyms_lookup_name";
	kp_getAddr.pre_handler=handler_getAddr;
	res=register_kprobe(&kp_getAddr);
	if(res) {
		pr_err("Failed to register kprobe for address lookup: %d\n",res);
		return res;
	}
	kln_pointer_addr=(unsigned long (*)(const char *name))kp_getAddr.addr;
	unregister_kprobe(&kp_getAddr);
	return 0;
}

static int getFunctionAddresses(void) {
	if(!kln_pointer_addr) {
		return -1;
	}
	// Get the actual addresses
	func_set_memory_rw = (void *)kln_pointer_addr("set_memory_rw");
	if (!func_set_memory_rw) {
		pr_err("can't find set_memory_rw symbol\n");
		return -ENXIO;
	}
	func_set_memory_ro = (void *)kln_pointer_addr("set_memory_ro");
	if (!func_set_memory_ro) {
		pr_err("can't find set_memory_ro symbol\n");
		return -ENXIO;
	}
	func_set_memory_x = (void *)kln_pointer_addr("set_memory_x");
	if (!func_set_memory_x) {
		pr_err("can't find set_memory_x symbol\n");
		return -ENXIO;
	}
	func_set_memory_nx = (void *)kln_pointer_addr("set_memory_nx");
	if (!func_set_memory_nx) {
		pr_err("can't find set_memory_nx symbol\n");
		return -ENXIO;
	}
	return 0;
}

typedef struct program {	// 4096 bytes = one page
	// ATTENTION! Offsets are hardcoded in the machine code below too!
	char code[2000];	// chars are automatically packed
	char data[2000];
	void *ptr[12] __attribute__((packed));
} Program;

typedef struct relocationEntry {
	char *name;
	unsigned int indexOfEntry;
} RelocEntry;

// Program in machine code that we inject; note: MUST be position independent, so e.g. no relative calls
// MUST be at most 1000 bytes long (see struct program)
static char tsrCode[]={
// Preparation
0x53,								// pushq %rbx			# Save register we are using for indirect calls
0xe8,0x00,0x00,0x00,0x00,			// call +0				# Call to next instruction (relative offset 0); useless, but puts our current RIP onto the stack!
0x5b,								// popq %rbx			# Retrieve our own address and restore the stack
//0x48,0x8d,0x1d,0x00,0x00,0x00,0x00,	// leaq (%rip),%rbx		# Alternative to the two instructions before; must adjust subtraction below from 6 to 8 then too!
// Save registers
0x9c,								// pushf				# Save flags
// Calculate base address
0x48,0x83,0xeb,0x06,				// subq $6,%rbx			# Subtract length of (push+call) instructions to get at start address of program
//0x48,0x83,0xeb,0x08,				// subq $8,%rbx			# Subtract length of (push+leaq) instructions to get at start address of program
// Check if we should print the message
// Signature: static bool (*filterProc)(struct input_handle *handle, unsigned int type, unsigned int code, int value)=NULL;
// RDI = handle; we don't care about this one
0x48,0x83,0xfe,0x01,				// cmpq $1,%rsi			# Compare RSI (=type) to EV_KEY (=1) 
0x75,0x20,							// jne _end				# If not matching, skip printing; relative jump (32 bytes forward) -> no base address problem
0x48,0x83,0xfa,0x23,				// cmpq $35,%rdx		# Compare RDX (=code) to "h" (=35) 
0x75,0x1a,							// jne _end				# If not matching, skip printing
0x48,0x83,0xf9,0x00,				// cmpq $0,%rcx			# Compare RCX (=value) to key-up (=0) 
0x75,0x14,							// jne _end				# If not matching, skip printing
// Call printk with string
0x57,								// pushq %rdi			# Save register - we are overwriting it for the printk call
0x53,								// pushq %rbx			# Save our own base address (needed for retrieving handler address)
0x48,0x8d,0xbb,0xd0,0x07,0x00,0x00,	// leaq 2000(%rbx),%rdi	# Load address of string. NOTE: offset is hardcoded!
0x48,0x8d,0x9b,0xa0,0x0f,0x00,0x00,	// leaq 4000(%rbx),%rbx	# Load address of printk. NOTE: address of "relocation table" and "index" in it is hardcoded
0xff,0x13,							// call *(%rbx)			# Call printk. Must be an indirect call as we don't know where we are (-> no relative call) and could be more than 32 bits (-> absolute call)
// Restore register
0x5b,								// popq %rbx			# Restore base address
0x5f,								// popq %rdi			# Restore register we clobbered
//_end:
// Call original handler
0x48,0x8d,0x9b,0xa8,0x0f,0x00,0x00,	// leaq 4008(%rbx),%rbx	# Load address of old handler. NOTE: "index" in "relocation table" is 1
0x9d,								// popf					# Restore flags
0xff,0x13,							// call *(%rbx)			# Call old handler
// Restore everything and return (don't touch RAX: return value from old handler is our "own" return value!)
0x5b,								// popq %rbx			# Restore register we used for indirect calls
0xc3								// ret					# Return from callback
};

// The message to print
static char *message="Hello world!\n";

// Relcation table: fill in address of "_printk" at index 0
// (printk is a macro, the actual function is _printk)
static RelocEntry relocationEntries[]={{"_printk",0},{"\0",-1}};

int fillRelocationTable(Program *prg,RelocEntry relocationEntries[]) {
	int i=0;
	while(*relocationEntries[i].name && i<12) {	// We only have space for 12 entries
		void *adr=(void*)kln_pointer_addr(relocationEntries[i].name);	// Get address
		if(adr==NULL) {
			return -(i+1);	// So we can correctly error on the first name too
		};
		printk(KERN_INFO "Relocation entry %d: %s= %px at index %d\n",(i+1),relocationEntries[i].name,adr,relocationEntries[i].indexOfEntry);
		prg->ptr[relocationEntries[i].indexOfEntry]=adr;
		i++;
	}
	return 0;
}

// Module initialization
static int logger_init(void) {
	struct input_handler *h;
	int res;
	getKAllSymsLookupName();
	// Get addresses for memory protection functions; not exported anymore
	res=getFunctionAddresses();
	if(res) {
		printk(KERN_ERR "TSR: Could not get function address: %d\n",res);
		return res;
	}
	// Register handler so we can find our "host"
	res=input_register_handler(&inputHandler);
	if(res) {
		printk(KERN_ERR "TSR: Could not register input handler: %d\n",res);
		return res;
	}
	res=-ENOENT;
	list_for_each_entry(h,&inputHandler.node,node) {
		if(h->name!=NULL && !strcmp(h->name,HOST_HANDLER)) {
			Program *prg;
			res=0; // Found/Success
			spin_lock(&filter_lock);
			printk(KERN_INFO "TSR: Host handler \"%s\" found; private data: %px\n",h->name,h->private);
			if(h->private==NULL) {
				// Install
				printk(KERN_INFO "TSR: Installing handler\n");
				prg=(void*)__get_free_pages(GFP_KERNEL,0);	// 0 --> 2^0 --> 1 page
				if(prg!=NULL) {
					memset(prg,0,sizeof(Program));
					// Create memory page content
					memcpy(&prg->code,tsrCode,sizeof(tsrCode));				// Copy code into it
					memcpy((void*)&prg->data,message,strlen(message)+1);	// Copy in data
					res=fillRelocationTable(prg,relocationEntries);			// Fill in address of kernel/other libraries
					if(!res) {
						prg->ptr[1]=h->filter;		// Address of original handler; index is hardcoded here!
						// Print some info
						printk(KERN_INFO "Original filter address   : %px\n",h->filter);
						printk(KERN_INFO "Address of callback       : %px\n",prg);
						// Make memory read-only (we can still access the string!) and executable
						int res=func_set_memory_ro((unsigned long)prg, 1);	// Superfluous; making it executable sets this too
						res=func_set_memory_x((unsigned long)prg, 1);
						// Store as as the new handler; make it "findable" via the private data for removal
						h->private=prg->code;
						h->filter=(void*)prg->code;
					} else {
						printk(KERN_ERR "TSR: Could not find %d. function\n",-res);
						res=-ENXIO;
						__free_pages((void*)prg,0);
					}
				} else {
					printk(KERN_ERR "TSR: Could not allocate memory page\n");
					res=-ENOMEM;
					__free_pages((void*)prg,0);
				}
			} else {
				// Uninstall
				printk(KERN_INFO "TSR: Removing handler\n");
				prg=h->private;
				printk(KERN_INFO "Address of callback       : %px\n",prg);
				h->filter=prg->ptr[1];		// Get old handler address
				printk(KERN_INFO "Restored address of filter: %px\n",h->filter);
				h->private=NULL;
				// MUST be here: __free_pages will crash otherwise, and the second try will hang the OS...
				func_set_memory_nx((unsigned long)prg, 1);	// Must be set back to no-exec or setting as writable will fail
				func_set_memory_rw((unsigned long)prg, 1);
				__free_pages((void*)prg,0);
			}
			spin_unlock(&filter_lock);
			// No need to continue searching...
			input_unregister_handler(&inputHandler);
			return res;
		}
	}
	// Now immediately unregister again
	input_unregister_handler(&inputHandler);
	printk(KERN_INFO "TSR: Host handler \"%s\"not found\n",HOST_HANDLER);
	return res;
}

// Module cleanup
static void logger_cleanup(void) {
	// As we don't (permanently) register a handler, we don't do anything here.
	// Removing the inserted code is done by "installing" the module a second time
}

// Module initialization/finalization functions
module_init(logger_init);
// Must be there or unload fails...
module_exit(logger_cleanup);
