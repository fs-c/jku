#include <linux/input.h>	/* We use input handlers for hooking */
#include <linux/string.h>	/* Cannot use C library... */
#include <linux/kernel.h>	/* We're doing kernel work */
#include <linux/module.h>	/* Specifically, a module */
#include <linux/gfp.h>		/* Memory management */
#include <linux/kprobes.h>	/* KProbes to get at addresses */
#include <linux/fs.h>		/* File access */


// Cannot easily be a "normal" program instead of a module: we don't get access to any kernel function and would have to use syscalls only...
MODULE_DESCRIPTION("Loader: loading and relocating code in a kernel module.");
MODULE_AUTHOR("Michael Sonntag <michael.sonntag@ins.jku.at>");
MODULE_LICENSE("GPL");

// Name of file we load our executable code from
#define CODE_FILE "./code.o"
// Name of file we load the section, relocation etc info from for the code file above
#define LOAD_INFO_FILE "./load.info"
// Name of function used to call the previous filter in the code file
#define OLD_FILTER_SYMBOL_NAME "oldFilterProc"

#define HOST_HANDLER "sysrq"	// Does not use the private data (or any of the others on my system, but this is probably present everywhere)

// Spinlock: we may not install & uninstall the old pointer simultaneously (probably a bit overkill!)
static DEFINE_SPINLOCK(filter_lock);

// Address/function kallsyms_lookup_name
static unsigned long (*kln_pointer_addr)(const char *name)=NULL;

// Functions we need for page modification; no longer exported by kernel so must be specially "retrieved"
static int (*func_set_memory_rw)(unsigned long addr, int numpages);
static int (*func_set_memory_ro)(unsigned long addr, int numpages);
static int (*func_set_memory_x )(unsigned long addr, int numpages);
static int (*func_set_memory_nx)(unsigned long addr, int numpages);

typedef struct {
	unsigned long textOffset;	// Offset of .text segment
	unsigned long textLength;	// Length of .text segment
	unsigned long roOffset;		// Offset of .rodata segment
	unsigned long roLength;		// Length of .rodata segment
	unsigned long startOffset;	// Offset of function "filterProc" in .text segment
	unsigned int relCount;		// Count of relocations
	struct  {					// Relocation info
		char name[64];			// Symbol name (e.g. kernel function name)
		unsigned long offset;	// Offset in segment where to insert the address
		signed int addend;		// Addend used to calculate the correct address
	} relocation[5];			// At most 5, as our GOT table is not longer than that...
} Config;

typedef struct program {		// 4096 bytes = one page
	unsigned char code[2000];	// chars are automatically packed
	unsigned char data[2000];
	void *ptr[10] __attribute__((packed));	// 5 entries of two pointers (double indirection)
	void *origHandler;			// Original handler address
	// One void* space remains unused in the page
} Program;

// Maximum length of configuration file - needed for buffer length
#define LEN 512
static int loadConfig(Config *config) {
	loff_t pos=0;
	unsigned char buffer[LEN];
	struct file *f= filp_open(LOAD_INFO_FILE,O_RDONLY,0);
	if (IS_ERR(f)) {	
		printk(KERN_INFO "Error loading config: %ld\n",PTR_ERR(f));
		return -1;
	}
	int readCount=kernel_read(f,buffer,LEN,&pos);
    filp_close(f, NULL);
	loff_t cur=0;
	sscanf(&buffer[cur],"%lx %lx\n%lx %lx\n%lx\n",&config->textOffset,&config->textLength,&config->roOffset,&config->roLength,&config->startOffset);
	printk(KERN_INFO ".text segment   : pos=%lx, length=%lx\n",config->textOffset,config->textLength);
	printk(KERN_INFO ".rodata segment : pos=%lx, length=%lx\n",config->roOffset,config->roLength);
	printk(KERN_INFO "Start of handler: %lx\n",config->startOffset);
	// Skip these three lines
	while(buffer[cur]!='\n' && cur<readCount) cur++;
	cur++;
	while(buffer[cur]!='\n' && cur<readCount) cur++;
	cur++;
	while(buffer[cur]!='\n' && cur<readCount) cur++;
	cur++;
	if(config->textLength>2000) {
		printk(KERN_ERR "Text segment too long!\n");
		return -1;
	}
	if(config->roLength>2000) {
		printk(KERN_ERR "ROData segment too long!\n");
		return -2;
	}
	config->relCount=0;
	while(cur<readCount && config->relCount<6) {
		if(config->relCount==5) {
			printk(KERN_ERR "Too many relocations!\n");
			return -3;
		}
		// 63: 64 bytes in Config structure (+ zero-termination)
		sscanf(&buffer[cur],"%63s %lx %d\n",config->relocation[config->relCount].name,
			&config->relocation[config->relCount].offset,
			&config->relocation[config->relCount].addend);
		// Skip line
		while(buffer[cur]!='\n' && cur<readCount) cur++;
		cur++;
		printk(KERN_INFO "Relocation    %2d: %s @ %lx (%d)\n",config->relCount+1,
			config->relocation[config->relCount].name,
			config->relocation[config->relCount].offset,
			config->relocation[config->relCount].addend);
		config->relCount++;
	}
	printk(KERN_INFO "Relocation count: %d\n",config->relCount);
	return 0;
}

static int loadProgramBytes(loff_t offset,size_t length,unsigned char *buffer) {
	struct file *f=filp_open(CODE_FILE,O_RDONLY,0);
	if (IS_ERR(f)) {	
		printk(KERN_INFO "Error loading text segment: %ld\n",PTR_ERR(f));
		return -1;
	}
	int ret=kernel_read(f,buffer,length,&offset);
	//printk(KERN_INFO "%hhx %hhx %hhx %hhx %hhx %hhx %hhx %hhx\n",buffer[0],buffer[1],buffer[2],buffer[3],buffer[4],buffer[5],buffer[6],buffer[7]);
    filp_close(f,NULL);
	return ret;
}

// Hex-dumping a portion of memory for debugging
// (length is rounded up to multiple of 16)
__attribute__ ((unused)) static void dumpMemory(char *name,unsigned char *adr,size_t len) {
	char buffer[50];
	printk(KERN_INFO "%s: %px\n",name,adr);
	for(size_t i=0;i<len;i+=16) {
		for(int j=0;j<16;j++) {
			sprintf(&buffer[j*3],"%02hhx ",adr[i+j]);
		}
		buffer[48]='\0';
		printk(KERN_INFO "%s\n",buffer);
	}
}

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
	.name		= "Loader",
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

static int fillRelocationTable(Program *prg,Config codeConfig) {
	// 5 because we have 10 entry spaces in our GOT and we often require double indirection
	for(int i=0;i<codeConfig.relCount && i<5;i++) {
		void *adr=NULL;
		uint32_t relOffset;
		if(!strcmp(".data.rel.local",codeConfig.relocation[i].name)) {
			// This is our ".rodata" segment
			unsigned long offsetInData=0;
			// Technically incorrect; data segments need a second indirection:
			// The addend gives us the information where in the relocation table of the
			// rodata section the actual offset is (the value of that symbol):
			// First is -4 (actually 0; but RIP-indirection adds 4 bytes), second is +4;
			// so the first entry is at 0 (=start of rodata), the second at e.g. 0e (string 
			// starts at offset 14 in .rodata section)
			// Here we only have a single string which starts at the beginning of the 
			// .rodata section, so we hardcode it as 0 for simplicity

			adr=prg->data+offsetInData;
			// We must use single-indirection - strings are accessed differently than 
			// functions in the assembler code generated by GCC...
			prg->ptr[2*i]=adr;
			prg->ptr[2*i+1]=0;
		} else {
			if(!strcmp(OLD_FILTER_SYMBOL_NAME,codeConfig.relocation[i].name)) {
				// Old filter proc symbol name is hardcoced here for simplicity;
				// just the address is not a kernel symbol
				adr=prg->origHandler;
			} else {
				adr=(void*)kln_pointer_addr(codeConfig.relocation[i].name);	// Get address for GOT
			}
			if(adr==NULL) {
				return -(i+1);	// So we can correctly error on the first entry too
			};
			// We must use double-indirection as functions are called via the GOT, where the
			// final location for the address is stored (this allows optimizations like
			// resolving the name on the first call and then replacing the resolver function
			// with the actual address)...
			prg->ptr[2*i]=&prg->ptr[2*i+1];	// Points to next entry
			prg->ptr[2*i+1]=adr;			// Points to actual function code
		}
		// The relative offset we have to fill in: this depends not only on the address
		// in the GOT table, but also how far the location to fill in is from that table.
		// We assume (!) it to be a relocation of type R_X86_64_REX_GOTPCRELX --> G + GOT + A - P
		relOffset=sizeof(void*)*(i*2)			// G = where in the table (entry; each is two pointers long)
			+offsetof(Program,ptr)				// GOT = GOT table base address
			+codeConfig.relocation[i].addend	// A = the correction value (here -4, as the 
			-codeConfig.relocation[i].offset;	// P = where the reference is located
			// code uses RIP-indirection and the RIP already points to the next instruction)
		printk(KERN_INFO "Relocation entry %d: %s=%px filled at %lx -> %hx\n",(i+1),codeConfig.relocation[i].name,adr,codeConfig.relocation[i].offset,relOffset);
		// Little endian 32 bit value
		prg->code[codeConfig.relocation[i].offset+0]= relOffset     &0xff;
		prg->code[codeConfig.relocation[i].offset+1]=(relOffset>>8) &0xff;
		prg->code[codeConfig.relocation[i].offset+2]=(relOffset>>16)&0xff;
		prg->code[codeConfig.relocation[i].offset+3]=(relOffset>>24)&0xff;
		//printk(KERN_INFO "%hhx %hhx [ %hhx %hhx %hhx %hhx ] %hhx %hhx\n",prg->code[codeConfig.relocation[i].offset-2],prg->code[codeConfig.relocation[i].offset-1],prg->code[codeConfig.relocation[i].offset-0],prg->code[codeConfig.relocation[i].offset+1],
		//prg->code[codeConfig.relocation[i].offset+2],prg->code[codeConfig.relocation[i].offset+3],prg->code[codeConfig.relocation[i].offset+4],prg->code[codeConfig.relocation[i].offset+5]);
	}
	return 0;
}

// Module initialization
static int logger_init(void) {
	struct input_handler *h;
	Config codeConfig;
	int res;
	if(loadConfig(&codeConfig)) {
		printk(KERN_ERR "Loader: Could not load config 'load.info'\n");
		return -1;
	}
	getKAllSymsLookupName();
	// Get addresses for memory protection functions; not exported anymore
	res=getFunctionAddresses();
	if(res) {
		printk(KERN_ERR "Loader: Could not get function addresses: %d\n",res);
		return res;
	}
	// Register handler so we can find our "host"
	res=input_register_handler(&inputHandler);
	if(res) {
		printk(KERN_ERR "Loader: Could not register input handler: %d\n",res);
		return res;
	}
	res=-ENOENT;
	list_for_each_entry(h,&inputHandler.node,node) {
		if(h->name!=NULL && !strcmp(h->name,HOST_HANDLER)) {
			res=0; // Found/Success
			Program *prg;
			spin_lock(&filter_lock);
			printk(KERN_INFO "Loader: Host handler \"%s\" found; private data: %px\n",h->name,h->private);
			if(h->private==NULL) {
				// Install
				printk(KERN_INFO "Loader: Installing handler\n");
				prg=(void*)__get_free_pages(GFP_KERNEL,0);	// 0 --> 2^0 --> 1 page
				if(prg!=NULL) {
					memset(prg,0,sizeof(Program));
					// Create memory page content
					prg->origHandler=h->filter;		// Save address of original handler
					// Load code into it
					loadProgramBytes(codeConfig.textOffset,codeConfig.textLength,prg->code);
					// Load read-only data into it					
					loadProgramBytes(codeConfig.roOffset,codeConfig.roLength,prg->data);
					// Fill in address of kernel functions, old handler address, and data
					res=fillRelocationTable(prg,codeConfig);							
					if(res==0) {
						// Print some info
						printk(KERN_INFO "Original filter address   : %px\n",h->filter);
						printk(KERN_INFO "Address of callback       : %px\n",prg+codeConfig.startOffset);
						// Make memory read-only (we can still read the string!) and executable
						res=func_set_memory_ro((unsigned long)prg, 1);	// Superfluous; making it executable sets this too
						res=func_set_memory_x((unsigned long)prg, 1);
						/* Dump the final (relocated) memory we created */
						dumpMemory(".text",prg->code,codeConfig.textLength);
						dumpMemory(".rodata",prg->data,codeConfig.roLength);
						dumpMemory("GOT",(void*)prg->ptr,sizeof(((Program*)0)->ptr));
						/* */
						// Make it "findable" via the private data for removal
						h->private=prg;
						// Store as as the new handler; 
						h->filter=(void*)prg->code;
					} else {
						printk(KERN_ERR "Loader: Could not find function %s for relocation\n",
							codeConfig.relocation[-res].name);
						res=-ENXIO;
						__free_pages((void*)prg,0);
					}
				} else {
					printk(KERN_ERR "Loader: Could not allocate memory page\n");
					res=-ENOMEM;
					__free_pages((void*)prg,0);
				}
			} else {
				// Uninstall
				printk(KERN_INFO "Loader: Removing handler\n");
				prg=h->private;
				printk(KERN_INFO "Address of callback       : %px\n",prg);
				h->filter=prg->origHandler;		// Restore old handler address
				printk(KERN_INFO "Restored address of filter: %px\n",h->filter);
				h->private=NULL;	// Remove info to ourselves 
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
	printk(KERN_INFO "Loader: Host handler \"%s\"not found\n",HOST_HANDLER);
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
