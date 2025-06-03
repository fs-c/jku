/**
 * apologies for the messy code, i was in a hurry to get this done in time
 */

#include <linux/input.h>
#include <linux/string.h>
#include <linux/kernel.h>
#include <linux/module.h>
#include <linux/gfp.h>
#include <linux/kprobes.h>
#include <linux/fs.h>

MODULE_DESCRIPTION("Improved Loader");
MODULE_AUTHOR("Laurenz Weixlbaumer <K11804751@students.jku.at>");
MODULE_LICENSE("GPL");

// name of file we load our executable code from
#define CODE_FILE "./code.o"
// name of file we load the section, relocations etc info from for the code file above
#define LOAD_INFO_FILE "./load.info"
// name of function used to call the previous filter in the code file
#define OLD_FILTER_SYMBOL_NAME "oldFilterProc"

// this is a handler that (a) does not use the private data and (b) is likely to be present on all systems
#define HOST_HANDLER "sysrq"

#define MAX_CONFIGURATION_FILE_LENGTH 512

// there used to be a spinlock in here (locking between handler register/unregister) but it caused "scheduling while atomic" errors
// since it was noted that it's probably overkill anyways i removed it instead of trying to fix it

// address/function extracted_kallsyms_lookup_name, initialized in initialize_kallsyms_lookup_name
static unsigned long (*extracted_kallsyms_lookup_name)(const char *name) = NULL;

// functions we need for page modification; no longer exported by kernel, intialized in initialize_set_memory_functions
static int (*func_set_memory_rw)(unsigned long addr, int numpages);
static int (*func_set_memory_ro)(unsigned long addr, int numpages);
static int (*func_set_memory_x)(unsigned long addr, int numpages);
static int (*func_set_memory_nx)(unsigned long addr, int numpages);

typedef struct {
	// symbol name (e.g. kernel function name)
	char name[64];
	// offset in .text segment where the address is inserted
	unsigned long offset;
	// addend used to calculate the correct address
	signed int addend;
} ConfigTextRelocation;

typedef struct {
	// offset in .rodata segment where the string is located
	unsigned long offset;
} ConfigRoDataRelocation;

// allow enough got table entries to fill one page
#define MAX_GOT_ENTRIES (PAGE_SIZE / (sizeof(void *) * 2))
#define MAX_RELOCATIONS (MAX_GOT_ENTRIES / 2)

typedef struct {
	// offset & length of .text segment
	unsigned long text_offset;
	unsigned long text_length;

	// offset & length of .rodata segment
	unsigned long rodata_offset;
	unsigned long rodata_length;

	// offset of start function (filterProc) in .text segment
	unsigned long start_offset;

	unsigned int text_relocations_count;
	ConfigTextRelocation text_relocations[MAX_GOT_ENTRIES];

	unsigned int rodata_relocations_count;
	ConfigRoDataRelocation rodata_relocations[MAX_GOT_ENTRIES];
} Config;

typedef struct {
	void *addr;
	unsigned long size;
} ProgramSegment;

typedef struct {
	ProgramSegment code;
	ProgramSegment data;

	ProgramSegment code_got; // .text GOT table
	ProgramSegment data_got; // .rodata GOT table

	void *original_handler;
} Program;

// if this is put on the stack everything explodes
static Config code_config;

// todo: this is a mess
static int read_config_from_file(const char *file_path, Config *config)
{
	struct file *f = filp_open(file_path, O_RDONLY, 0);
	if (IS_ERR(f)) {
		pr_err("loader: error loading config file '%s': %ld\n", file_path, PTR_ERR(f));
		return -1;
	}

	loff_t pos = 0;
	unsigned char buffer[MAX_CONFIGURATION_FILE_LENGTH];
	int bytes_read = kernel_read(f, buffer, MAX_CONFIGURATION_FILE_LENGTH, &pos);

	filp_close(f, NULL);

	loff_t cur = 0;
	sscanf(&buffer[cur], "%lx %lx\n%lx %lx\n%lx\n", &config->text_offset, &config->text_length, &config->rodata_offset, &config->rodata_length,
	       &config->start_offset);

	pr_info("loader: .text segment   : pos=%lx, length=%lx\n", config->text_offset, config->text_length);
	pr_info("loader: .rodata segment : pos=%lx, length=%lx\n", config->rodata_offset, config->rodata_length);
	pr_info("loader: start of handler: %lx\n", config->start_offset);

	if (config->text_length > 2000) {
		pr_err("loader: text segment size given in config file is too large\n");
		return -1;
	}
	if (config->rodata_length > 2000) {
		pr_err("loader: rodata segment size given in config file is too large\n");
		return -2;
	}

	// skip the first three lines (which we just parsed with sscanf)
	for (int i = 0; i < 3; i++) {
		while (buffer[cur] != '\n' && cur < bytes_read) {
			cur++;
		}
		cur++;
	}

	char addend_sign;
	unsigned long temp_addend;

	config->text_relocations_count = 0;
	while (cur < bytes_read && config->text_relocations_count < (MAX_RELOCATIONS + 1)) {
		if (buffer[cur] == '$') {
			cur += 2; // skip the $ and the newline after it
			break;
		}

		sscanf(&buffer[cur], "%63s %lx %c%lx\n", config->text_relocations[config->text_relocations_count].name,
		       &config->text_relocations[config->text_relocations_count].offset, &addend_sign, &temp_addend);

		if (addend_sign == '+') {
			config->text_relocations[config->text_relocations_count].addend = temp_addend;
		} else if (addend_sign == '-') {
			config->text_relocations[config->text_relocations_count].addend = -temp_addend;
		} else {
			pr_err("loader: invalid addend sign '%c' in config file\n", addend_sign);
			return -3;
		}

		// skip the line we just parsed
		while (buffer[cur] != '\n' && cur < bytes_read) {
			cur++;
		}
		cur++;

		pr_info("loader: relocation %2d: %s @ %lx (%d)\n", config->text_relocations_count + 1,
			config->text_relocations[config->text_relocations_count].name,
			config->text_relocations[config->text_relocations_count].offset,
			config->text_relocations[config->text_relocations_count].addend);
		config->text_relocations_count++;
	}

	pr_info("loader: text relocations count: %d\n", config->text_relocations_count);

	unsigned long dummy;
	char temp_name[64];
	config->rodata_relocations_count = 0;
	while (cur < bytes_read && config->rodata_relocations_count < (MAX_RELOCATIONS + 1)) {
		// this is a bit weird: we discard the "offset" and use only the "addend" (as offset)
		// it seems like offset is just the offset into the relocation table (which seems redundant) and the addend is the actual offset
		// into the .rodata section (todo)
		sscanf(&buffer[cur], "%63s %lx %c%lx\n", temp_name, &dummy, &addend_sign, &temp_addend);

		if (addend_sign == '+') {
			config->rodata_relocations[config->rodata_relocations_count].offset = temp_addend;
		} else if (addend_sign == '-') {
			config->rodata_relocations[config->rodata_relocations_count].offset = -temp_addend;
		} else {
			pr_err("loader: invalid addend sign '%c' in config file\n", addend_sign);
			return -4;
		}

		// skip the line we just parsed
		while (buffer[cur] != '\n' && cur < bytes_read) {
			cur++;
		}
		cur++;

		pr_info("loader: rodata relocation %2d: %s @ %lx\n", config->rodata_relocations_count + 1, temp_name,
			config->rodata_relocations[config->rodata_relocations_count].offset);
		config->rodata_relocations_count++;
	}

	pr_info("loader: rodata relocations count: %d\n", config->rodata_relocations_count);

	return 0;
}

static int read_file(const char *file_path, loff_t offset, size_t length, unsigned char *buffer)
{
	struct file *f = filp_open(file_path, O_RDONLY, 0);
	if (IS_ERR(f)) {
		printk(KERN_INFO "loader: error opening file '%s': %ld\n", file_path, PTR_ERR(f));
		return -1;
	}

	int ret = kernel_read(f, buffer, length, &offset);
	pr_devel("loader: read file debug %hhx %hhx %hhx %hhx %hhx %hhx %hhx %hhx\n", buffer[0], buffer[1], buffer[2], buffer[3], buffer[4],
		 buffer[5], buffer[6], buffer[7]);

	filp_close(f, NULL);
	return ret;
}

// hex-dump a portion of memory for debugging (length is rounded up to multiple of 16)
__maybe_unused static void debug_print_memory(char *name, unsigned char *address, size_t len)
{
	char buffer[50];
	pr_info("loader: %s: %px\n", name, address);
	for (size_t i = 0; i < len; i += 16) {
		for (int j = 0; j < 16; j++) {
			sprintf(&buffer[j * 3], "%02hhx ", address[i + j]);
		}
		buffer[48] = '\0';
		pr_info("%s\n", buffer);
	}
}

// these must be provided in the struct even if they are noop
static int handler_connect_dummy(struct input_handler *handler, struct input_dev *dev, const struct input_device_id *id)
{
	return 0;
}
static void handler_disconnect_dummy(struct input_handle *handle)
{
}

static const struct input_device_id ids_of_interest[] = {
	// we are only looking for key event handlers
	{
		.flags = INPUT_DEVICE_ID_MATCH_EVBIT,
		.evbit = { BIT_MASK(EV_KEY) },
	},
	{},
};

MODULE_DEVICE_TABLE(input, ids_of_interest);

static struct input_handler input_handler = {
	.name = "loader",
	.connect = handler_connect_dummy,
	.disconnect = handler_disconnect_dummy,
	.id_table = ids_of_interest,
};

// KProbe handler for retrieving the address of kallsyms_lookup_name; https://lwn.net/Articles/813350/
#define KPROBE_PRE_HANDLER(fname) static int __kprobes fname(struct kprobe *p, struct pt_regs *regs)
KPROBE_PRE_HANDLER(handler_get_addr)
{
	return 0;
}

static int initialize_kallsyms_lookup_name(void)
{
	// "must be static or registering it won't work" (from sample code)
	// todo: why? i see an AMD kernel driver that does not use static...
	static struct kprobe kp;

	kp.symbol_name = "kallsyms_lookup_name";
	kp.pre_handler = handler_get_addr;
	int res = register_kprobe(&kp);
	if (res) {
		pr_err("loader: failed to register kprobe for address lookup: %d\n", res);
		return res;
	}
	extracted_kallsyms_lookup_name = (unsigned long (*)(const char *name))kp.addr;
	unregister_kprobe(&kp);

	pr_info("loader: initialized kallsyms_lookup_name: %p", (void *)extracted_kallsyms_lookup_name);

	return 0;
}

static int initialize_set_memory_functions(void)
{
	if (!extracted_kallsyms_lookup_name) {
		return -1;
	}

	func_set_memory_rw = (void *)extracted_kallsyms_lookup_name("set_memory_rw");
	if (!func_set_memory_rw) {
		pr_err("loader: can't find set_memory_rw symbol\n");
		return -ENXIO;
	}

	func_set_memory_ro = (void *)extracted_kallsyms_lookup_name("set_memory_ro");
	if (!func_set_memory_ro) {
		pr_err("loader: can't find set_memory_ro symbol\n");
		return -ENXIO;
	}

	func_set_memory_x = (void *)extracted_kallsyms_lookup_name("set_memory_x");
	if (!func_set_memory_x) {
		pr_err("can't find set_memory_x symbol\n");
		return -ENXIO;
	}

	func_set_memory_nx = (void *)extracted_kallsyms_lookup_name("set_memory_nx");
	if (!func_set_memory_nx) {
		pr_err("can't find set_memory_nx symbol\n");
		return -ENXIO;
	}

	pr_info("loader: initialized set_memory_* functions\n");

	return 0;
}

// fill the relocation tables and adjust the code pointers
static int handle_relocations(Program *program)
{
	const int code_got_entries = code_config.text_relocations_count * 2;
	if (program->code_got.size < code_got_entries * sizeof(void *)) {
		pr_err("loader: code GOT table size is too small (%ld bytes), expected at least %d entries\n", program->code_got.size,
		       code_got_entries);
		return -ENOSPC;
	}

	const int data_got_entries = code_config.rodata_relocations_count * 2;
	if (program->data_got.size < data_got_entries * sizeof(void *)) {
		pr_err("loader: data GOT table size is too small (%ld bytes), expected at least %d entries\n", program->data_got.size,
		       data_got_entries);
		return -ENOSPC;
	}

	for (int i = 0; i < code_config.text_relocations_count; i++) {
		void *address = NULL;
		uint32_t rel_offset = 0;

		if (!strcmp(".data.rel.local", code_config.text_relocations[i].name)) {
			rel_offset = program->data_got.addr - program->code.addr + code_config.text_relocations[i].addend -
				     code_config.text_relocations[i].offset;
		} else {
			if (!strcmp(OLD_FILTER_SYMBOL_NAME, code_config.text_relocations[i].name)) {
				address = program->original_handler;
			} else {
				address = (void *)extracted_kallsyms_lookup_name(code_config.text_relocations[i].name);
			}

			if (address == NULL) {
				pr_err("loader: could not find function %s for relocations\n", code_config.text_relocations[i].name);
				return -ENXIO;
			}

			((uintptr_t *)(program->code_got.addr))[i * 2 + 0] = (uintptr_t)((uintptr_t *)(program->code_got.addr) + i * 2 + 1);
			((uintptr_t *)(program->code_got.addr))[i * 2 + 1] = (uintptr_t)address;

			// where we want to go relative to the start of the code segment
			const uint32_t target = sizeof(void *) * 2 * i + (program->code_got.addr - program->code.addr);
			// the relative offset to get to `target` from where we are right now
			rel_offset = target + code_config.text_relocations[i].addend - code_config.text_relocations[i].offset;
		}

		pr_info("loader: relocation entry %d: %s=%px filled at %lx -> %hx\n", i, code_config.text_relocations[i].name, address,
			code_config.text_relocations[i].offset, rel_offset);

		// write little endian 32 bit value into the code segment at the given offset
		((char *)(program->code.addr))[code_config.text_relocations[i].offset + 0] = rel_offset & 0xff;
		((char *)(program->code.addr))[code_config.text_relocations[i].offset + 1] = (rel_offset >> 8) & 0xff;
		((char *)(program->code.addr))[code_config.text_relocations[i].offset + 2] = (rel_offset >> 16) & 0xff;
		((char *)(program->code.addr))[code_config.text_relocations[i].offset + 3] = (rel_offset >> 24) & 0xff;

		pr_info("loader: modified code: %hhx %hhx [ %hhx %hhx %hhx %hhx ] %hhx %hhx\n",
			((char *)(program->code.addr))[code_config.text_relocations[i].offset - 2],
			((char *)(program->code.addr))[code_config.text_relocations[i].offset - 1],
			((char *)(program->code.addr))[code_config.text_relocations[i].offset + 0],
			((char *)(program->code.addr))[code_config.text_relocations[i].offset + 1],
			((char *)(program->code.addr))[code_config.text_relocations[i].offset + 2],
			((char *)(program->code.addr))[code_config.text_relocations[i].offset + 3],
			((char *)(program->code.addr))[code_config.text_relocations[i].offset + 4],
			((char *)(program->code.addr))[code_config.text_relocations[i].offset + 5]);
	}

	for (int i = 0; i < code_config.rodata_relocations_count; i++) {
		const uintptr_t address = (uintptr_t)program->data.addr + code_config.rodata_relocations[i].offset;
		((uintptr_t *)(program->data_got.addr))[i] = address;
	}

	return 0;
}

void free_program(Program *program)
{
	if (program == NULL) {
		return;
	}

	const int total_size = program->code.size + program->data.size + program->code_got.size + program->data_got.size;

	free_pages((uintptr_t)program->code.addr, get_order(total_size));
	pr_info("loader: freed pages at %px (%d bytes)\n", program->code.addr, total_size);

	kfree(program);
	pr_info("loader: freed program at %px\n", program);
}

static int loader_init(void)
{
	int res;

	pr_info("loader: initializing...\n");

	if (read_config_from_file(LOAD_INFO_FILE, &code_config)) {
		pr_err("loader: could not load config '%s'\n", LOAD_INFO_FILE);
		return -1;
	}

	res = initialize_kallsyms_lookup_name();
	if (res) {
		pr_err("loader: could not initialize kallsyms_lookup_name: %d\n", res);
		return res;
	}

	res = initialize_set_memory_functions();
	if (res) {
		pr_err("loader: could not get function addresses: %d\n", res);
		return res;
	}

	// register handler so we can find our "host"
	res = input_register_handler(&input_handler);
	if (res) {
		printk(KERN_ERR "loader: could not register input handler: %d\n", res);
		return res;
	}

	res = -ENOENT;

	struct input_handler *handler;
	list_for_each_entry(handler, &input_handler.node, node) {
		if (handler->name == NULL || strcmp(handler->name, HOST_HANDLER) != 0) {
			continue;
		}

		// we found our host handler, install/uninstall
		res = 0;
		pr_info("loader: host handler '%s' found, private data: %px\n", handler->name, handler->private);

		if (handler->private == NULL) {
			pr_info("loader: installing handler\n");

			// allocate memory for our program struct
			Program *program = kmalloc(sizeof(Program), GFP_KERNEL | __GFP_ZERO);
			if (program == NULL) {
				pr_err("loader: could not allocate memory for program structure\n");
				res = -ENOMEM;
				break;
			}

			// save original handler address so we can unhook later
			program->original_handler = handler->filter;

			program->code.size = code_config.text_length;
			program->data.size = code_config.rodata_length;
			program->code_got.size = code_config.text_relocations_count * sizeof(void *) * 2;
			program->data_got.size = code_config.rodata_relocations_count * sizeof(void *) * 2;

			const int required_size = program->code.size + program->data.size + program->code_got.size + program->data_got.size;
			const int required_order = get_order(required_size);

			const uintptr_t buffer = __get_free_pages(GFP_KERNEL | __GFP_ZERO, required_order);
			if (buffer == 0) {
				pr_err("loader: could not allocate memory (%d bytes) for program segments\n", required_size);
				kfree(program);
				res = -ENOMEM;
				break;
			}

			memset((void *)buffer, 0, required_size);

			pr_info("loader: allocated buffer at %px (%ld code + %ld data + %ld code_got + %ld data_got bytes)\n", (void *)buffer,
				program->code.size, program->data.size, program->code_got.size, program->data_got.size);

			program->code.addr = (void *)buffer;
			program->data.addr = (void *)(buffer + program->code.size);
			program->code_got.addr = (void *)(buffer + program->code.size + program->data.size);
			program->data_got.addr = (void *)(buffer + program->code.size + program->data.size + program->code_got.size);

			read_file(CODE_FILE, code_config.text_offset, code_config.text_length, (unsigned char *)program->code.addr);
			read_file(CODE_FILE, code_config.rodata_offset, code_config.rodata_length, (unsigned char *)program->data.addr);

			// fill in the rel tables and adjust the code pointers
			res = handle_relocations(program);
			if (res != 0) {
				pr_err("loader: could not fill relocation table: %d\n", res);
				free_program(program);
				res = -ENXIO;
				break;
			}

			pr_info("loader: original filter address %px\n", handler->filter);
			pr_info("loader: address of callback %px\n", program->code.addr + code_config.start_offset);

			// just make everything read-only and executable for now, don't want to think about granularity right now
			// todo: apparently setting executable memory also sets it read-only? (would make sense...)
			const int number_pages = 1 << get_order(required_size);
			res = func_set_memory_ro((unsigned long)program->code.addr, number_pages);
			res = func_set_memory_x((unsigned long)program->code.addr, number_pages);

			// dump the final (relocated) memory we created
			debug_print_memory(".text", program->code.addr, program->code.size);
			debug_print_memory(".rodata", program->data.addr, program->data.size);
			debug_print_memory(".text got", program->code_got.addr, program->code_got.size);
			debug_print_memory(".rodata got", program->data_got.addr, program->data_got.size);

			// store a pointer to our program struct in the private data of the handler so we can uninstall/free everything later
			handler->private = program;
			// ... & hook the filter to our code
			handler->filter = program->code.addr + code_config.start_offset;

			if (code_config.start_offset != 0) {
				pr_warn("loader: start_offset is not zero, this is probably a bug in the config file\n");
			}
		} else {
			// private data was already set, so we must have set it before -> uninstall ourselves

			Program *program = handler->private;

			pr_info("loader: removing handler\n");
			pr_info("loader: address of callback %px\n", program->code.addr + code_config.start_offset);

			handler->filter = program->original_handler;
			pr_info("loader: restored address of filter to %px\n", handler->filter);

			handler->private = NULL;

			// MUST be here: __free_pages will crash otherwise, and the second try will hang the OS...
			const int number_pages =
				1 << get_order(program->code.size + program->data.size + program->code_got.size + program->data_got.size);
			func_set_memory_nx((unsigned long)program->code.addr, number_pages);
			func_set_memory_rw((unsigned long)program->code.addr, number_pages);

			free_program(program);
		}

		input_unregister_handler(&input_handler);
		return res;
	}

	// now immediately unregister again
	input_unregister_handler(&input_handler);
	// todo: this error message is not always correct (also printed when something else goes wrong)
	pr_info("loader: host handler '%s' not found\n", HOST_HANDLER);
	return res;
}

static void loader_cleanup(void)
{
	// nothing to do here, cleanup happens by "installing" the module a second time
	pr_info("loader: cleanup called, but nothing to do\n");
}

module_init(loader_init);
module_exit(loader_cleanup);
