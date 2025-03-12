/* 
 * procfs.c - Create a "file" in the /proc filesystem. root can write to it 
 * (every write will be appended as a string; memory will be reallocated 
 * every time for the exact number of bytes required), and everyone can read 
 * from it.
 * Written by Michael Sonntag
 */

#include <linux/kernel.h>	/* We're doing kernel work */
#include <linux/module.h>	/* Specifically, a module */
#include <linux/proc_fs.h>	/* Necessary because we use proc fs */
#include <linux/slab.h>		/* Necessary for kmalloc/kfree */
#include <linux/uaccess.h>	/* for copy_*_user */
// See https://www.kernel.org/doc/html/latest/timers/timers-howto.html
#include <linux/delay.h>	/* for ssleep */
#include <linux/mutex.h>	/* Mutex for synchronisation */

MODULE_DESCRIPTION("Example module illustrating the use of procfs.");
MODULE_AUTHOR("Michael Sonntag <michael.sonntag@ins.jku.at>");
MODULE_LICENSE("GPL");

#define PROC_DIR "proc_example"
#define PROC_FILENAME "linebuffer"
#define INITIAL_CONTENT "Hello world!\n"

#define USE_SYNCHRONISATION

#ifdef USE_SYNCHRONISATION
	DEFINE_MUTEX(myMutex);
	// Note: In real code this should be an interruptible lock and handle interruptions
	#define LOCK(myMutex) mutex_lock(&myMutex);
	// The next line DOES work but produces a warning, as we use LOCK in procfs_cleanup - which is a "void" function...
	// #define LOCK(myMutex) if(mutex_lock_interruptible(&myMutex)!=0) return -EINTR;
	#define UNLOCK(myMutex) mutex_unlock(&myMutex);
#else
	// Define as empty (= gets removed)
	#define LOCK(myMutex)
	#define UNLOCK(myMutex)
#endif

// REMEMBER: data marked as "static" is "this-file-only"; otherwise it would be visible kernel-wide!

// Pointer to directory entry in proc tree
static struct proc_dir_entry *procfs_dir=NULL;
// Pointer to file entry in proc tree
static struct proc_dir_entry *procfs_file=NULL;

// Pointer to buffer for data stored in proc tree
static unsigned char *buffer=NULL;

// Prototypes for the file functions we override
static ssize_t procfs_read(struct file *file, char __user *ubuf, size_t bufLen, loff_t *ppos);
static ssize_t procfs_write(struct file *file, const char __user *ubuf, size_t bufLen, loff_t *ppos);

// Which operations we support for our "file"
static struct proc_ops file_ops={
	// file operations we override
	.proc_read	= procfs_read,
	.proc_write	= procfs_write,
};


static ssize_t procfs_read(struct file *file, char __user *ubuf, size_t bufLen, loff_t *ppos) {
	// Note: We have to trust the user that bufLen bytes are available at ubuf...
	unsigned long res;
	ssize_t len,toCopy;
	kuid_t user_id;
	// We do not really need to check file, as we don't use it
	if(file==NULL || ubuf==NULL || ppos==NULL) {
		return -EFAULT;			
	}
	if(*ppos<0) {
		return -EBADFD;	// File descriptor is in bad state
	}
	user_id=current_uid();
	// E.g. additional permission checks could take place here
	LOCK(myMutex)
	// Needs to be checked AFTER locking - we access our shared buffer
	if(buffer==NULL || bufLen==0) {
		UNLOCK(myMutex)
		return 0;
	}
	len=strlen(buffer);
	if(*ppos>len) {
		UNLOCK(myMutex)
		// After end
		return -EBADFD;
	}
	if(*ppos==len) {
		// This mutex-unlock is ESSENTIAL - every single read activity (<>operation/call!) will end in here...
		UNLOCK(myMutex)
		// At/after end, we don't have anything more
		return 0;
	}
	// We do have at least something to return; the above will be called twice: reading until read returns 0 (=EOF)!
	printk(KERN_INFO "procfs_read - Reading as user id %d\n",user_id.val);	
	// Calculate how much to copy
	// Strlen=3 & ppos=2 --> 2 bytes already read/points to last character, one left
	toCopy=len-*ppos;
	if(bufLen<toCopy) {
		// More data than space -> copy only a part
		toCopy=bufLen;
	}
	// copy_to_user return value: 0 = everything copied, anything else = number of bytes NOT copied
	res=copy_to_user(ubuf,buffer+*ppos,toCopy);
	UNLOCK(myMutex)
	if(res) {
		// We could also declare it a (partial) success and update ppos only for as much as was copied...
		// But according to bufLen (we checked!) there should be enough space
		printk(KERN_ERR "procfs_read - could not copy data to userspace\n");
		return -ENOMEM;			
	}
	// Current position is toCopy bytes forward
	*ppos+=toCopy;
	// toCopy bytes were retrieved and copied into the buffer
	return toCopy;
}


static ssize_t procfs_write(struct file *file, const char __user *ubuf, size_t bufLen, loff_t *ppos) {	
	unsigned long res;
	ssize_t len,newLen;
	kuid_t user_id;
	// We would not need to check file and ppos (no insertion/overwriting), as we don't use them at all
	if(file==NULL || ubuf==NULL || ppos==NULL) {
		return -EFAULT;			
	}
	if(*ppos<0) {
		return -EBADFD;	// File descriptor is in bad state
	}
	user_id=current_uid();
	// E.g. permission checks could take place here
	// Note that the permissions on the file only allow writing by owner (=root) anyway
	LOCK(myMutex)
	// Needs to be checked AFTER locking - we access our shared buffer
	if(buffer==NULL || bufLen==0) {
		UNLOCK(myMutex)
		return 0;
	}
	printk(KERN_INFO "procfs_write - Writing as user id %d\n",user_id.val);
	// Ignore the writing position: we ALWAYS simply append
	len=strlen(buffer);
	// Additional +1 for the terminating null byte (len is not buffer-length but only string-length!)
	newLen=len+bufLen+1;
	printk(KERN_INFO "Current STRING length: %ld\n",len);
	if(newLen>len) {	// Here always the case; but if we had a larger buffer and a separate content length this is necessary
		unsigned char *newBuf=kmalloc(sizeof(*buffer)*newLen,GFP_KERNEL);
		if(newBuf==NULL) {
			UNLOCK(myMutex)
			printk(KERN_ERR "procfs_write - out of buffer memory\n");
			return -ENOMEM;
		}
		// Copy old content into new buffer
		// We can use memcpy here, as both are kernel memory
		memcpy(newBuf,buffer,len);
		// Free old buffer & replace with new
		// Do it before waiting: Double-free seems to be recognized by kernel and leads to reboot...
		kfree(buffer);		
		// Wait 5 seconds - otherwise a race condition is very difficult to achieve
		ssleep(5);	
		// Note: Reading in the meantime also produces "interesting" results (as we don't set the pointer to NULL!)
		buffer=newBuf;
	}
	// No memcpy here, as the source is user space, but the target kernel space
	res=copy_from_user(buffer+len,ubuf,bufLen);
	if(res) {	
		// Not everything was copied; we just fault here and do not handle partial copying, which should not 
		// happen anyway, as we reserved enough space above
		UNLOCK(myMutex)
		return -ENOMEM;
	}
	// Ensure correct string termination - we do not have a length counter!
	buffer[newLen-1]=0;	
	UNLOCK(myMutex)
	// Note difference: this is buffer length, so also includes the zero byte (which the string length above does not!)
	printk("New BUFFER length: %ld\n",newLen);
	return bufLen;
}

// Module initialization
// Remember: may be preempted...
static int procfs_init(void) {
	kuid_t user;
	kgid_t group;
	mutex_init(&myMutex);
	// We do not want to create this twice/interlocked
	LOCK(myMutex)
	if(procfs_dir!=NULL) {
		UNLOCK(myMutex)
		printk(KERN_ALERT "Error: Directory /proc/%s already exists\n",PROC_DIR);
		return -EEXIST;
	}	
	// Create the directory in proc tree
	procfs_dir=proc_mkdir(PROC_DIR,NULL);
	if(procfs_dir==NULL) {
		UNLOCK(myMutex)
		printk(KERN_ALERT "Error: Could not create directory /proc/%s\n",PROC_DIR);
		return -ENOENT;	// No such file or directory
	}	
	// Create file entry in proc tree
	procfs_file=proc_create(PROC_FILENAME,0644,procfs_dir,&file_ops);	
	// Did it work?
	if(procfs_file==NULL){
		// Cleanup: we did create the directory...
		proc_remove(procfs_dir);	
		procfs_dir=NULL;
		UNLOCK(myMutex)
		printk(KERN_ALERT "Error: Could not create file /proc/%s/%s\n",PROC_DIR,PROC_FILENAME);
		return -ENOENT;
	}	
	// Set owner and group information
	user.val=0;	// 0 = root
	group.val=1000;	// 1000 = in VM the group/user "osstudent"
	proc_set_user(procfs_file,user,group);
	printk(KERN_INFO "Created /proc/%s/%s\n",PROC_DIR,PROC_FILENAME);
	// Allocate memory for initial content; +1 for terminating zero-byte
	buffer=kmalloc(sizeof(*buffer)*(strlen(INITIAL_CONTENT)+1),GFP_KERNEL);
	if(buffer==NULL) {
		// Cleanup: we did create directory and file
		proc_remove(procfs_file);
		procfs_file=NULL;
		proc_remove(procfs_dir);		
		procfs_dir=NULL;
		UNLOCK(myMutex)
		printk(KERN_ERR "procfs_write - out of buffer memory\n");
		return -ENOMEM;
	}
	// Can use strcpy here, as we copy static kernel data into kernel buffer
	// Note: strcpy DOES copy the terminating zero-byte!
	strcpy(buffer,INITIAL_CONTENT);
	// Do NOT set the size of the "file" - it will work here, but we cannot update it later if the buffer gets longer...
	// Any changes to it will not be shown (we would probably have to somehow invalidate the procfs_dir to get it read again)
	// proc_set_size(procfs_file,strlen(buffer));
	UNLOCK(myMutex)
	return 0;
}

// Module cleanup
static void procfs_cleanup(void) {
	// Free buffer; only one can do this
	LOCK(myMutex)
	if(procfs_dir==NULL) {
		UNLOCK(myMutex)
		printk(KERN_ALERT "Error: Directory /proc/%s not existing\n",PROC_DIR);
		return;
	}
	// Remove proc tree entries
	remove_proc_entry(PROC_FILENAME,procfs_dir);
	procfs_file=NULL;
	remove_proc_entry(PROC_DIR,NULL);
	procfs_dir=NULL;
	// Free memory
	if(buffer!=NULL) {
		kfree(buffer);
		buffer=NULL;
	}
	UNLOCK(myMutex)
	// Success message
	printk(KERN_INFO "Removed /proc/%s/%s\n",PROC_DIR,PROC_FILENAME);
}

// Module initialization/finalization functions
module_init(procfs_init);
module_exit(procfs_cleanup);
