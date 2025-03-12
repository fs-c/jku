// Function prototypes; will end up in GOT
int (*oldFilterProc)(void *handle, unsigned int type, unsigned int code, int value);
int (*_printk)(char *str);

// The message to be printed
// Take care: Relocating data implementation is VERY simple, so we can
// only have a SINGLE constant!
static char *message="Hello world!\n";

static int filterProc(void *handle, unsigned int type, unsigned int code, int value) {
    // EV_KEY && key "h" && key-up --> print message
    if(type==1 && code==35 && value==0) {
        _printk(message);
    }
    return oldFilterProc(handle,type,code,value); 
return 0;
}
