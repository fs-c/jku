// Function prototypes; will end up in GOT
int (*oldFilterProc)(void *handle, unsigned int type, unsigned int code, int value);
int (*_printk)(char *str);

// The message to be printed
// Take care: Relocating data implementation is VERY simple, so we can
// only have a SINGLE constant!
static char *message1 = "Hello world!\n";
static char *message2 = "Hello 2!\n";
static char *message3 = "Hello 3!\n";

static int filterProc(void *handle, unsigned int type, unsigned int code, int value) {
    // EV_KEY && key "h" && key-up --> print message

    if(type==1 && code==35 && value==0) {
        _printk(message1);
        _printk(message2);
        _printk(message3);
    }
    return oldFilterProc(handle,type,code,value); 
    return 0;
}
