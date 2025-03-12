#define _GNU_SOURCE

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <stdint.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/stat.h>

#define ERROR(msg) {int e=errno;printf(msg);printf("\nErrno=%d\n",e);exit(-1);}

const char *filename="fuse/dir/file";
const char *filename2="fuse/file2";

static void printHex(const char *title,const void* data,const size_t len);

int main(void) {
    ssize_t res;
    int f;
    uint8_t buffer[100]="ABCDEFGHIJKLMNOPQRSTUVWXYZ";

    // Note: Group and Other write permissions will NOT appear, as the umask for the parent filesystem is set to 022
    // Changing the umask for fuse to 0 is not going to change that...
    f=mknod(filename2,S_IFREG|S_IRUSR|S_IWUSR|S_IRGRP|S_IWGRP|S_IROTH|S_IWOTH,0l);
    if(f<0) {
        ERROR("Could not create file2")
    }
    res=chmod(filename2, S_IFREG|S_IRUSR|S_IWUSR|S_IRGRP|S_IWGRP|S_IROTH|S_IWOTH);
    if(res<0) {
        ERROR("Could not set mode for file2")
    }
    f=open(filename2,O_RDWR);
    if(f<0) {
        ERROR("Could not open file2 for writing")
    }
    // Should be "123456789\n1234\n"
    res=write(f,buffer,(ssize_t)5);
    if(res!=5) {
        ERROR("Could not write five new bytes")
    }
    // Should be "ABCDE6789\n1234\n"
    res=write(f,buffer,(ssize_t)10);
    if(res!=10) {
        ERROR("Could not write ten new bytes")
    }
    // Should be "ABCDEABCDEFGHIJ"
    res=write(f,buffer+5,(ssize_t)7);
    if(res!=7) {
        ERROR("Could not write seven new bytes")
    }
    // Should be "ABCDEABCDEFGHIJFGHIJKL"
    res=close(f);
    if(res!=0) {
        ERROR("Could not close file2")
    }
    res=unlink(filename2);
    if(res!=0) {
        ERROR("Could not delete file2")
    }
	// Note: Will NOT work if executed twice on the second time: We delete
	// the file at the end, but at the start we require it to exist
	// It is created (and filled) when the partition is initialized, so on 
	// the first execution is DOES exist (and has the correct content). 
	// This means it will also fail if we start with an empty partition!
    res=chmod(filename, S_IFREG|S_IRUSR|S_IWUSR|S_IRGRP|S_IWGRP|S_IROTH|S_IWOTH);
    if(res<0) {
        ERROR("Could not set mode for file")
    }
    f=open(filename,O_RDWR);
    if(f<0) {
        ERROR("Could not open file")
    }
    res=read(f,buffer,5l);
    if(res!=5) {
        ERROR("Could not read first five bytes")
    }
    res=memcmp(buffer,"12345",5l);
    if(res!=0) {
        printHex("Content",buffer,5l);
        ERROR("First five bytes differ")
    }
    res=read(f,buffer,10l);
    if(res!=10) {
        ERROR("Could not read second ten bytes")
    }
    res=memcmp(buffer,"6789\n1234\n",10l);
    if(res!=0) {
        ERROR("Second ten bytes differ")
    }
    res=read(f,buffer,1l);
    if(res!=0) {
        ERROR("Could read byte after end of file")
    }
    res=ftruncate(f,20l);    // Same block; no extension needed
    if(res!=0) {
        printf("Res %ld\n",res);
        ERROR("Could not set size to 20")
    }
    res=read(f,buffer,5l);
    if(res!=5) {
        ERROR("Could not read five new bytes")
    }
    res=memcmp(buffer,"\0\0\0\0\0",5l);
    if(res!=0) {
        ERROR("Five new bytes are not empty")
    }
    res=ftruncate(f,25l);    // One new block
    if(res!=0) {
        ERROR("Could not set size to 25")
    }
    res=read(f,buffer,5l);
    if(res!=5) {
        ERROR("Could not read five new bytes")
    }
    res=close(f);
    if(res!=0) {
        ERROR("Could not close file")
    }
    res=unlink(filename);
    if(res!=0) {
        ERROR("Could not delete file")
    }

    printf("All tests passed successfully!\n");
    return 0;
}


__attribute__((unused)) static void printHex(const char *title,const void* data,const size_t len) {
    printf("%s: ",title);
    for(size_t i=0;i<len;i++) {
        printf("%02X ",((const uint8_t*)data)[i]);
    }
    printf("\n");
}