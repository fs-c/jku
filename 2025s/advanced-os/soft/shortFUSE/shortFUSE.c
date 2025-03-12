#define FUSE_USE_VERSION 31

#define _GNU_SOURCE

#include <stdlib.h>
#include <stdbool.h>
#include <stddef.h>
#include <string.h>
#include <fcntl.h>
#include <errno.h>
#include <unistd.h>
#include <fuse.h>
// Sequence important: We need GNU basename, but the POSIX dirname (which does not exist in glibc...)
#include <string.h>
#include <libgen.h>

#include "shortFUSE.h"

// Used in sf_init
const char* PARTITION_FILE="/tmp/baseimage.dd";

// File used as our "disk"
static FILE *baseImage=NULL;

// Current end of the "disk" (=file length)
static uint64_t currentEnd=0;


// Log level
// Normal: FUSE_LOG_ERR
// Debug: FUSE_LOG_DEBUG
enum fuse_log_level lastLevelToShow=FUSE_LOG_DEBUG;

static bool checkCRC(__attribute__((unused)) const struct sf_entry *entry) {
// TODO
    return true;
}

static void calculateAndSetCRC(__attribute__((unused)) struct sf_entry *entry) {
// TODO
    return;
}

static uint64_t getCurrentPos(void) {
    return currentEnd;
}

static uint32_t sizeOfDirectoryEntry(const struct directory_entry *d) {
    return (uint32_t)sizeof(struct directory_entry)+d->child_count*(uint32_t)sizeof(uint64_t);
}

static uint32_t sizeOfEntry(const struct sf_entry *entry) {
    uint32_t res=offsetof(struct sf_entry,entry);
    if(entry->type==Directory) {
        res+=sizeOfDirectoryEntry(&entry->entry.dir);
    }
    if(entry->type==File) {
        res+=(uint32_t)sizeof(struct file_entry);
    }
    if(entry->type==Data) {
        res+=(uint32_t)sizeof(struct data_entry);
    }
    return res;
}

static struct sf_entry *createDirEntry(const char *name,const uint32_t child_count) {
    if(name==NULL || *name=='\0') {
        fuse_log(FUSE_LOG_ERR,"No filename provided to create directory entry\n");
        return NULL;
    }
    uint32_t len=(uint32_t)offsetof(struct sf_entry,entry)+(uint32_t)sizeof(struct directory_entry)+(uint32_t)sizeof(uint64_t)*child_count;
    struct sf_entry *entry=calloc(1l,(size_t)len);
    if(entry==NULL) {
        fuse_log(FUSE_LOG_EMERG,"Could not reserve memory for directory\n");
        return false;
    }
    entry->type=Directory;
    entry->entry.dir.child_count=child_count;
    entry->entry.dir.permissions=S_IRWXU;    // RWX for owner, nothing else
    entry->entry.dir.ctime=(uint32_t)time(NULL);
    entry->entry.dir.mtime=(uint32_t)time(NULL);
    strcpy(entry->entry.dir.name,name);
    return entry;
}

static struct sf_entry *createFileEntry(const char *name,const uint32_t size,__attribute__((unused)) const uint64_t previousDirEntry) {
    if(name==NULL || *name=='\0') {
        fuse_log(FUSE_LOG_ERR,"No filename provided to create file entry\n");
        return NULL;
    }
    uint32_t len=(uint32_t)offsetof(struct sf_entry,entry)+(uint32_t)sizeof(struct file_entry);
    struct sf_entry *entry=calloc(1l,(size_t)len);
    if(entry==NULL) {
        fuse_log(FUSE_LOG_EMERG,"Could not reserve memory for file\n");
        return false;
    }
    entry->type=File;
    entry->entry.file.size=size;
    entry->entry.file.permissions=S_IRUSR|S_IWUSR;   // RW for owner, nothing else
    entry->entry.file.ctime=(uint32_t)time(NULL);
    entry->entry.file.mtime=(uint32_t)time(NULL);
    strcpy(entry->entry.file.name,name);
    return entry;
}

// Attention: the block will always be BLOCKSIZE long; length only determines how much data will be copied; it will also
// ALWAYS be copied to the START of the block! The rest will be zeros (calloc being used)
static struct sf_entry *createDataEntry(const uint64_t previous_data_entry,const char *data,const uint32_t offset,const uint32_t length) {
    if((data==NULL)) {
        fuse_log(FUSE_LOG_ERR,"No filename provided to create data entry\n");
        return NULL;
    }
    if(offset%DATABLOCKSIZE!=0) {
        fuse_log(FUSE_LOG_ERR,"Offset in file must be multiple of data block size (%ld %% %ld == 0)\n",offset,DATABLOCKSIZE);
        return NULL;
    }
    if(length>DATABLOCKSIZE) {
        fuse_log(FUSE_LOG_ERR,"length cannot be longer than data block size: %ld > %ld\n",length,DATABLOCKSIZE);
        return NULL;
    }
    uint32_t len=(uint32_t)offsetof(struct sf_entry,entry)+(uint32_t)sizeof(struct data_entry);
    struct sf_entry *entry=calloc(1l,(size_t)len);
    if(entry==NULL) {
        fuse_log(FUSE_LOG_EMERG,"Could not reserve memory for data\n");
        return NULL;
    }
    entry->type=Data;
    entry->entry.data.previous_data_entry=previous_data_entry;
    entry->entry.data.offset=offset;
    memcpy(entry->entry.data.data,data,(size_t)length);
    return entry;
}

/* Returns the position of THIS entry, NOT the new end!
 * The entry will be freed by this function, so it is no longer accessible afterwards.
 * Will calculate and set the CRC immediately before writing
 */
static uint64_t appendEntry(struct sf_entry *entry) {
    uint64_t curPos=getCurrentPos();
    fseek(baseImage,(long int)curPos,SEEK_SET);
    calculateAndSetCRC(entry);
    uint32_t size=sizeOfEntry(entry);
    if(fwrite(entry,(size_t)size,1l,baseImage)!=1) {
        free(entry);
        fuse_log(FUSE_LOG_EMERG,"Could not append entry\n");
        return 0;
    }
    currentEnd+=size;
    free(entry);
    fuse_log(FUSE_LOG_DEBUG,"Appended entry at position %ld of length %ld\n",curPos,size);
    return curPos;
}

static void updateRootDirPos(const uint64_t rootDirPos) {
    fseek(baseImage,0l+offsetof(struct super_block,root_dir_offset),SEEK_SET);
    if(fwrite(&rootDirPos,sizeof(uint64_t),1l,baseImage)!=1) {
        fuse_log(FUSE_LOG_EMERG,"Could not update root dir position\n");
        return;
    }
    // TODO: Update CRC of super block
    fuse_log(FUSE_LOG_DEBUG,"Root dir position updated to %ld\n",rootDirPos);
}

static bool initalize_partition(void) {
    baseImage=fopen(PARTITION_FILE,"w+");
    if(baseImage==NULL) {
        int e=errno;
        fuse_log(FUSE_LOG_EMERG,"Could not open base image %s; errno = %d\n",PARTITION_FILE,e);
        return false;
    }
    fseek(baseImage,0l,SEEK_SET);
    // Create super block_count
    struct super_block sb;
    memset(&sb,0,sizeof(struct super_block));
    memcpy(sb.magic_number,"shrtFUSE",8l);
    sb.version=1;
    sb.root_dir_offset=0;
    if(fwrite(&sb,sizeof(struct super_block),1l,baseImage)!=1) {
        fuse_log(FUSE_LOG_EMERG,"Could not write super block\n");
		fclose(baseImage);
        return false;
    }
    // TODO: calculate CRC of superblock
    currentEnd=sizeof(struct super_block);

    // Create a partition with a subdirectory and a file for testing

    // Create data block for file
    struct sf_entry *de=createDataEntry(0l,"123456789\n",0,10);
    uint64_t dePos1=appendEntry(de);
    de=createDataEntry(dePos1,"1234\n",10,5);
    uint64_t dePos2=appendEntry(de);

    // Create test file
    struct sf_entry *fe=createFileEntry("file",10+5,0l);
    fe->entry.file.uid=0;
    fe->entry.file.gid=0;
    fe->entry.file.permissions=S_IRWXU|S_IRGRP|S_IWGRP;    // 0750
    fe->entry.file.data_entry=dePos2;
    uint64_t fePos=appendEntry(fe);

    // Create subdirectory
    struct sf_entry *sde=createDirEntry("dir",1);
    sde->entry.dir.depth=1;
    sde->entry.dir.uid=0;
    sde->entry.dir.gid=0;
    sde->entry.dir.permissions=S_IRWXU|S_IRGRP|S_IXGRP|S_IROTH|S_IXOTH;    // 0755
    sde->entry.dir.child_entries[0]=fePos;
    uint64_t sdePos=appendEntry(sde);

    // Create root directory
    struct sf_entry *rde=createDirEntry("/",1);
    rde->entry.dir.depth=0;
    rde->entry.dir.child_entries[0]=sdePos;
    uint64_t rdePos=appendEntry(rde);

/*
    // Create empty root directory for an empty filesystem
    struct sf_entry *rde=createDirEntry("/",0);
    rde->entry.dir.depth=0;
    uint64_t rdePos=appendEntry(rde);
*/
    updateRootDirPos(rdePos);
    return true;
}

static void *sf_init(__attribute__((unused)) struct fuse_conn_info *conn, __attribute__((unused)) struct fuse_config *cfg) {
    if(!initalize_partition()) {
		exit(1);
	}
    return NULL;
}

static void sf_destroy(__attribute__((unused)) void *private_data) {
    if(baseImage!=NULL) {
        if(fclose(baseImage)) {
            int e=errno;
            fuse_log(FUSE_LOG_EMERG,"Could not close base image; errno = %d\n",e);
        }
    }
    baseImage=NULL;
}

static sfType getEntryType(const uint64_t file_offset) {
    fseek(baseImage,(long int)file_offset,SEEK_SET);
    struct sf_entry e;
    // Read only the "header" - do NOT access anything else than the type!
    if(fread(&e,offsetof(struct sf_entry,type)+sizeof(((struct sf_entry*)NULL)->type),1l,baseImage)!=1) {
        fuse_log(FUSE_LOG_CRIT,"Could not read entry type at %ld\n",file_offset);
        return Unknown;
    }
    return e.type;
}

static struct sf_entry *getEntry(const uint64_t file_offset) {
    // Minimal size: general part + directory with no entries (all other entry types are of fixed length)
    uint32_t minimalSize=offsetof(struct sf_entry,entry)+offsetof(struct directory_entry,child_entries);
    unsigned char buf[minimalSize];
    fseek(baseImage,(long int)file_offset,SEEK_SET);
    if(fread(buf,(size_t)minimalSize,1l,baseImage)!=1) {
        fuse_log(FUSE_LOG_CRIT,"Could not read entry at %ld of size %ld\n",file_offset,minimalSize);
        return NULL;
    }
    struct sf_entry *res=(struct sf_entry*)buf; // ATTENTION: do NOT access "later" elements, it may be (=practically guaranteed!) incomplete!
    if(res->type==Directory) {
        uint32_t len=sizeOfEntry(res);
        res=calloc(1l,(size_t)len);
        if(res==NULL) {
            fuse_log(FUSE_LOG_EMERG,"Could not get memory for directory entry\n");
            return NULL;
        }
        // Read again, but this time the entry with all the directory content data
        fseek(baseImage,(long int)file_offset,SEEK_SET);
        if(fread(res,(size_t)len,1l,baseImage)!=1) {
            free(res);
            fuse_log(FUSE_LOG_CRIT,"Could not read directory entry content\n");
            return NULL;
        }
    } else if (res->type==File) {
        uint32_t len=sizeOfEntry(res);
        res=calloc(1l,(size_t)len);
        if(res==NULL) {
            fuse_log(FUSE_LOG_EMERG,"Could not get memory for file entry\n");
            return NULL;
        }
        // Read again, but this time the entry with all the file data
        fseek(baseImage,(long int)file_offset,SEEK_SET);
        if(fread(res,(size_t)len,1l,baseImage)!=1) {
            free(res);
            fuse_log(FUSE_LOG_CRIT,"Could not read file entry content\n");
            return NULL;
        }
    } else if (res->type==Data) {
        uint32_t len=sizeOfEntry(res);
        res=calloc(1l,(size_t)len);
        if(res==NULL) {
            fuse_log(FUSE_LOG_EMERG,"Could not get memory for data entry\n");
            return NULL;
        }
        // Read again, but this time the entry with all the content data
        fseek(baseImage,(long int)file_offset,SEEK_SET);
        if(fread(res,(size_t)len,1l,baseImage)!=1) {
            free(res);
            fuse_log(FUSE_LOG_CRIT,"Could not read data entry content\n");
            return NULL;
        }
    } else {
        fuse_log(FUSE_LOG_CRIT,"Unknown entry type %d\n",res->type);
        return NULL;
    }
    if(!checkCRC(res)) {
        fuse_log(FUSE_LOG_CRIT,"CRC error\n");
        free(res);
        return NULL;
    }
    return res;
}

/* We cannot do the same here as with getFileEntry, as the size is not known in advance
 * The caller would have to reserve "enough" memory, and then provide the size as a third
 * parameter so we could realloc if necessary. This is too much trouble here...
 */
static struct directory_entry *getDirectoryEntry(const uint64_t dir_offset) {
    if(dir_offset==0) {
        return NULL;
    }
    fseek(baseImage,(long int)dir_offset,SEEK_SET);
    struct sf_entry e;
    if(fread(&e,offsetof(struct sf_entry,entry.dir)+sizeof(struct directory_entry),1l,baseImage)!=1) {
        fuse_log(FUSE_LOG_CRIT,"Could not read directory entry\n");
        return NULL;
    }
    if(e.type!=Directory) {
        fuse_log(FUSE_LOG_CRIT,"Not a directory entry but %d\n",e.type);
        return NULL;
    }
    if(!checkCRC(&e)) {
        // TODO: The directory entry might not be completely read, but we can't check later, as then we have ONLY the directory entry anymore, minus the sf_entry data! So this might need more reworking.
        fuse_log(FUSE_LOG_CRIT,"CRC error\n");
        return NULL;
    }
    struct directory_entry *res=calloc(1l,(size_t)sizeOfDirectoryEntry(&e.entry.dir));
    if(res==NULL) {
        fuse_log(FUSE_LOG_EMERG,"Could not get memory for directory entry\n");
        return NULL;
    }
    // Read again, but this time only the entry but with all the directory content data
    fseek(baseImage,(long)(dir_offset+offsetof(struct sf_entry,entry.dir)),SEEK_SET);
    if(fread(res,(size_t)sizeOfDirectoryEntry(&e.entry.dir),1l,baseImage)!=1) {
        free(res);
        fuse_log(FUSE_LOG_CRIT,"Could not read directory entry content\n");
        return NULL;
    }
    return res;
}

static int getFileEntry(const uint64_t file_offset,struct file_entry *fileEntry) {
    if(file_offset==0) {
        return EFAULT;
    }
    if(fileEntry==NULL) {
        fuse_log(FUSE_LOG_ERR,"File entry space not provided\n");
        return EFAULT;
    }
    fseek(baseImage,(long)file_offset,SEEK_SET);
    struct sf_entry e;
    if(fread(&e,offsetof(struct sf_entry,entry.file)+sizeof(struct file_entry),1l,baseImage)!=1) {
        fuse_log(FUSE_LOG_CRIT,"Could not read file entry\n");
        return EFAULT;
    }
    if(e.type!=File) {
        fuse_log(FUSE_LOG_CRIT,"Not a file entry but %d\n",e.type);
        return ENOENT;
    }
    if(!checkCRC(&e)) {
        fuse_log(FUSE_LOG_CRIT,"CRC error\n");
        return EFAULT;
    }
    // Copy so we only have the file entry itself
    memcpy(fileEntry,&e.entry.file,sizeof(struct file_entry));
    return 0;
}

static int getDataEntry(const uint64_t data_offset,struct data_entry *dataEntry) {
    if(data_offset==0) {
        return EFAULT;
    }
    if(dataEntry==NULL) {
        fuse_log(FUSE_LOG_ERR,"Data entry space not provided\n");
        return EFAULT;
    }
    fseek(baseImage,(long)data_offset,SEEK_SET);
    struct sf_entry e;
    if(fread(&e,offsetof(struct sf_entry,entry.data)+sizeof(struct data_entry),1l,baseImage)!=1) {
        fuse_log(FUSE_LOG_CRIT,"Could not read data entry\n");
        return EFAULT;
    }
    if(e.type!=Data) {
        fuse_log(FUSE_LOG_CRIT,"Not a data entry\n");
        return ENOENT;
    }
    if(!checkCRC(&e)) {
        fuse_log(FUSE_LOG_CRIT,"CRC error\n");
        return EFAULT;
    }
    // Copy so we only have the date entry itself
    memcpy(dataEntry,&e.entry.data,sizeof(struct data_entry));
    return 0;
}

static uint64_t getRootDirPos(void) {
    fseek(baseImage,0l,SEEK_SET);
    struct super_block sb;
    if(fread(&sb,sizeof(struct super_block),1l,baseImage)!=1) {
        fuse_log(FUSE_LOG_EMERG,"Could not read super block\n");
        errno=ENODEV;
        return 0;
    }
    // TODO: Check CRC of superblock
    return sb.root_dir_offset;
}

static struct sf_entry *findRootDirEntry(void) {
    struct sf_entry *res=getEntry(getRootDirPos());
    // Check it really is the root directory entry
    if(res==NULL || res->type!=Directory || (res->entry.dir.depth!=0)) {
        if(res!=NULL) {
            free(res);
        }
        errno=ENOTDIR;
        return NULL;
    }
    return res;
}

static struct directory_entry *findRootDir(void) {
    struct directory_entry *res=getDirectoryEntry(getRootDirPos());
    // Check it really is the root directory entry
    if(res==NULL || (res->depth!=0)) {
        if(res!=NULL) {
            free(res);
        }
        errno=ENOTDIR;
        return NULL;
    }
    return res;
}

/*
 * Find the parent directory entry of given path
 * The element described by path does not have to exist yet
 * e.g. path="/a/b/c" -> entry for "/a/b"
 */
static struct directory_entry *findParentDirectoryOfPath(const char *path,uint64_t *foundAtPosition) {
    if(path==NULL) {
        fuse_log(FUSE_LOG_ERR,"Path not provided\n");
        return NULL;
    }
    if(foundAtPosition==NULL) {
        fuse_log(FUSE_LOG_ERR,"Position pointer not provided\n");
        return NULL;
    }
    char *dirc=strdup(path);
    char *dir=dirname(dirc);
    char *filec=strdup(path);
    char *file=basename(filec);
    fuse_log(FUSE_LOG_DEBUG,"Finding directory of entry %s; directory=%s file=%s\n",path,dir,file);
    // Name might be "/" (=root directory), "." or ".."
    if(!strcmp(file,"/")) { // Root dir does not have a parent
        free(dirc);
        free(filec);
        fuse_log(FUSE_LOG_DEBUG,"Root directory doesn't have a parent...\n");
        return NULL;
    }
    // Not handled. We currently have no "current directory"
    if(!strcmp(file,".") || !strcmp(file,"..")) {
        free(dirc);
        free(filec);
        fuse_log(FUSE_LOG_ERR,"'Current directory' not supported\n");
        return NULL;
    }
    struct directory_entry *curDir=findRootDir();
    if(curDir==NULL) {
        free(dirc);
        free(filec);
        fuse_log(FUSE_LOG_ERR,"Root directory not found\n");
        return NULL;
    }
    *foundAtPosition=getRootDirPos();
    dir++;  // Skip current slash
    // Extract rest: directory name + optionally a slash and more directory names
    while(*dir!='\0') {
        char cur[MAX_FILENAME_LENGTH];
        char *nextSlash=strstr(dir,"/");
        if(nextSlash==NULL) {
            // Last element
            strcpy(cur,dir);
            dir+=strlen(dir);
        } else {
            memcpy(cur,dir,(size_t)(nextSlash-dir));
            cur[nextSlash-dir]=0;
            dir=nextSlash+1;
        }
        // Find entry in current dir
        struct directory_entry *nextDir=NULL;
        for(uint32_t i=0;i<curDir->child_count && nextDir==NULL;i++) {
            struct sf_entry *e=getEntry(curDir->child_entries[i]);
            if(e->type!=Directory) {
                free(e);
                continue;
            }
            // Check name
            if(!strcmp(cur,e->entry.dir.name)) {
                fuse_log(FUSE_LOG_DEBUG,"Found %s at index %d offset %ld\n",cur,i,curDir->child_entries[i]);
                nextDir=getDirectoryEntry(curDir->child_entries[i]);
                *foundAtPosition=curDir->child_entries[i];
            }
            free(e);
        }
        free(curDir);
        curDir=nextDir;
    }
    free(dirc);
    free(filec);
    return curDir;
}

/*
 * Find the parent directory entry of entry described by path
 * The main difference to findParentDirectoryOfPath is, that
 * in this function the existence of an entry described by path
 * is checked (it must exist)
 */
static struct directory_entry *findDirectoryOfEntry(const char *path,uint64_t *foundAtPosition) {
    struct directory_entry *curDir=findParentDirectoryOfPath(path, foundAtPosition);
    if(curDir==NULL) {
        fuse_log(FUSE_LOG_ERR,"Parent directory of %s not found\n",path);
        return NULL;
    }
    char *filec=strdup(path);
    char *file=basename(filec);
    bool found=false;
    // We are now at the final level - look for directory or file of that name
    for(uint32_t i=0;i<curDir->child_count && !found;i++) {
        uint64_t childPos=curDir->child_entries[i];
        struct sf_entry *e=getEntry(childPos);
        if(e->type==Directory) {
            // Check name
            found=!strcmp(file,e->entry.dir.name);
        } else if(e->type==File) {
            // Check name
            found=!strcmp(file,e->entry.file.name);
        }
        free(e);
    }
    free(filec);
    if(!found) {
        fuse_log(FUSE_LOG_DEBUG,"Parent directory for %s not found\n",path);
        free(curDir);
        return NULL;
    }
    fuse_log(FUSE_LOG_DEBUG,"Parent directory for %s found at %ld\n",path,*foundAtPosition);
    return curDir;
}

static struct sf_entry *findEntry(const char *path,uint64_t *foundAtPosition) {
    if(path==NULL) {
        fuse_log(FUSE_LOG_ERR,"Path not provided\n");
        return NULL;
    }
    if(foundAtPosition==NULL) {
        fuse_log(FUSE_LOG_ERR,"Position pointer not provided\n");
        return NULL;
    }
    fuse_log(FUSE_LOG_DEBUG,"Finding entry for %s\n",path);
    struct sf_entry *res=NULL;
    char *filec=strdup(path);
    char *file=basename(filec);
    if(!strcmp(file,"/")) { // Root does not have a parent, so we cannot get its parent directory...
        free(filec);
        *foundAtPosition=getRootDirPos();
        res=findRootDirEntry();
        if(res==NULL) {
            fuse_log(FUSE_LOG_ERR,"Root directory not found\n");
        }
        return res;
    }
    uint64_t resPos;
    struct directory_entry *curDir=findDirectoryOfEntry(path,&resPos);
    if(curDir==NULL) {
        // this is not an error -> may occur when accessing a file that does not exist
        fuse_log(FUSE_LOG_DEBUG,"Parent directory of %s not found\n", path);
        free(filec);
        return NULL;
    }
    // We are now at the final level - look for directory or file of that name
    for(uint32_t i=0;i<curDir->child_count && res==NULL;i++) {
        resPos=curDir->child_entries[i];
        struct sf_entry *e=getEntry(resPos);
        if(e->type==Directory) {
            // Check name
            if(!strcmp(file,e->entry.dir.name)) {
                res=e;
            }
        } else if(e->type==File) {
            // Check name
            if(!strcmp(file,e->entry.file.name)) {
                res=e;
            }
        }
        if(res==NULL) {
            free(e);
        }
    }
    free(filec);
    free(curDir);
    if(res==NULL) {
        fuse_log(FUSE_LOG_ERR,"Entry %s not found\n",path);
    } else {
        *foundAtPosition=resPos;
        fuse_log(FUSE_LOG_DEBUG,"Entry %s found at %ld\n",path,resPos);
    }
    return res;
}

static struct directory_entry *findDirectoryEntry(const char *path,uint64_t *foundAtPosition) {
    if(path==NULL) {
        fuse_log(FUSE_LOG_ERR,"Path not provided\n");
        return NULL;
    }
    if(foundAtPosition==NULL) {
        fuse_log(FUSE_LOG_ERR,"Position pointer not provided\n");
        return NULL;
    }
    struct sf_entry *e=findEntry(path,foundAtPosition);
    if(e==NULL) {
        fuse_log(FUSE_LOG_DEBUG,"Directory %s not found\n",path);
        errno=ENOENT;
        return NULL;
    }
    if(e->type!=Directory) {
        fuse_log(FUSE_LOG_DEBUG,"%s is not a directory, but %d\n",path,e->type);
        free(e);
        errno=ENOTDIR;
        return NULL;
    }
    struct directory_entry *res=(calloc(1l,(size_t)sizeOfDirectoryEntry(&e->entry.dir)));
    if(res==NULL) {
        fuse_log(FUSE_LOG_EMERG,"Could not allocate directory entry");
        free(e);
        errno=EFAULT;
        return NULL;
    }
    memcpy(res,&e->entry.dir,(size_t)sizeOfDirectoryEntry(&e->entry.dir));
    free(e);
    return res;
}

static struct file_entry *findFileEntry(const char *path,uint64_t *foundAtPosition) {
    if(path==NULL) {
        fuse_log(FUSE_LOG_ERR,"Path not provided\n");
        return NULL;
    }
    if(foundAtPosition==NULL) {
        fuse_log(FUSE_LOG_ERR,"Position pointer not provided\n");
        return NULL;
    }
    struct sf_entry *e=findEntry(path,foundAtPosition);
    if(e==NULL) {
        fuse_log(FUSE_LOG_DEBUG,"File %s not found\n",path);
        errno=ENOENT;
        return NULL;
    }
    if(e->type!=File) {
        fuse_log(FUSE_LOG_DEBUG,"%s is not a file, but %d\n",path,e->type);
        free(e);
        errno=ENOENT;
        return NULL;
    }
    struct file_entry *res=(calloc(1l,sizeof(struct file_entry)));
    if(res==NULL) {
        fuse_log(FUSE_LOG_EMERG,"Could not allocate file entry");
        free(e);
        errno=EFAULT;
        return NULL;
    }
    memcpy(res,&e->entry.file,sizeof(struct file_entry));
    free(e);
    return res;
}

static int sf_readdir(const char *path, void *buf, fuse_fill_dir_t filler,
               __attribute__((unused)) off_t offset, __attribute__((unused)) struct fuse_file_info *fi, __attribute__((unused)) enum fuse_readdir_flags flags) {
    fuse_log(FUSE_LOG_DEBUG,"Reading directory %s\n",path);
    uint64_t posPtr;
    struct directory_entry *dir=findDirectoryEntry(path,&posPtr);
    if(dir==NULL) {
        fuse_log(FUSE_LOG_DEBUG,"Directory %s not found\n",path);
        return -1;
    }
    filler(buf, ".", NULL, 0l, 0);
    filler(buf, "..", NULL, 0l, 0);
    for(uint32_t i=0;i<dir->child_count;i++) {
        sfType type=getEntryType(dir->child_entries[i]);
        if(type==Directory) {   // Directory
            struct directory_entry *entry=getDirectoryEntry(dir->child_entries[i]);
            if(entry==NULL) {
                fuse_log(FUSE_LOG_ERR,"Could not read dir entry %d\n",i);
            } else {
                filler(buf, entry->name, NULL, 0l, 0);
                free(entry);
            }
        } else if(type==File) { // File
            struct file_entry file;
            int error=getFileEntry(dir->child_entries[i],&file);
            if(error) {
                fuse_log(FUSE_LOG_ERR,"Could not read file entry %d: %d\n",i,error);
            } else {
                filler(buf, file.name, NULL, 0l, 0);
            }
        }
    }
    free(dir);
    return 0;
}

static int sf_getattr(const char *path, struct stat *stbuf, __attribute__((unused)) struct fuse_file_info *fi) {
    int res=-ENOENT;
    fuse_log(FUSE_LOG_DEBUG,"getattr of file %s\n",path);
    uint64_t posPtr;
    struct sf_entry *e=findEntry(path,&posPtr);
    if(e==NULL) {
        return res;
    }
    if(e->type==Directory) {
        struct directory_entry *dir=&e->entry.dir;
        stbuf->st_mode = S_IFDIR | dir->permissions;
        stbuf->st_nlink = 1;
        stbuf->st_uid = dir->uid;
        stbuf->st_gid = dir->gid;
        stbuf->st_size = dir->child_count;
        stbuf->st_blocks = 0;   // TODO: How many sf_entries are used?!? (size+511)/512? "size" of directory???
        stbuf->st_atim.tv_sec=0;
        stbuf->st_mtim.tv_sec=dir->mtime;
        stbuf->st_ctim.tv_sec=dir->ctime;
        res=0;
    } else if(e->type==File) {
        struct file_entry *f=&e->entry.file;
        stbuf->st_mode = S_IFREG | f->permissions;
        stbuf->st_nlink = 1;
        stbuf->st_uid = f->uid;
        stbuf->st_gid = f->gid;
        stbuf->st_size = f->size;
        stbuf->st_blocks = (f->size+511)/512;
        stbuf->st_atim.tv_sec=0;
        stbuf->st_mtim.tv_sec=f->mtime;
        stbuf->st_ctim.tv_sec=f->ctime;
        res=0;
    } else {
        fuse_log(FUSE_LOG_ERR,"Unknown type: %d\n",e->type);
    }
    free(e);
    return res;
}

// Check file exists
// Check permissions: O_RDONLY, O_WRONLY, O_RDWR, O_EXEC
// Create and set file handle: We do NOT use one -> always see the newest data & keep no state
static int sf_open(const char *path, struct fuse_file_info *fi) {
    // Who is the user requesting this?
    struct fuse_context *context=fuse_get_context();
    uid_t curUid=context->uid;
    gid_t curGid=context->gid;
    fuse_log(FUSE_LOG_DEBUG,"Opening %s as uid=%d, gid=%d\n",path,curUid,curGid);
    // Get file info
    uint64_t posPtr;
    struct file_entry *f=findFileEntry(path,&posPtr);
    if(f==NULL) {
        return -ENOENT;
    }
    // Is she allowed to do this?
    if((fi->flags&O_RDONLY) || (fi->flags&O_RDWR)) {
        // Read access desired
        if(!((f->permissions&S_IROTH) || (curUid==f->uid && (f->permissions&S_IRUSR)) || (curGid==f->gid && (f->permissions&S_IRGRP)))) {
            free(f);
            return -EACCES;
        }
    }
    if((fi->flags&O_WRONLY) || (fi->flags&O_RDWR)) {
        // Write access desired
        if(!((f->permissions&S_IWOTH) || (curUid==f->uid && (f->permissions&S_IWUSR)) || (curGid==f->gid && (f->permissions&S_IWGRP)))) {
            free(f);
            return -EACCES;
        }
    }
    /* Is not defined and should not appear here: execute permission is checked when actually executing it. Here we only check if we can read/write.
    if(fi->flags&O_EXEC) {
        // Execute access desired
        if(!((f->permissions&S_IXOTH) || (curUid==f->uid && (f->permissions&S_IXUSR)) || (curGid==f->gid && (f->permissions&S_IXGRP)))) {
            return -EACCES;
        }
    }
    */
    free(f);
    return 0;
}

// Free up data structures, especially file handle: We have none, so there is nothing to do!
static int sf_release(const char *path, __attribute__((unused)) struct fuse_file_info *fi) {
    fuse_log(FUSE_LOG_DEBUG,"Closing %s\n",path);
    return 0;
}


/* Read size bytes from the given file into the buffer buf, beginning offset bytes
 * into the file. See read(2) for full details. Returns the number of bytes transferred,
 * or 0 if offset was at or beyond the end of the file. Required for any sensible filesystem.
*/
static int sf_read(const char *path, char *buf, size_t siz, off_t offs,
            __attribute__((unused)) struct fuse_file_info *fi) {
    fuse_log(FUSE_LOG_DEBUG,"Reading from %s offset %ld length %ld\n",path,offs,siz);
    if(offs<0) {
        fuse_log(FUSE_LOG_ERR,"Negatige offset\n");
        return -ENOENT;
    }
	uint32_t offset=(uint32_t)offs;
	uint32_t size=(uint32_t)siz;
    // Get file info
    uint64_t posPtr;
    struct file_entry *f=findFileEntry(path,&posPtr);
    if(f==NULL) {
        return -ENOENT;
    }
    if(offset>=f->size) {
        free(f);
        return 0;
    }
    // Limit data searched for to actual content: offset+size cannot be longer than the file length
    if(offset+size>f->size) {
        size=f->size-offset;
    }
    // Optimization possibility: we only need a single bit per block, not a whole boolean (which is often much longer)...
    bool blocksFound[(size+DATABLOCKSIZE-1)/DATABLOCKSIZE];    // Cannot initialze with "={0}": impossible for variable-sized objects!
    for(uint32_t i=0;i<(size+DATABLOCKSIZE-1)/DATABLOCKSIZE;i++) {
        blocksFound[i]=false;   // Not found yet
    }
    uint32_t firstBlockNumber=offset/DATABLOCKSIZE;
    uint32_t lastBlockNumber=(offset+size-1)/DATABLOCKSIZE;
    uint32_t blockCount=lastBlockNumber-firstBlockNumber+1;
    fuse_log(FUSE_LOG_DEBUG,"Blocks: count %ld, first %ld, last %ld\n",blockCount,firstBlockNumber,lastBlockNumber);
    uint64_t nextData=f->data_entry;
    free(f);
    do {
        struct data_entry dataEntry;
        int result=getDataEntry(nextData,&dataEntry);
        if(result) {
            fuse_log(FUSE_LOG_ERR,"Reached end of file list but still missing data...\n");
            return -result;
        }
        if(((uint32_t)offset<dataEntry.offset+DATABLOCKSIZE) && (offset+size>=dataEntry.offset)) {
            // We are at least in the area requested
            uint32_t curBlockNumber=dataEntry.offset/DATABLOCKSIZE;
            fuse_log(FUSE_LOG_DEBUG,"Found block number %ld\n",curBlockNumber);
            if(!blocksFound[curBlockNumber-firstBlockNumber]) {   // A block not yet found
                fuse_log(FUSE_LOG_DEBUG,"Block number %ld contains new data\n",curBlockNumber);
                uint32_t copyLen=DATABLOCKSIZE;
                if(curBlockNumber==lastBlockNumber && size%DATABLOCKSIZE!=0) {  // Second: full blocks would have length 0 otherwise...
                    copyLen=size%DATABLOCKSIZE;
                }
                unsigned char *copySrc=dataEntry.data;
                if(curBlockNumber==firstBlockNumber) {
                    copySrc=dataEntry.data+(offset-dataEntry.offset);
                }
                char *copyDst=buf+(curBlockNumber-firstBlockNumber)*DATABLOCKSIZE-offset%DATABLOCKSIZE;
                memcpy(copyDst,copySrc,(size_t)copyLen);
                // Mark block as completed
                blocksFound[curBlockNumber-firstBlockNumber]=true;
                blockCount--;
            }
        }
        nextData=dataEntry.previous_data_entry;
    } while(blockCount);
    return (int)size;
}

/* path parent directory currently containing the child element "previousPosition"
 * previousPosition old location of the entry to replacement
 * newPosition new location of the replacement entry
 */
static int updateDirHierarchy(const char *path, uint64_t previousPosition,uint64_t newPosition) {
    fuse_log(FUSE_LOG_DEBUG,"Updating directory hierarchy\n");
    char *dirc=strdup(path);
    char *dir=dirc;
    uint64_t parentPosition = 0;
    do {
        struct directory_entry *dirEntry=NULL;
        if(strncmp(dir,"/",2l)) {
            // not root
            dirEntry=findParentDirectoryOfPath(dir,&parentPosition);
            if(dirEntry==NULL) {
                fuse_log(FUSE_LOG_DEBUG,"Could not find parent of %s\n", dir);
                free(dirc);
                return -ENOENT;
            }
        }

        fuse_log(FUSE_LOG_DEBUG,"Currently at previous %ld, new %ld; parent %ld (%s)\n",previousPosition,newPosition,parentPosition,dir);
        if(parentPosition==0) {
            updateRootDirPos(newPosition);
            free(dirEntry);
            free(dirc);
            return 0;
        }
        int64_t index=-1;
        for(uint32_t i=0;i<dirEntry->child_count && index<0;i++) {
            if(previousPosition==dirEntry->child_entries[i]) {
                index=i;
            }
        }
        if(index<0) {
            fuse_log(FUSE_LOG_ERR,"Child %ld not found\n",previousPosition);
            free(dirc);
            free(dirEntry);
            return -EFAULT;
        }
        // Make copy of dirEntry
        struct sf_entry *replacement=createDirEntry(dirEntry->name,dirEntry->child_count);
        memcpy(&replacement->entry.dir,dirEntry,(size_t)sizeOfDirectoryEntry(dirEntry));
        replacement->entry.dir.mtime=(uint32_t)time(NULL);    // Update modification time
        previousPosition=parentPosition;
        free(dirEntry);

        parentPosition=0;
        if(replacement->entry.dir.depth>0) {
            struct directory_entry *de=findDirectoryOfEntry(dirname(dir),&parentPosition);
            if(de==NULL) {
                free(dirc);
                free(replacement);
                fuse_log(FUSE_LOG_DEBUG,"Parent directory entry not found\n");
                return -ENOENT;
            }
            replacement->entry.dir.depth=de->depth+1;
            free(de);
        }

        // Replace target at index
        replacement->entry.dir.child_entries[index]=newPosition;
        // Append and set variables for next loop of ascent
        newPosition=appendEntry(replacement);
    } while(parentPosition!=0);
    free(dirc);
    // Store location of new root dir
    updateRootDirPos(newPosition);
    return 0;
}


// Note: enlarging --> filled with null bytes '\0'
// If the size changed, ctime and mtime change too
// Unless FUSE_CAP_HANDLE_KILLPRIV is disabled, this method is expected to reset the setuid and setgid bits.
static int sf_truncate(const char *path, off_t siz, __attribute__((unused)) struct fuse_file_info *fi) {
    uint64_t previousPosition;
    fuse_log(FUSE_LOG_DEBUG,"Truncating file %s to length %ld\n",path,siz);
    if(siz<0) {
        fuse_log(FUSE_LOG_ERR,"Negative file length\n");
        return -ENOENT;
    }
	uint32_t size=(uint32_t)siz;
    struct file_entry *f=findFileEntry(path,&previousPosition);
    if(f==NULL) {
        fuse_log(FUSE_LOG_DEBUG,"File entry not found\n");
        return -ENOENT;
    }
    if(f->size!=size) {
        fuse_log(FUSE_LOG_DEBUG,"Changing size from %ld to %ld\n",f->size,size);
        // Have to adapt
        uint64_t dataEntry=f->data_entry;
        if(size>f->size) {
            // If size is not multiple of block size, the last block is not full; but we always fill them up with zeros on creation, so nothing to do there
            // Create empty data blocks (full + "partially" full last one if necessary);
            uint32_t curMax=f->size;
            if(curMax%DATABLOCKSIZE!=0) {
                curMax+=DATABLOCKSIZE-f->size%DATABLOCKSIZE;
            }
            uint32_t additionalBlocks=(size-curMax+DATABLOCKSIZE-1)/DATABLOCKSIZE;
            fuse_log(FUSE_LOG_DEBUG,"Adding %ld empty blocks\n",additionalBlocks);
            // Create an empty data area
            char data[DATABLOCKSIZE]={0};   // Must be initialized to be guaranteed to be empty
            for(uint32_t i=0;i<additionalBlocks;i++) {
                struct sf_entry *de=createDataEntry(dataEntry,data,curMax,DATABLOCKSIZE);
                dataEntry=appendEntry(de);
                curMax+=DATABLOCKSIZE;
            }
        } // If shortening, we do nothing to the data blocks; log-structured!
        // Create new file entry (and directory entries up to and including the root directory)
        struct sf_entry *e=createFileEntry(f->name,size,previousPosition);
        e->entry.file.uid=f->uid;
        e->entry.file.gid=f->gid;
        e->entry.file.permissions=f->permissions & (~(uint32_t)S_ISUID | ~(uint32_t)S_ISGID);
        e->entry.file.ctime=(uint32_t)time(NULL);   // Set to now
        e->entry.file.mtime=(uint32_t)time(NULL);   // Set to now
        e->entry.file.size=size;  // Set new size
        e->entry.file.data_entry=dataEntry;
        uint64_t newPosition=appendEntry(e);
        updateDirHierarchy(path,previousPosition,newPosition);
    }
    free(f);
    return 0;
}

/* Delete a file: Find the parent directory and remove the child entry.
 * Nothing else to be done on a log-structured file system.
 * Does NOT allow deleting directories -> rmdir!
 */
static int sf_unlink(const char *path) {
    uint64_t filePosition;
    fuse_log(FUSE_LOG_DEBUG,"Unlinking %s\n",path);
    struct file_entry *fe=findFileEntry(path,&filePosition);
    if(fe==NULL) {
        fuse_log(FUSE_LOG_DEBUG,"File entry not found\n");
        return -ENOENT;
    }
    free(fe);
    uint64_t dirPos;
    struct directory_entry *de=findDirectoryOfEntry(path,&dirPos);
    if(de==NULL) {
        fuse_log(FUSE_LOG_DEBUG,"Parent directory entry not found\n");
        return -ENOENT;
    }
    int64_t index=-1;
    for(uint32_t i=0;i<de->child_count && index<0;i++) {
        if(de->child_entries[i]==filePosition) {
            index=i;
        }
    }
    if(index<0) {
        free(de);
        fuse_log(FUSE_LOG_DEBUG,"Position in parent directory not found\n");
        return -EFAULT;
    }
    struct sf_entry *replacement=createDirEntry(de->name,de->child_count-1);
    // Copy everything, then remove that one child and copy rest forward
    memcpy(&replacement->entry.dir,de,(size_t)sizeOfDirectoryEntry(&replacement->entry.dir));
    replacement->entry.dir.child_count--;
    replacement->entry.dir.mtime=(uint32_t)time(NULL);
    for(uint32_t i=(uint32_t)index;i<de->child_count-1;i++) {
        replacement->entry.dir.child_entries[i]=de->child_entries[i+1];
    }
    free(de);
    uint64_t newPosition=appendEntry(replacement);
    char *dirc=strdup(path);
    char *dir=dirname(dirc);
    int res=updateDirHierarchy(dir,dirPos,newPosition);
    free(dirc);
    return res;
}

/* Delete a directory: Find the parent directory and remove the child entry.
 * Will fail if not empty!
 * Nothing else to be done on a log-structured file system.
 * Does NOT allow deleting files -> unlink!
 */
static int sf_rmdir(const char *path) {
    uint64_t dirPosition;
    fuse_log(FUSE_LOG_DEBUG,"Deleting directory %s\n",path);
    struct directory_entry *de=findDirectoryEntry(path,&dirPosition);
    if(de==NULL) {
        fuse_log(FUSE_LOG_DEBUG,"Directory not found\n");
        return -ENOENT;
    }
    if(de->child_count>0) {
        fuse_log(FUSE_LOG_DEBUG,"Directory not empty\n");
        free(de);
        return -ENOTEMPTY;
    }
    if(de->depth==0) {   // We should delete the root dir -> not allowed!
        fuse_log(FUSE_LOG_ERR,"Cannot delete root directory\n");
        free(de);
        return -EBUSY;
    }
    free(de);
    uint64_t parentDirPos;
    struct directory_entry *pde=findDirectoryOfEntry(path,&parentDirPos);
    if(pde==NULL) {
        fuse_log(FUSE_LOG_DEBUG,"Parent directory not found\n");
        return -EFAULT;
    }
    int64_t index=-1;
    for(uint32_t i=0;i<pde->child_count && index<0;i++) {
        if(pde->child_entries[i]==dirPosition) {
            index=i;
        }
    }
    if(index<0) {
        free(pde);
        fuse_log(FUSE_LOG_ERR,"Index in parent directory not found\n");
        return -EFAULT;
    }
    struct sf_entry *replacement=createDirEntry(pde->name,pde->child_count-1);
    // Copy until child_count
    memcpy(&replacement->entry.dir,pde,(size_t)sizeOfDirectoryEntry(&replacement->entry.dir));
    replacement->entry.dir.child_count--;
    replacement->entry.dir.mtime=(uint32_t)time(NULL);
    for(uint32_t i=(uint32_t)index;i<pde->child_count-1;i++) {
        replacement->entry.dir.child_entries[i]=pde->child_entries[i+1];
    }
    free(pde);
    char *dirc=strdup(path);
    char *parentPath=dirname(dirc);
    uint64_t newPosition=appendEntry(replacement);
    int res=updateDirHierarchy(parentPath,parentDirPos,newPosition);
    free(dirc);
    return res;
}

static int sf_mkdir(const char *path, mode_t mode) {
    fuse_log(FUSE_LOG_DEBUG,"Creating directory %s with mode %0o\n",path,mode);
    uint64_t parentPosition;
    struct directory_entry *parentDir=findParentDirectoryOfPath(path,&parentPosition);
    if(parentDir==NULL) {
        fuse_log(FUSE_LOG_DEBUG,"Parent directory of %s not found\n",path);
        return -ENOENT;
    }
    char *filec=strdup(path);
    char *file=basename(filec);
    // Check it does not exists (either as file or subdirectory!)
    bool found=false;
    for(uint32_t i=0;i<parentDir->child_count;i++) {
        sfType type=getEntryType(parentDir->child_entries[i]);
        if(type==Directory) {   // Directory
            struct directory_entry *entry=getDirectoryEntry(parentDir->child_entries[i]);
            if(entry==NULL) {
                fuse_log(FUSE_LOG_ERR,"Could not read dir entry %d\n",i);
            } else {
                found=!strcmp(file,entry->name);
            }
            free(entry);
        } else if(type==File) { // File
            struct file_entry fe;
            int error=getFileEntry(parentDir->child_entries[i],&fe);
            if(error) {
                fuse_log(FUSE_LOG_ERR,"Could not read file entry %d: %d\n",i,error);
            } else {
                found=!strcmp(file,fe.name);
            }
        }
    }
    if(found) {
        fuse_log(FUSE_LOG_DEBUG,"Directory %s already exists\n",file);
        free(parentDir);
        free(filec);
        return -EEXIST;
    }
    struct sf_entry *e=createDirEntry(file,0);
    free(filec);
    e->entry.dir.depth=parentDir->depth+1;
    // No data available for uid and gid, so default values only!
    e->entry.dir.uid=0;
    e->entry.dir.gid=0;
    e->entry.dir.permissions=mode;
    uint64_t newPosition=appendEntry(e);
    // Add to parent directory
    struct sf_entry *newParent=createDirEntry(parentDir->name,parentDir->child_count+1);
    memcpy(&newParent->entry.dir,parentDir,(size_t)sizeOfDirectoryEntry(parentDir));
    free(parentDir);
    // Add at end
    newParent->entry.dir.child_entries[newParent->entry.dir.child_count]=newPosition;   // Current count is last/new index
    newParent->entry.dir.child_count++; // Has been overwritten with memcpy!
    newParent->entry.dir.mtime=(uint32_t)time(NULL);
    char *dirc=strdup(path);
    char *parentPath=dirname(dirc);
    newPosition=appendEntry(newParent);
    int res=updateDirHierarchy(parentPath,parentPosition,newPosition);
    free(dirc);
    return res;
}

// Create and open a file (creation only - we don't do anything on opening anyway!)
int sf_create(const char *path, mode_t mode, __attribute__((unused)) struct fuse_file_info *fi) {
    fuse_log(FUSE_LOG_DEBUG,"Creating file %s with mode %0o\n",path,mode);
    if((mode&S_IFMT)!=S_IFREG) {    // See inode(7)
        // We only have regular files; no character/block devices, FIFOs or sockets or directories
        fuse_log(FUSE_LOG_DEBUG,"Not a regular file\n");
        return -EINVAL;
    }
    uint64_t parentPosition;
    struct directory_entry *parentDir=findParentDirectoryOfPath(path,&parentPosition);
    if(parentDir==NULL) {
        fuse_log(FUSE_LOG_DEBUG,"Parent directory of %s not found\n",path);
        return -ENOENT;
    }
    char *filec=strdup(path);
    char *file=basename(filec);
    // Check it does not exists (either as file or subdirectory!)
    bool found=false;
    for(uint32_t i=0;i<parentDir->child_count;i++) {
        sfType type=getEntryType(parentDir->child_entries[i]);
        if(type==Directory) {   // Directory
            struct directory_entry *entry=getDirectoryEntry(parentDir->child_entries[i]);
            if(entry==NULL) {
                fuse_log(FUSE_LOG_ERR,"Could not read dir entry %d\n",i);
            } else {
                found=!strcmp(file,entry->name);
            }
            free(entry);
        } else if(type==File) { // File
            struct file_entry fe;
            int error=getFileEntry(parentDir->child_entries[i],&fe);
            if(error) {
                fuse_log(FUSE_LOG_ERR,"Could not read file entry %d: %d\n",i,error);
            } else {
                found=!strcmp(file,fe.name);
            }
        }
    }
    if(found) {
        fuse_log(FUSE_LOG_DEBUG,"File %s already exists\n",file);
        free(parentDir);
        free(filec);
        return -EEXIST;
    }
    struct sf_entry *e=createFileEntry(file,0,parentPosition);
    free(filec);
    // No data available for uid and gid, so default values only!
    e->entry.file.uid=0;
    e->entry.file.gid=0;
    e->entry.file.permissions=mode&(~(uint32_t)S_IFMT);
    e->entry.file.data_entry=0;
    uint64_t newPosition=appendEntry(e);
    // Add to parent directory
    struct sf_entry *newParent=createDirEntry(parentDir->name,parentDir->child_count+1);
    memcpy(&newParent->entry.dir,parentDir,(size_t)sizeOfDirectoryEntry(parentDir));
    free(parentDir);
    // Add at end
    newParent->entry.dir.child_entries[newParent->entry.dir.child_count]=newPosition;   // Current count is last/new index
    newParent->entry.dir.child_count++; // Has been overwritten with memcpy!
    newParent->entry.dir.mtime=(uint32_t)time(NULL);
    newPosition=appendEntry(newParent);

    char *dirc=strdup(path);
    char *parentPath=dirname(dirc);
    int res=updateDirHierarchy(parentPath,parentPosition,newPosition);
    free(dirc);
    return res;
}

static int sf_write(const char *path, const char *buf, size_t siz,
             off_t offs, __attribute__((unused)) struct fuse_file_info *fi) {
    fuse_log(FUSE_LOG_DEBUG,"Writing to file %s at offset %ld length %ld\n",path,offs,siz);
    if(offs<0) {
        fuse_log(FUSE_LOG_ERR,"Negatige offset\n");
        return -ENOENT;
    }
	uint32_t offset=(uint32_t)offs;
	uint32_t size=(uint32_t)siz;
    // Get file info
    uint64_t previousPosition;
    struct file_entry *f=findFileEntry(path,&previousPosition);
    if(f==NULL) {
        fuse_log(FUSE_LOG_DEBUG,"File not found\n");
        return -ENOENT;
    }
    if(size==0) {
        free(f);
        return 0;
    }
    if(offset>f->size) {    // We cannot write past the end. Note: f->size-1 is last byte, so f->size is a valid offset as we will not get any empty space
        free(f);
        fuse_log(FUSE_LOG_DEBUG,"Cannot write to a location after the end of the file\n");
        return ENOSPC;
    }
    // Find any partial starting block (if any) and get the data from before
    bool partialFirst=offset%DATABLOCKSIZE!=0;
    uint32_t firstBlockOffset=(offset/DATABLOCKSIZE)*DATABLOCKSIZE;
    // Find any partial ending block (if any) and get the data from afterwards
    bool partialLast=(offset+size-1)%DATABLOCKSIZE!=DATABLOCKSIZE-1;
    uint32_t lastBlockOffset=((offset+size-1)/DATABLOCKSIZE)*DATABLOCKSIZE;
    fuse_log(FUSE_LOG_DEBUG,"First block offset: %d (partial: %s), last block offset: %d (partial: %s)\n",firstBlockOffset,partialFirst?"Yes":"No",lastBlockOffset,partialLast?"Yes":"No");
    char firstBlock[DATABLOCKSIZE];
    // Fill at end with data from beginning of buf
    memcpy(firstBlock+offset%DATABLOCKSIZE,buf,(size_t)(DATABLOCKSIZE-offset%DATABLOCKSIZE));
/*
if(offset%DATABLOCKSIZE) {
    printf("Skipping %ld (yet) unknown bytes\n",offset%DATABLOCKSIZE);
}
uint32_t len=DATABLOCKSIZE-offset%DATABLOCKSIZE;    // Complicated: Just to avoid errors on accessing not-yet-initialized parts.
if(offset%DATABLOCKSIZE+size<len) {
    len=size;
}
printHex("First block content",firstBlock+offset%DATABLOCKSIZE,len);
*/
    char lastBlock[DATABLOCKSIZE]={0};  // must be initialized, as if appending at the end we don't fill it up --> valgrind message
    // Fill at start with data from end of buf
    memcpy(lastBlock,buf+size-(offset+size)%DATABLOCKSIZE,(size_t)((offset+size)%DATABLOCKSIZE));
    // Do we need to fill the start of the first block with existing data, as we start in the middle?
    bool partialFirstFound=!partialFirst;
    // Do we need to fill the end of the last block with existing data, as we end in the middle?
    bool partialLastFound=!partialLast    // Last block is already full
    // Calculate index of last byte in the last block (not the last used byte but the last offset which does not require adding a new block!)
    || lastBlockOffset>f->size-1+(DATABLOCKSIZE-1-(f->size-1)%DATABLOCKSIZE)    // We append at least one block after the end of the file
    || offset==f->size; // Append exactly at end of file (but potentially not adding a block) -> no filling of end of last block needed
    uint64_t nextData=f->data_entry;
    while((!partialFirstFound) || (!partialLastFound)) {
        struct data_entry dataEntry;
        int result=getDataEntry(nextData,&dataEntry);
        if(result) {
            fuse_log(FUSE_LOG_ERR,"Reached end of file list and still missing data...\n");
            return -EFAULT;
        }
        if(partialFirst && !partialFirstFound && dataEntry.offset==firstBlockOffset) {
            fuse_log(FUSE_LOG_DEBUG,"Filling partial first block from 0 - %ld\n",offset%DATABLOCKSIZE);
            // Fill remaining data
            memcpy(firstBlock,dataEntry.data,(size_t)(offset%DATABLOCKSIZE));
            partialFirstFound=true;
        }
        if(partialLast && !partialLastFound && dataEntry.offset==lastBlockOffset) {
            fuse_log(FUSE_LOG_DEBUG,"Filling partial last block from %ld - %ld\n",(offset+size)%DATABLOCKSIZE,DATABLOCKSIZE-(offset+size)%DATABLOCKSIZE);
            memcpy(lastBlock+(offset+size)%DATABLOCKSIZE,dataEntry.data+(offset+size)%DATABLOCKSIZE,(size_t)(DATABLOCKSIZE-(offset+size)%DATABLOCKSIZE));
            partialLastFound=true;
        }
        nextData=dataEntry.previous_data_entry;
    }
    nextData=f->data_entry;
    if(partialFirst && partialLast && firstBlockOffset==lastBlockOffset) {
        // TODO: Test this case
        fuse_log(FUSE_LOG_DEBUG,"Partial first and last blocks must be merged\n");
        // We have to combine both into a single block
        char block[DATABLOCKSIZE];
        memcpy(&block,&firstBlock,(size_t)(offset%DATABLOCKSIZE));
        memcpy(&block+offset%DATABLOCKSIZE,buf,(size_t)size);   // Size MUST be smaller than DATABLOCKSIZE here!
        memcpy(&block+offset%DATABLOCKSIZE+size,&lastBlock+(offset+size)%DATABLOCKSIZE,(size_t)(DATABLOCKSIZE-size-offset%DATABLOCKSIZE));
        struct sf_entry *d=createDataEntry(nextData,block,offset,DATABLOCKSIZE);
        nextData=appendEntry(d);
    } else {
        if(partialFirst) {
            fuse_log(FUSE_LOG_DEBUG,"Adding partial first block\n");
            struct sf_entry *d=createDataEntry(nextData,firstBlock,firstBlockOffset,DATABLOCKSIZE);
            nextData=appendEntry(d);
            firstBlockOffset+=DATABLOCKSIZE;    // Ensure to not write it again with the full blocks
        }
        if(partialLast) {
            fuse_log(FUSE_LOG_DEBUG,"Adding partial last block\n");
            uint32_t len=(offset+size-1)%DATABLOCKSIZE+1;
            struct sf_entry *d=createDataEntry(nextData,lastBlock,lastBlockOffset,len);
            nextData=appendEntry(d);
            if(lastBlockOffset>DATABLOCKSIZE) {
                lastBlockOffset-=DATABLOCKSIZE; // Ensure to not write it again with the full blocks
            } else {
                lastBlockOffset=0;    // Unsigned, so we cannot go into negative numbers and must clamp to 0
            }
        }
    }
    // Add all the remaining middle blocks
    for(uint32_t i=firstBlockOffset;i<=lastBlockOffset;i+=DATABLOCKSIZE) {
        fuse_log(FUSE_LOG_DEBUG,"Adding block for offset %d\n",i);
        uint32_t len=DATABLOCKSIZE;
        if(i==lastBlockOffset && offset+size<i+DATABLOCKSIZE) {
            len=(offset+size)%DATABLOCKSIZE;
        }
        struct sf_entry *d=createDataEntry(nextData,buf+i-offset%DATABLOCKSIZE,i,len);
        nextData=appendEntry(d);
    }
    // Update file entry and all directory entries
    struct sf_entry *e=createFileEntry(f->name,f->size>offset+size?f->size:offset+size,previousPosition);
    e->entry.file.uid=f->uid;
    e->entry.file.gid=f->gid;
    e->entry.file.permissions=f->permissions;
    e->entry.file.ctime=f->ctime;
    e->entry.file.mtime=(uint32_t)time(NULL);   // Set to now
    e->entry.file.data_entry=nextData;
    uint64_t newPosition=appendEntry(e);
    updateDirHierarchy(path,previousPosition,newPosition);
    free(f);
    return (int)size;
}

int sf_chmod(const char *path, mode_t mode, __attribute__((unused)) struct fuse_file_info *fi) {
    fuse_log(FUSE_LOG_DEBUG,"Chmod %s to %0o\n",path,mode);
    // Get file info
    uint64_t previousPosition;
    // TODO: Does NOT work for directories, obviously...
    struct file_entry *f=findFileEntry(path,&previousPosition);
    if(f==NULL) {
        fuse_log(FUSE_LOG_DEBUG,"File not found\n");
        return -ENOENT;
    }
    if(f->permissions!=mode) {
        struct sf_entry *e=createFileEntry(f->name,f->size,previousPosition);
        e->entry.file.uid=f->uid;
        e->entry.file.gid=f->gid;
        e->entry.file.permissions=mode;   // Update permissions
        e->entry.file.ctime=f->ctime;
        e->entry.file.mtime=(uint32_t)time(NULL);   // Set to now
        e->entry.file.data_entry=f->data_entry;
        uint64_t newPosition=appendEntry(e);
        updateDirHierarchy(path,previousPosition,newPosition);
    }
    free(f);
    return 0;
}

// Unless FUSE_CAP_HANDLE_KILLPRIV is disabled, this method is expected to reset the setuid and setgid bits.
// fuse_conn_info.capable
int sf_chown(const char *path,uid_t uid, gid_t gid, __attribute__((unused)) struct fuse_file_info *fi) {
    fuse_log(FUSE_LOG_DEBUG,"Chown %s to UID=%d, GID=%d\n",path,uid,gid);
    // Get file info
    uint64_t previousPosition;
    // TODO: Does NOT work for directories, obviously...
    struct file_entry *f=findFileEntry(path,&previousPosition);
    if(f==NULL) {
        fuse_log(FUSE_LOG_DEBUG,"File not found\n");
        return -ENOENT;
    }
    if(f->uid!=uid || f->gid!=gid) {
        struct sf_entry *e=createFileEntry(f->name,f->size,previousPosition);
        e->entry.file.uid=uid;
        e->entry.file.gid=gid;
        e->entry.file.permissions=f->permissions & (~(uint32_t)S_ISUID | ~(uint32_t)S_ISGID);
        e->entry.file.ctime=f->ctime;
        e->entry.file.mtime=(uint32_t)time(NULL);   // Set to now
        e->entry.file.data_entry=f->data_entry;
        uint64_t newPosition=appendEntry(e);
        updateDirHierarchy(path,previousPosition,newPosition);
    }
    free(f);
    return 0;
}

int sf_utimens(const char *path, const struct timespec tv[2], __attribute__((unused)) struct fuse_file_info *fi) {
    fuse_log(FUSE_LOG_DEBUG,"Utimens %s; mtime=");
    if(tv[1].tv_nsec==UTIME_NOW) {
        fuse_log(FUSE_LOG_DEBUG,"NOW\n");
    } else {
        fuse_log(FUSE_LOG_DEBUG,"%ld sec, %ld nsec\n",tv[1].tv_sec,tv[1].tv_nsec);
    }
    // Get file info
    uint64_t previousPosition;
    struct file_entry *f=findFileEntry(path,&previousPosition);
    if(f==NULL) {
        fuse_log(FUSE_LOG_DEBUG,"File not found\n");
        return -ENOENT;
    }
    // tv[0] is access time: we don't store that...
    if(f->mtime!=tv[1].tv_sec && tv[1].tv_nsec!=UTIME_OMIT) {
        struct sf_entry *e=createFileEntry(f->name,f->size,previousPosition);
        e->entry.file.uid=f->uid;
        e->entry.file.gid=f->gid;
        e->entry.file.permissions=f->permissions;
        e->entry.file.ctime=f->ctime;
        if(tv[1].tv_nsec==UTIME_NOW) {
            e->entry.file.mtime=(uint32_t)time(NULL);
        } else {
            e->entry.file.mtime=(uint32_t)tv[1].tv_sec;
        }
        e->entry.file.data_entry=f->data_entry;
        uint64_t newPosition=appendEntry(e);
        updateDirHierarchy(path,previousPosition,newPosition);
    }
    free(f);
    return 0;
}


static const struct fuse_operations xmp_oper = {
    .init       = sf_init,
    .destroy    = sf_destroy,
    .getattr    = sf_getattr,
    .readdir    = sf_readdir,
    .mkdir      = sf_mkdir,
    .unlink     = sf_unlink,
    .rmdir      = sf_rmdir,
    .truncate   = sf_truncate,
    .open       = sf_open,
    .read       = sf_read,
    .write      = sf_write,
    .release    = sf_release,
    .create     = sf_create,
    .chmod      = sf_chmod,
    .chown      = sf_chown,
    .utimens    = sf_utimens,
};

static void sf_printLog(enum fuse_log_level level, const char *fmt, va_list ap) {
    if(level<=lastLevelToShow) {
        vfprintf(stderr, fmt, ap);
    }
}

int main(int argc, char *argv[]) {
    printf("FUSE library version %s\n", fuse_pkgversion());
    // Set our own log function; the default one prints everything regardless of log level
    fuse_set_log_func(sf_printLog);
    // Start filesystems
    return fuse_main(argc, argv, &xmp_oper, NULL);
}

static void dumpFS(void) {
    printf("\n\nDumping filesystem\n");
    uint64_t rdp=getRootDirPos();
    struct directory_entry *rd=findRootDir();
    printf("Root dir at %lu:\n",rdp);
    printDirEntry(rd);
    for(uint32_t i=0;i<rd->child_count;i++) {
        printf("Child %u:\n",i);
        struct sf_entry *e=getEntry(rd->child_entries[i]);
        if(e->type==Directory) {
            printDirEntry(&e->entry.dir);
        } else if (e->type==File) {
            printFileEntry(&e->entry.file);
        } else {
            printf("Unknown type %d\n",e->type);
        }
        free(e);
    }
    free(rd);
    printf("\n\n");
}
