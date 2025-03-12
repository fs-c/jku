#ifndef shortFUSE
#define shortFUSE

#include <stdio.h>
#include <stdint.h>

// Size of a single block of content data (=data length inside)
#define DATABLOCKSIZE ((uint32_t)10)
//#define DATABLOCKSIZE (512-sizeof(uint64_t)-sizeof(off_t)-offsetof(struct sf_entry,entry))    // To get data blocks of 512 bytes total

// Maximum length of a filename. Note: not the full path; that's length is unlimited in this filesystem
#define MAX_FILENAME_LENGTH (255)


struct __attribute__((__packed__)) super_block {
    unsigned char magic_number[8];  // "shrtFUSE"
    uint16_t version;               // Version number: currently only "1"
    uint64_t root_dir_offset;       // Link to current directory_entry of root directory
    uint32_t crc;                   // CRC of the whole superblock
};

/* Not actually used - only concept!
struct filesystem {
        struct super_block superBlock;
        struct sf_entry content[];  // Note: each has different length...
}
*/

// Kinds of entry types
typedef enum {Unknown = -1, Directory = 0, File = 1, Data = 2} sfType;

// Entry type = 0
struct __attribute__((__packed__)) directory_entry {
    uint32_t child_count; // No diff to previous entries - always full list
    char name[MAX_FILENAME_LENGTH+1];
    uint32_t uid;                // User-ID (Owner)
    uint32_t gid;                // Group-ID
    uint32_t permissions;        // Permissions (Unix-like)
    uint32_t ctime;              // Creation time of this directory
    uint32_t mtime;              // Time of last modification of this directory
    uint32_t depth;              // Depth of directory (0 .. root)
    uint64_t child_entries[];    // Child elements within this directory; can be files or directory entries
};
/* ATTENTION: the offset of child_count is used as the minimal size to read for an sf_entry
 * This also means, that any variable-size entries must have all the data needed to calculate their
 * actual size before this number of bytes!
 */

// Entry type = 1
struct __attribute__((__packed__)) file_entry {
    char name[MAX_FILENAME_LENGTH+1];
    uint32_t uid;                // User-ID (Owner)
    uint32_t gid;                // Group-ID
    uint32_t permissions;        // Permissions (Unix-like)
    uint32_t ctime;              // Creation time of this file
    uint32_t mtime;              // Time of last modification of this file
    uint32_t size;               // Size of the file in bytes
    uint64_t data_entry;         // Link to last data entry
//  uint64_t old_directory_entry;   // To allow reconstruction if writing the rest of the hierarchy fails. For new files this is the directory it should be created in. How do we know which entry to replace? -> go back in list of data entries to the first one which is different from this entry, this is the address of the "old" file entry; this we have to look for in the old_directory_entry, replace it with the address of this entry, and then append the new entry (plus chain up).
};

// Entry type = 2
// Note: we only store full blocks. This may waste space but makes the program INFINITELY more simple!
// But this also means, that on writing we may have to find the first&last blocks first and copy the partial new data into them
struct __attribute__((__packed__)) data_entry {
    uint64_t previous_data_entry;         // Link to the previous (in chain of entries, not as in "version of this data")
    uint32_t offset;                      // Offset of this data in the file
    // Cannot use offsetof here of ourself, as it is not completely defined yet...
    // We also cannot use sf_entry (and if we move it ahead, it will not work either; declaring it won't work, as it's not a pointer)
    // We ignore this here (we could subtract sizeof(uint8_t) and sizeof(uint32_t) though)
    // So we just define it at the top
    unsigned char data[DATABLOCKSIZE];    // The actual data content
};

struct __attribute__((__packed__)) sf_entry {
    uint32_t crc;   // Checksum of the whole entry (=including the variable-length entry below!)
    uint8_t type;   // Determines the type (and length) of the entry below!
    union {         // One of various kinds of entries
        struct directory_entry dir;
        struct file_entry file;
        struct data_entry data;
    } entry;
};


// Debug/Helper functions

static void printHex(const char *title,const void* data,const uint32_t len) {
    printf("%s: ",title);
    for(uint32_t i=0;i<len;i++) {
        printf("%02X ",((const uint8_t*)data)[i]);
    }
    printf("\n");
}

static void printDirEntry(const struct directory_entry *de) {
    printf("Directory entry %s:\n",de->name);
    printf("Depth=%u\n",de->depth);
    printf("UID=%u, GID=%u, Perm=%o\n",de->uid,de->gid,de->permissions);
    printf("CTime=%u, MTime=%u\n",de->ctime,de->mtime);
    printf("%u child entries:\n",de->child_count);
    for(uint32_t i=0;i<de->child_count;i++) {
        printf("  %u @ %lu\n",i,de->child_entries[i]);
    }
    printf("\n");
}

static void printFileEntry(const struct file_entry *fe) {
    printf("File entry %s:\n",fe->name);
    printf("UID=%u, GID=%u, Perm=%o\n",fe->uid,fe->gid,fe->permissions);
    printf("CTime=%u, MTime=%u\n",fe->ctime,fe->mtime);
    printf("Size: %u:\n",fe->size);
    printf("Last data entry @ %lu:\n",fe->data_entry);
    printf("\n");
}

static void printDataEntry(const struct data_entry *de) {
    printf("Data entry:\n");
    printf("Previous data entry @: %lu\n",de->previous_data_entry);
    printf("Offset: %u\n",de->offset);
    uint32_t len=DATABLOCKSIZE;
    printf("Data content (length %u):\n",len);
    printHex("",de->data,len);
    printf("\n");
}

__attribute__((unused)) static void printSFEntry(const struct sf_entry *entry) {
    printf("SF-Entry Type=");
    if(entry->type==0) {
        printf("Directory\n");
        printDirEntry((const struct directory_entry*)&entry->entry.dir);
    } else if(entry->type==1) {
        printf("File\n");
        printFileEntry((const struct file_entry*)&entry->entry.file);
    } else if(entry->type==2)  {
        printf("Data\n");
        printDataEntry((const struct data_entry*)&entry->entry.data);
    }
//  printf("CRC: %ld\n",entry->crc);
    printHex("First 20 bytes",&entry->entry,20);
}

__attribute__((unused)) static void dumpFS(void);

#endif
