#!/bin/sh
SECTIONS=$(readelf -S $1)
#echo -e "$SECTIONS"

# .text section
TEXT=$(echo -e "${SECTIONS}" |grep -A 1 " .text")
#echo "Syntax: [Nr] Name Type Address Offset Size EntSize Flags Link Info Align"
#echo -e $TEXT
OFFSET=$(echo ${TEXT} | sed 's/\[.*\]\ //' | cut -d ' ' -f 4)
LENGTH=$(echo ${TEXT} | sed 's/\[.*\]\ //' | cut -d ' ' -f 5 )
echo "${OFFSET} ${LENGTH}"

# .rodata section
TEXT=$(echo -e "${SECTIONS}" |grep -A 1 " .rodata")
#echo "Syntax: [Nr] Name Type Address Offset Size EntSize Flags Link Info Align"
#echo -e $TEXT
OFFSET=$(echo ${TEXT} | sed 's/\[.*\]\ //' | cut -d ' ' -f 4)
LENGTH=$(echo ${TEXT} | sed 's/\[.*\]\ //' | cut -d ' ' -f 5 )
echo "${OFFSET} ${LENGTH}"

# Start offset in .text section
SYMBOLS=$(readelf -s $1)
#echo -e "$SYMBOLS"
FILTER=$(echo -e "$SYMBOLS" | grep "filterProc")
#echo "Syntax: Num Value Size Type Bind Vis Ndx Name"
#echo -e "$FILTER"
START=$(echo ${FILTER} | sed 's/.*:\ //' | cut -d ' ' -f 1)
echo "${START}"

# Text relocation information - may be multiple lines
RELOC=$(readelf -r $1)
#echo -e "$RELOC"
TABLE=$(echo -e "${RELOC}" | sed -n '/.rela.text/,/.rela.data/p' | head -n -2 | tail -n +3)
#echo "Syntax: Offset Info Type Sym.-Value Sym.-Name Addend"
#echo -e "${TABLE}"

while IFS= read -r LINE; do
    #echo "Line: ${LINE}"
    OFFSET=$(echo ${LINE} | cut -d ' ' -f 1)
    NAME=$(echo ${LINE} | cut -d ' ' -f 5)
    SIGN=$(echo ${LINE} | cut -d ' ' -f 6)
    ADDEND=$(echo ${LINE} | cut -d ' ' -f 7)
    echo "${NAME} ${OFFSET} ${SIGN}${ADDEND}"
done <<< "${TABLE}"

# use $ as a separator between different relocation types (shouldn't be a valid symbol name so no conflict)
echo "$"

# RoData relocation information
RELOC=$(readelf -r $1)
TABLE=$(echo -e "${RELOC}" | sed -n '/.rela.data/,/.rela.eh_frame/p' | head -n -2 | tail -n +3)

while IFS= read -r LINE; do
    #echo "Line: ${LINE}"
    OFFSET=$(echo ${LINE} | cut -d ' ' -f 1)
    NAME=$(echo ${LINE} | cut -d ' ' -f 5)
    SIGN=$(echo ${LINE} | cut -d ' ' -f 6)
    ADDEND=$(echo ${LINE} | cut -d ' ' -f 7)
    echo "${NAME} ${OFFSET} ${SIGN}${ADDEND}"
done <<< "${TABLE}"
