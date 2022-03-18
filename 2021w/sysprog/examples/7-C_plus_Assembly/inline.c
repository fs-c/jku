#include <stdio.h> 
#include <stdlib.h>
#include <stdint.h>

#define LEN 10

static void cpuid(uint32_t code, uint32_t *a, uint32_t *b, uint32_t *d) {
    __asm__ volatile ("cpuid\n" : "=a"(*a), "=b"(*b), "=d"(*d)  : "0"(code) : "ecx");
}

void clearArray(int32_t *ptr, uint64_t length) {
	__asm__ (
		"cmpq $0,%2\n"		/* Compare the argument 2 (=third=length) with the value zero */
		"jle end\n"		/* If the len is negative or zero, we have nothing to do */
		"start:\n"		/* Start of loop */
		"decq %2\n"		/* First array element is at index length-1 */
		"movl $0,(%1,%2,4)\n"	/* Clear element. Take care: %1 is an address so we must use the appropriate addressing mode! */
		"cmpq $0,%2\n"		/* End reached? */
		"jg start\n"
		"end:\n"
	: "=r" (length) 		/* Define length as output, as inputs may never be changed - unless they are output too. Put it in any register (=argument 0; Note: address!) */
	:"r" (ptr), "0" (length) 	/* ptr -> any register (=argument 1); length is the same as the output ("0" = first argument; this is argument 2) */
	: "cc"				/* Flags register will be clobbered */
	);
}

int main(void) { 
	int32_t *ptr; 
	unsigned int i;
	unsigned int check;

	uint32_t a, b, d;
	cpuid(0, &a, &b, &d);
	/* Rest of string would be in ECX! */
	printf("CPUID: A=%0X, B=%0X, D=%0X\n%c%c%c%c %c%c%c%c\n\n", a, b, d, b&0xff, b>>8&0xff, b>>16&0xff, b>>24, d&0xff, d>>8&0xff, d>>16&0xff, d>>24);
	
	/* allocate space to hold an array of LEN ints */ 
	ptr= (int32_t*) malloc(LEN * sizeof(int32_t)); 

	/* Fill array with some values */ 
	for (i = 0; i < LEN; i++) {
		ptr[i] = i - LEN / 2 + 1;
	}

	/* Call function to clear array */ 
	clearArray(ptr, LEN);

	/* Print content of array and check it */ 
	check = 1;
	for (i = 0; i < LEN; i++) {
		printf("%d", ptr[i]);
		if (i < LEN - 1) {
			printf(", ");
		}
		check = check && (ptr[i] == 0);
	}
	printf("\n");
	if (check) {
		printf("Array successfully cleared!\n");
	} else {
		printf("ERROR: Array NOT cleared!\n");
	}

	 /* free up the allocated space */
	free(ptr); 
	
	return 0;
} 
