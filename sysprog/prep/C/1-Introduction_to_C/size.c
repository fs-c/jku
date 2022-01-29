#include <stdlib.h>
#include <stdio.h>
#include <limits.h>

int main(void) {
	/* Note: %lu is the best match for size_t in C90; from C99 on it should be %zu */
	printf("char                  : %zu (%d...%d)\n",sizeof(char),CHAR_MIN,CHAR_MAX);
	printf("signed char           : %zu (%d...%d)\n",sizeof(signed char),SCHAR_MIN,SCHAR_MAX);
	printf("unsigned char         : %zu (%u...%u)\n",sizeof(unsigned char),0,UCHAR_MAX);
	printf("short                 : %zu (%d...%d)\n",sizeof(short),SHRT_MIN,SHRT_MAX);
	printf("short int             : %zu (%d...%d)\n",sizeof(short int),SHRT_MIN,SHRT_MAX);
	printf("signed short          : %zu (%d...%d)\n",sizeof(signed short),SHRT_MIN,SHRT_MAX);
	printf("signed short int      : %zu (%d...%d)\n",sizeof(signed short int),SHRT_MIN,SHRT_MAX);
	printf("unsigned short        : %zu (%u...%u)\n",sizeof(unsigned short),0,USHRT_MAX);
	printf("unsigned short int    : %zu (%u...%u)\n",sizeof(unsigned short int),0,USHRT_MAX);
	printf("int                   : %zu (%d...%d)\n",sizeof(int),INT_MIN,INT_MAX);
	printf("signed                : %zu (%d...%d)\n",sizeof(signed),INT_MIN,INT_MAX);
	printf("signed int            : %zu (%d...%d)\n",sizeof(signed int),INT_MIN,INT_MAX);
	printf("unsigned              : %zu (%d...%u)\n",sizeof(unsigned),0,UINT_MAX);
	printf("unsigned int          : %zu (%u...%u)\n",sizeof(unsigned int),0,UINT_MAX);
	printf("long                  : %zu (%ld...%ld)\n",sizeof(long),LONG_MIN,LONG_MAX);
	printf("long int              : %zu (%ld...%ld)\n",sizeof(long int),LONG_MIN,LONG_MAX);
	printf("signed long           : %zu (%ld...%ld)\n",sizeof(signed long),LONG_MIN,LONG_MAX);
	printf("signed long int       : %zu (%ld...%ld)\n",sizeof(signed long int),LONG_MIN,LONG_MAX);
	printf("unsigned long         : %zu (%u...%zu)\n",sizeof(unsigned long),0,ULONG_MAX);
	printf("unsigned long int     : %zu (%u...%zu)\n",sizeof(unsigned long int),0,ULONG_MAX);
	/* These will not work in C90: LLONG_MIN, LLONG_MAX, ULLONG_MAX do not exist there, as the 
	   long long datatype was introduced in C99 */
	printf("long long             : %zu (%lld...%lld)\n",sizeof(unsigned long int),LLONG_MIN,LLONG_MAX);
	printf("long long int         : %zu (%lld...%lld)\n",sizeof(unsigned long int),LLONG_MIN,LLONG_MAX);
	printf("signed long long      : %zu (%lld...%lld)\n",sizeof(unsigned long int),LLONG_MIN,LLONG_MAX);
	printf("signed long long int  : %zu (%lld...%lld)\n",sizeof(unsigned long int),LLONG_MIN,LLONG_MAX);
	printf("unsigned long long    : %zu (%u...%llu)\n",sizeof(unsigned long int),0,ULLONG_MAX);
	printf("unsigned long long int: %zu (%u...%llu)\n",sizeof(unsigned long int),0,ULLONG_MAX);
	printf("float                 : %zu\n",sizeof(float));
	printf("double                : %zu\n",sizeof(double));
	printf("long double           : %zu\n",sizeof(long double));
	printf("void                  : %zu\n",sizeof(void));
	printf("void*                 : %zu\n",sizeof(void*));
	return 0;
}
