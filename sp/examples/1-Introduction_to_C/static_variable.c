#include <stdio.h>

void increment()
{
	static int i = 0;
  	printf("i=%d\n", i++);
}

int main(void) {
	int j = 0;
	for(; j<10; j++)
	   increment();
	return 0;
}
