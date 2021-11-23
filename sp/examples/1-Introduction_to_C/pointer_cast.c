#include <stdio.h>

int main(void) {
        float x = 6.0;
        int d = (int)x;
	printf("d=%d\n", d);
	printf("d=%d\n", *((int*)&x));
	printf("%d\n", (1<<30)+(1<<23)+(1<<22));
return 0;
}
