#include <stdio.h>

int main(void) { 
	
	int row, col;
	
/*	This way of initializing arrays is not correct */
/*	char multi[5][10];
	
	multi[0] = {'0','1','2','3','4','5','6','7','8','9'};
	multi[1] = {'a','b','c','d','e','f','g','h','i','j'};
	multi[2] = {'A','B','C','D','E','F','G','H','I','J'};
	multi[3] = {'9','8','7','6','5','4','3','2','1','0'};
	multi[4] = {'J','I','H','G','F','E','D','C','B','A'}; */

/*	Here's how to do it correctly */
	char multi[5][10] = {{'0','1','2','3','4','5','6','7','8','9'},
						 {'a','b','c','d','e','f','g','h','i','j'},
						 {'A','B','C','D','E','F','G','H','I','J'},
						 {'9','8','7','6','5','4','3','2','1','0'},
						 {'J','I','H','G','F','E','D','C','B','A'}};

	for (row = 0; row < 5; row++) {
		for (col = 0; col < 10; col++) {
			printf("%2c ",multi[row][col]);
		}
		printf("\n");
	}
	
	return 0;
} 
