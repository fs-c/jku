#include <stdio.h> 

int main(void) 
{ 
	char msg[10]; /* array of 10 chars */ 
	char *p; /* pointer to a char */ 
	char msg2[]="Hello"; /* msg2 = 'H' 'e' 'l' 'l 'o' '\0' */ 

	/* ERROR. msg has a const address.*/ 
/* msg = "Bonjour"; */
	p = "Bonjour"; /* address of "Bonjour" goes into p */ 

	/* ERROR. Message has a constant address.
	 * cannot change it. */ 
/* msg = p; */
            

	p = msg; /* OK */ 

	p[0] = 'H', p[1] = 'i', p[2] = '\0'; 
	/* *p and msg are now "Hi" */ 

	printf("msg=%s\n", msg); 
	printf("msg2=%s\n", msg2); 
	
	return 0;
} 
