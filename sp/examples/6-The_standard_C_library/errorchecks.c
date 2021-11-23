#include <stdio.h>
#include <errno.h>
#include <string.h>

#define MSG_LEN 200

int main(void) {

	/* Buffer to hold error message */
	char error_msg[MSG_LEN];

	/* Try to open file that doesn't exist */
	FILE *file = NULL;
	file = fopen("notexistingfile", "r");

	if (file == NULL) {
		fprintf(stderr, "Error number %d occurred: %s\n", errno, strerror(errno));
	}

	/* Try to write to standard input */
	if (fputc(1, stdin) == EOF) {

		int errorCode = errno;
		int retCode = strerror_r(errno, error_msg, MSG_LEN);

		/* strerror_r can also fail */
		switch (retCode) {
			case 0:			/* success */
				fprintf(stderr, "Error number %d occurred: %s\n", errorCode, error_msg);
				break;
			case EINVAL:	/* invalid value */
				fprintf(stderr, "Error number %d occurred but no error message could be found\n", errorCode);
				break;
			case ERANGE:	/* range exceeded */
				fprintf(stderr, "Error number %d occurred but buffer was too small to hold error message\n", errorCode);
				break;
			default:		/* other error */
				fprintf(stderr, "Error number %d occurred\n", errorCode);
				break;
		}
	}

	/* Try to close standard input two times */
	fclose(stdin);
	if (fclose(stdin) == EOF) {
		perror("Error when closing standard input the second time");
	}

	return 0;
}
