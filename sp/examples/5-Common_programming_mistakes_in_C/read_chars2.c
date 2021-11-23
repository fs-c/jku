	...

	char c;
	while ((c = getc(file)) != EOF) {
		putchar(c);
	}
	if (feof(file)) {
		printf("File ended normally\n");
	} else if (ferror(file)) {
		printf("File error\n");
	} else {
		printf("What was the problem again?\n");
	}
	
	...