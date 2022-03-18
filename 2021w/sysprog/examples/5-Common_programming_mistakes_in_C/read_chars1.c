	...
	
	char c;
	while (!feof(file)) {
		c = getc(file);
		putchar(c);
	}
	
	...