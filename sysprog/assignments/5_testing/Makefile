all: testing

testing: main.c presettings.h
	gcc -std=c17 -Wall -Wextra -g -o testing main.c presettings.h -fsanitize=address

clean:
	rm -f testing
