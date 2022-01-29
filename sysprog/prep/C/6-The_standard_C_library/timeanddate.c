/* Required for non-standard strptime() call */
#define _XOPEN_SOURCE

#include <stdio.h>
#include <stdlib.h>
#include <time.h>

char * get_day_of_week(int);

int main(void) {

	time_t timestamp = time(0);
	struct tm *date_and_time;
	char datestring[100];

	printf("Number of seconds elapsed since 00:00:00 on January 1, 1970, Coordinated Universal Time is %lu\n", (unsigned long) timestamp);

	date_and_time = localtime(&timestamp);
	printf("The current date and time is: %d-%d-%d %d:%d:%d\n", date_and_time->tm_year + 1900,
															date_and_time->tm_mon + 1,	/* Months go from 0 to 11 */
															date_and_time->tm_mday,		/* Days go from 1 to 31 as normal */
															date_and_time->tm_hour,
															date_and_time->tm_min,
															date_and_time->tm_sec);

	printf("In standard format: %s", asctime(date_and_time));	/* Newline added at end */

	char * name_of_weekday = get_day_of_week(date_and_time->tm_wday);
	printf("The current day of the week is %s\n\n", name_of_weekday);

	/* Change to one year in the future */
	date_and_time->tm_year++;

	/* Re-adjust the rest of the structure (e.g., weekday) and get new timestamp */
	timestamp = mktime(date_and_time);

	name_of_weekday = get_day_of_week(date_and_time->tm_wday);
	printf("One year from now, the day of the week will be %s\n", name_of_weekday);
	printf("Then, the number of seconds elapsed since 00:00:00 on January 1, 1970, Coordinated Universal Time will be %lu\n", (unsigned long) timestamp);

	printf("In standard format: %s", ctime(&timestamp));	/* Newline added at end */

	strftime(datestring, sizeof(datestring), "%A, %B %d, week %V", date_and_time);
	printf("Or in a custom format: %s\n\n", datestring);

	/* Parsing a date string */
	if(strptime("December 21, 2012", "%B %d, %Y", date_and_time) != NULL) {
		printf("The day where the world is supposed to end: %s", asctime(date_and_time));
	} else {
		fprintf(stderr, "Date conversion failed\n");
	}

	return 0;
}

char * get_day_of_week(int dow) {
	char *dow_name;
	switch (dow) {
		case 0: dow_name = "Sunday"; break;
		case 1: dow_name = "Monday"; break;
		case 2: dow_name = "Tuesday"; break;
		case 3: dow_name = "Wednesday"; break;
		case 4: dow_name = "Thursday"; break;
		case 5: dow_name = "Friday"; break;
		case 6: dow_name = "Saturday"; break;
		default: dow_name = "Invalid day number"; break;
	}
	return dow_name;
}
