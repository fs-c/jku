#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <fcntl.h>

#define PROC_PATH "/proc/kbd_buffer"
#define MAX_READ 4

int main()
{
    unsigned char buffer[MAX_READ];

    const int fd = open(PROC_PATH, O_RDONLY);
    if (fd == -1)
    {
        perror("error opening proc file");
        return 1;
    }

    while (true)
    {
        const ssize_t bytes_read = read(fd, buffer, MAX_READ);
        if (bytes_read <= 0)
        {
            break;
        }

        for (int i = 0; i < bytes_read; i++)
        {
            printf("%d ", buffer[i]);
        }
        printf("\n");

        if (bytes_read < MAX_READ)
        {
            break;
        }

        sleep(2);
    }

    close(fd);
    return 0;
}