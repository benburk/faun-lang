// Measure only the child: for small static ELFs, Python's resident set
// before exec can be larger than the whole program being measured.
#define _GNU_SOURCE
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/resource.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

int main(int argc, char **argv) {
    if (argc < 4) return 1;
    struct timespec start, end;
    struct rusage usage;
    int status;
    if (clock_gettime(CLOCK_MONOTONIC, &start)) return 1;
    pid_t child = fork();
    if (child < 0) return 1;
    if (child == 0) {
        alarm(atoi(argv[1]));
        execv(argv[3], argv + 3);
        perror("execv");
        _exit(127);
    }
    while (wait4(child, &status, 0, &usage) < 0) {
        if (errno != EINTR) return 1;
    }
    if (clock_gettime(CLOCK_MONOTONIC, &end)) return 1;
    if (WIFSIGNALED(status)) {
        fprintf(stderr, "signal %d\n", WTERMSIG(status));
        return 128 + WTERMSIG(status);
    }
    if (!WIFEXITED(status)) return 1;
    if (WEXITSTATUS(status)) return WEXITSTATUS(status);
    FILE *metrics = argv[2][0] == '-' ? stderr : fopen(argv[2], "w");
    if (!metrics) return 1;
    fprintf(metrics, "%lld %ld\n",
            (end.tv_sec - start.tv_sec) * 1000000000LL + end.tv_nsec - start.tv_nsec,
            usage.ru_maxrss);
    return fclose(metrics) == 0 ? 0 : 1;
}
