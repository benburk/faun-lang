// Run a program and write what it took to a file: elapsed nanoseconds, its
// peak resident kilobytes, the instructions it ran in user space, or -1
// where the kernel will not count them, the nanoseconds of processor time
// it was given, which waiting for a busy processor does not lengthen, and
// the branches it took in user space, or -1, as the instructions.
//
//     measure SECONDS METRICS PROGRAM [ARGUMENT...]
//
// Only the program is measured, and each measure but the time is the same
// from run to run on a busy machine. The counter starts at the program's
// exec. Memory is counted from the program's page tables, since the peak
// `wait4` answers is rounded by the kernel's per-CPU bookkeeping, to a
// quarter of a megabyte on a machine of 32: it is read when the program
// leaves and before each call that could give memory back, between which
// it only grows, so the most seen is the peak. The program runs without
// address randomization or huge pages, which would move it by a page or by
// two megabytes.
#define _GNU_SOURCE
#include <errno.h>
#include <linux/filter.h>
#include <linux/perf_event.h>
#include <linux/seccomp.h>
#include <signal.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/personality.h>
#include <sys/prctl.h>
#include <sys/ptrace.h>
#include <sys/resource.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

// The kilobytes resident in a stopped program, or -1.
static long resident(pid_t program) {
    char path[64], line[256];
    long kilobytes = -1;
    snprintf(path, sizeof path, "/proc/%d/smaps_rollup", program);
    FILE *file = fopen(path, "r");
    if (!file) return -1;
    while (fgets(line, sizeof line, file)) {
        if (sscanf(line, "Rss: %ld kB", &kilobytes) == 1) break;
    }
    fclose(file);
    return kilobytes;
}

// Become the program, traced, stopping before each call that can give
// memory back.
static void become(char **argv) {
    struct sock_filter releasing[] = {
        BPF_STMT(BPF_LD | BPF_W | BPF_ABS, offsetof(struct seccomp_data, nr)),
        BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, SYS_munmap, 3, 0),
        BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, SYS_brk, 2, 0),
        BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, SYS_madvise, 1, 0),
        BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, SYS_mremap, 0, 1),
        BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_TRACE),
        BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ALLOW),
    };
    struct sock_fprog filter = {sizeof releasing / sizeof *releasing, releasing};
    personality(ADDR_NO_RANDOMIZE);
    prctl(PR_SET_THP_DISABLE, 1, 0, 0, 0);
    // Stop until the parent has set its options and attached its counter.
    if (ptrace(PTRACE_TRACEME, 0, 0, 0) || raise(SIGSTOP)) _exit(126);
    if (prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0)) _exit(126);
    if (prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, &filter)) _exit(126);
    alarm(atoi(argv[1]));
    execv(argv[3], argv + 3);
    perror("execv");
    _exit(127);
}

int main(int argc, char **argv) {
    if (argc < 4) return 2;
    pid_t child = fork();
    if (child < 0) return 1;
    if (child == 0) become(argv);
    int status;
    if (waitpid(child, &status, 0) < 0 || !WIFSTOPPED(status)) return 1;
    long stops = PTRACE_O_TRACESECCOMP | PTRACE_O_TRACEEXEC | PTRACE_O_TRACEEXIT;
    if (ptrace(PTRACE_SETOPTIONS, child, 0, stops | PTRACE_O_EXITKILL)) return 1;
    struct perf_event_attr counted = {
        .type = PERF_TYPE_HARDWARE,
        .size = sizeof counted,
        .config = PERF_COUNT_HW_INSTRUCTIONS,
        .disabled = 1,
        .enable_on_exec = 1,
        .exclude_kernel = 1,
        .exclude_hv = 1,
        // A compiler's threads count with it.
        .inherit = 1,
    };
    int counter = syscall(SYS_perf_event_open, &counted, child, -1, -1, 0);
    // The branches beside them: two runs with as many instructions and as
    // many branches ran the same work, wherever their code lies.
    counted.config = PERF_COUNT_HW_BRANCH_INSTRUCTIONS;
    int branching = syscall(SYS_perf_event_open, &counted, child, -1, -1, 0);
    struct timespec start, end;
    struct rusage usage;
    long peak = -1;
    if (clock_gettime(CLOCK_MONOTONIC, &start)) return 1;
    if (ptrace(PTRACE_CONT, child, 0, 0)) return 1;
    for (;;) {
        if (wait4(child, &status, 0, &usage) < 0) {
            if (errno == EINTR) continue;
            return 1;
        }
        if (!WIFSTOPPED(status)) break;
        // One of the stops asked for, or a signal on its way to the program.
        int event = status >> 16, signal = event ? 0 : WSTOPSIG(status);
        if (event == PTRACE_EVENT_SECCOMP || event == PTRACE_EVENT_EXIT) {
            long now = resident(child);
            if (now > peak) peak = now;
        }
        if (ptrace(PTRACE_CONT, child, 0, signal)) return 1;
    }
    if (clock_gettime(CLOCK_MONOTONIC, &end)) return 1;
    if (WIFSIGNALED(status)) {
        fprintf(stderr, "signal %d\n", WTERMSIG(status));
        return 128 + WTERMSIG(status);
    }
    if (WEXITSTATUS(status)) return WEXITSTATUS(status);
    uint64_t count;
    long long instructions = -1, branches = -1;
    if (counter >= 0 && read(counter, &count, sizeof count) == sizeof count) {
        instructions = (long long)count;
    }
    if (branching >= 0 && read(branching, &count, sizeof count) == sizeof count) {
        branches = (long long)count;
    }
    FILE *metrics = fopen(argv[2], "w");
    if (!metrics) return 1;
    struct timeval user = usage.ru_utime, kernel = usage.ru_stime;
    fprintf(metrics, "%lld %ld %lld %lld %lld\n",
            (end.tv_sec - start.tv_sec) * 1000000000LL + end.tv_nsec - start.tv_nsec,
            peak < 0 ? usage.ru_maxrss : peak, instructions,
            (user.tv_sec + kernel.tv_sec) * 1000000000LL + (user.tv_usec + kernel.tv_usec) * 1000LL,
            branches);
    return fclose(metrics) == 0 ? 0 : 1;
}
