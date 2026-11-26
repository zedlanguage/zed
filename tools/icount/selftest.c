/* The self-test of the DynamoRIO client zed_icount (zed_icount.c), run by build.sh under the
 * client it just built, and the workload the instruction counters were compared on
 * (row BENCH-vm-no-instruction-counter; numbers in the comment at zed_tests::scaling::Meter::new).
 *
 *   selftest            checks the client's counts; exit 0 when they hold, 1 when one fails, 3
 *                       when no software counter answers (not run under the client)
 *   selftest work <n>   sorts n pseudo-random numbers by insertion (Θ(n²) instructions) and
 *                       prints the count the client gives for it, or -1 without the client
 *
 * The checks:
 * 1. Exactness: the loop `dec rcx; jnz` runs 2k instructions for k iterations, plus a fixed
 *    number around it, so the difference of the counts of k2 and k1 iterations is exactly
 *    2 (k2 - k1). The hardware counter gives the same difference; a client that counted a block
 *    once per trace, or lost counts across the code cache's traces, does not.
 * 2. Repeat: the same loop counted twice gives the same count.
 * 3. Threads: a thread started and joined between two reads adds its own loop's 2k
 *    instructions and the fixed costs of its start and end, which are below 10^6 instructions
 *    (pthread_create and the thread's exit run a few thousand); a client that did not fold an
 *    ended thread into its parent adds about nothing, and fails.
 * 4. Switching (FAIL-bench-pieces-past-limit-on-main): the call with ZED_ICOUNT_KEY_SET answers
 *    the state before it, 1 after a read and 0 after a switch off; a loop of 2 k2 instructions
 *    run while counting is off adds under 10^4 to two reads around it that switch it back on
 *    before the second read; and the loop counted after it ran while off counts exactly what it
 *    counted before (check 1's d1), so the block built while off is not run after the switch
 *    on. A client that kept the blocks built while off would count about 0 there, and fails.
 * 5. Child processes (ICOUNT-child-processes; zed_icount.c, "Child processes"): a child that
 *    fork starts, runs check 1's loop of k iterations and ends, reaped by waitpid between two
 *    reads, adds 2k and its fixed costs, so the difference for k2 and k1 is 2 (k2 - k1) within
 *    10^4; and a child that posix_spawn starts, running this program as `selftest spin <k>`,
 *    which makes no read, adds the same within 10^5 (the program's start under DynamoRIO is in
 *    both counts). The second needs the count carried through the execve with counting on. The
 *    old client, which counted no child, gave about 0 for both differences.
 *
 *   selftest spin <k>   runs check 1's loop of k iterations and makes no read (check 5)
 */

#define _GNU_SOURCE
#include <pthread.h>
#include <spawn.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>

#define ZED_ICOUNT_SYSNUM 0x5a45
#define ZED_ICOUNT_KEY 0x7a6564696e73ULL
#define ZED_ICOUNT_KEY_SET 0x7a6564736574ULL

static long
count(void)
{
    return syscall(ZED_ICOUNT_SYSNUM, ZED_ICOUNT_KEY);
}

/* Turns counting on (1) or off (0); answers the state before. */
static long
set_counting(long on)
{
    return syscall(ZED_ICOUNT_SYSNUM, ZED_ICOUNT_KEY_SET, on);
}

/* Not inlined, so that every call runs the one block of check 4. */
static __attribute__((noinline)) void
spin(uint64_t k)
{
    __asm__ volatile("1: dec %0\n\tjnz 1b" : "+r"(k) : : "cc");
}

static long
counted_spin(uint64_t k)
{
    long a = count();
    spin(k);
    long b = count();
    return b - a;
}

static void *
thread_spin(void *arg)
{
    spin((uint64_t)(uintptr_t)arg);
    return NULL;
}

static long
counted_thread(uint64_t k)
{
    pthread_t t;
    long a = count();
    if (pthread_create(&t, NULL, thread_spin, (void *)(uintptr_t)k) != 0 ||
        pthread_join(t, NULL) != 0) {
        perror("pthread");
        exit(1);
    }
    long b = count();
    return b - a;
}

/* Check 5: a child that fork starts runs the loop and ends; reaped between the two reads. */
static long
counted_fork(uint64_t k)
{
    long a = count();
    pid_t p = fork();
    if (p == 0) {
        spin(k);
        _exit(0);
    }
    if (p < 0 || waitpid(p, NULL, 0) != p) {
        perror("fork");
        exit(1);
    }
    long b = count();
    return b - a;
}

/* Check 5: this program, `self`, started by posix_spawn as `self spin <k>`. */
static long
counted_spawn(const char *self, uint64_t k)
{
    char arg[32];
    snprintf(arg, sizeof(arg), "%llu", (unsigned long long)k);
    char *args[] = {(char *)self, "spin", arg, NULL};
    pid_t p;
    long a = count();
    if (posix_spawn(&p, self, NULL, NULL, args, environ) != 0 || waitpid(p, NULL, 0) != p) {
        perror("posix_spawn");
        exit(1);
    }
    long b = count();
    return b - a;
}

static int failures;

static void
check(int ok, const char *what, long got, long want)
{
    printf("%s %s: got %ld, want %ld\n", ok ? "ok" : "FAILED", what, got, want);
    failures += !ok;
}

static void
work(long n)
{
    uint32_t *a = malloc(n * sizeof(*a));
    uint32_t x = 12345;
    for (long i = 0; i < n; i++) {
        x = x * 1103515245u + 12345u;
        a[i] = x;
    }
    for (long i = 1; i < n; i++) {
        uint32_t v = a[i];
        long j = i;
        while (j > 0 && a[j - 1] > v) {
            a[j] = a[j - 1];
            j--;
        }
        a[j] = v;
    }
    volatile uint32_t sink = a[n / 2];
    (void)sink;
    free(a);
}

int
main(int argc, char **argv)
{
    if (argc == 3 && strcmp(argv[1], "work") == 0) {
        long a = count();
        work(atol(argv[2]));
        long b = count();
        printf("%ld\n", a < 0 ? -1 : b - a);
        return 0;
    }
    if (argc == 3 && strcmp(argv[1], "spin") == 0) {
        spin(strtoull(argv[2], NULL, 10));
        return 0;
    }
    if (count() < 0) {
        printf("no software counter (not run under zed_icount)\n");
        return 3;
    }
    long k1 = 1000000, k2 = 9000000;
    /* Warm the code cache: the first run of a block builds it. */
    counted_spin(k1);
    counted_thread(k1);
    long d1 = counted_spin(k1), d2 = counted_spin(k2), d1b = counted_spin(k1);
    check(d2 - d1 == 2 * (k2 - k1), "exactness: count(k2) - count(k1) = 2 (k2 - k1)", d2 - d1,
          2 * (k2 - k1));
    check(d1 == d1b, "repeat: two counts of the same loop", d1b, d1);
    long t0 = counted_thread(1), t1 = counted_thread(k2);
    /* The start and end of a thread take a few more or fewer instructions from one run to the
     * next (glibc's cache of thread stacks, futex waits), hence the margin of 10^4. */
    check(labs(t1 - t0 - 2 * (k2 - 1)) < 10000,
          "threads: a joined thread's loop counts in the reader (within 10^4)", t1 - t0,
          2 * (k2 - 1));
    check(t0 > 0 && t0 < 1000000, "threads: a thread's fixed costs are below 10^6", t0, 0);
    long on = set_counting(0), off = set_counting(0);
    check(on == 1 && off == 0, "switching: the state before, after a read and after a switch off",
          on * 10 + off, 10);
    long a = count();
    set_counting(0);
    spin(k2);
    set_counting(1);
    long b = count();
    check(b - a < 10000, "switching: a loop run while off is not counted (under 10^4)", b - a,
          0);
    set_counting(0);
    spin(k1);
    long d1c = counted_spin(k1);
    check(d1c == d1, "switching: a loop first run while off counts as before once on", d1c, d1);
    /* Warm, as above; the switch-off just before is turned back on by the reads. */
    counted_fork(k1);
    long f1 = counted_fork(k1), f2 = counted_fork(k2);
    check(labs(f2 - f1 - 2 * (k2 - k1)) < 10000,
          "processes: a forked child's loop counts in the parent that reaps it (within 10^4)",
          f2 - f1, 2 * (k2 - k1));
    counted_spawn(argv[0], k1);
    long s1 = counted_spawn(argv[0], k1), s2 = counted_spawn(argv[0], k2);
    check(labs(s2 - s1 - 2 * (k2 - k1)) < 100000,
          "processes: a spawned program's loop counts in the parent that reaps it (within 10^5)",
          s2 - s1, 2 * (k2 - k1));
    return failures != 0;
}
