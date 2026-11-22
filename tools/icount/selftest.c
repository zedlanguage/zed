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
 */

#define _GNU_SOURCE
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/syscall.h>
#include <unistd.h>

#define ZED_ICOUNT_SYSNUM 0x5a45
#define ZED_ICOUNT_KEY 0x7a6564696e73ULL

static long
count(void)
{
    return syscall(ZED_ICOUNT_SYSNUM, ZED_ICOUNT_KEY);
}

static void
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
    return failures != 0;
}
