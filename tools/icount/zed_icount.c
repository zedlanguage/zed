/* zed_icount: a DynamoRIO client that counts the instructions a program executes in user mode,
 * per thread, and answers a read from the program with the count of the calling thread and of
 * the threads it started that have ended. It stands in for the hardware counter on machines
 * that have none (row BENCH-vm-no-instruction-counter: Colab VMs list no `cpu` event source),
 * so that the scaling tests (zed_tests::scaling, Meter::new) count instructions there too.
 *
 * Built by tools/icount/build.sh against a DynamoRIO release; started by the crate
 * zed-meter-settings (start_under_dynamorio), which a scaling test's meter calls to run its
 * test binary again under `drrun -c libzed_icount.so --` when the hardware counter is missing.
 *
 * Prior work (checked 2026-11-22):
 * - DynamoRIO: D. Bruening, T. Garnett, S. Amarasinghe, "An infrastructure for adaptive
 *   dynamic optimization", CGO 2003, doi:10.1109/CGO.2003.1191551 (Crossref metadata read;
 *   the paper's text was not). DynamoRIO copies each basic block of the program into a code
 *   cache before it runs it and lets a client add instructions to the copy.
 * - The counting is the method of DynamoRIO's sample client samples/inscount.cpp of release
 *   11.3.0 (read in full, 2026-11-22): at the first instruction of each block, add the number
 *   of the block's application instructions to a counter, where an emulated instruction counts
 *   once and the instructions DynamoRIO adds to emulate it do not. The sample adds with a clean
 *   call to one global counter, which threads race on; here the add is one inline instruction,
 *   `add qword [tls slot], n`, on a counter of the thread's own (a raw TLS slot,
 *   dr_raw_tls_calloc, "initialized to 0 for each new thread", dr_tools.h of 11.3.0), with the
 *   arithmetic flags saved around it by drreg when they are live. An add placed at the first
 *   instruction of the block where the flags are dead, so that drreg saves nothing, was measured
 *   and gave the same counts and times (module comment of zed_tests::scaling, with the cost).
 * - The alternatives measured and scored are in the handoff of b22-meter1 and in the module
 *   comment of zed_tests::scaling: valgrind (N. Nethercote, J. Seward, PLDI 2007,
 *   doi:10.1145/1250734.1250746), QEMU user mode with its TCG plugin libinsn.so, and Intel
 *   SDE / Pin (C.-K. Luk et al., PLDI 2005, doi:10.1145/1065010.1065034; not free software).
 *
 * What is counted, and how it differs from the hardware counter (perf's `instructions:u` with
 * `inherit`, which Meter::new reads where it exists):
 * - Each application instruction executed in user mode counts 1, as the hardware counts it.
 *   A `rep`-prefixed string instruction counts 1 per execution here; the hardware also counts
 *   it about once. The scaling meter keeps glibc from `rep movsb` and `rep stosb` for that
 *   reason (zed_meter_settings::GLIBC_TUNABLES), so the two agree there as well.
 * - A block is counted as it is entered, whole. A block left in the middle (a fault, a signal)
 *   counts the instructions after the point it left; no test of this workspace faults in a
 *   measured run.
 * - Threads. perf's counter opened with `inherit` counts the opening thread and every thread
 *   started after the opening by it or by those threads; a started thread's count joins the
 *   counter when that thread ends (kernel/events/core.c, perf_event_exit_task and
 *   sync_child_event, from memory of the kernel source; checked by the behavior Meter relies
 *   on: a run that starts and joins threads counts their work, test
 *   scaling_tests::a_run_counts_the_threads_it_starts). Here a read answers the calling
 *   thread's own count plus the totals of its ended descendants, as the tree below folds them:
 *   when a thread ends, its total (own count plus what its ended descendants gave it) is added
 *   to its nearest ancestor that has not ended. So the two agree on the use Meter makes of
 *   them, a difference of two reads around a run that joins the threads it starts. They differ
 *   (1) for a thread started before the first read and ended between two reads, which perf does
 *   not count and this does; (2) for a grandchild that ended while its parent still runs, which
 *   perf counts at once and this only when the parent ends; (3) for child processes, which perf
 *   counts when they end and this never does (each process under DynamoRIO counts alone).
 *   The scaling harness meets none of the three: a run's threads are started inside the run and
 *   joined before it returns, and a run starts no process (a check's run at 8n in a new process
 *   is measured by that process's own meter).
 *
 * The read. The program makes the system call ZED_ICOUNT_SYSNUM with first argument
 * ZED_ICOUNT_KEY. Under this client the call never reaches the kernel: the pre-syscall event
 * answers the count as the call's result and skips it. Natively the kernel has no system call
 * of that number and answers -ENOSYS (or -EPERM under a seccomp filter that refuses unknown
 * calls), which the program reads as "no software counter". The number is below 2^30, so it is
 * not an x32 call, and above every number Linux has used (under 500 in 2026), so a kernel
 * release that adds calls will not reach it soon; a call with another first argument is passed
 * to the kernel unchanged.
 */

#include "dr_api.h"
#include "drmgr.h"
#include "drreg.h"
#include "hashtable.h"

#include <stdint.h>
#include <sys/syscall.h>

#define ZED_ICOUNT_SYSNUM 0x5a45      /* "ZE"; also in zed_alloc_count::os::software_instructions */
#define ZED_ICOUNT_KEY 0x7a6564696e73ULL /* "zedins"; the same */
#ifndef CLONE_THREAD
#    define CLONE_THREAD 0x00010000
#endif

/* The raw TLS slot that holds each thread's own count. */
static reg_id_t tls_seg;
static uint tls_offs;
/* The drmgr TLS field that holds each thread's node. */
static int node_field;

/* A thread, for the folding of ended threads' totals into their ancestors. The nodes and the
 * table are guarded by `lock`. A node is never freed (a few dozen bytes per thread the process
 * ever starts), so a pointer to it stays valid; a thread's tid is in `by_tid` from the first of
 * its own start and its parent's return from clone until its total has been passed up. */
typedef enum { NODE_LIVE, NODE_WAITING, NODE_ENDED } node_state_t;
typedef struct node {
    thread_id_t tid;
    struct node *parent; /* NULL while unknown, and for the first thread */
    bool parent_known;
    node_state_t state;
    /* Totals of ended descendants passed to this node, and after it ends, its own count too. */
    uint64 acc;
    /* The thread's own counter while it runs; NULL before its start event. */
    volatile uint64 *own;
    /* clone flags saved by the pre-syscall event for the post-syscall event. */
    uint64 clone_flags;
} node_t;

static void *lock;
static hashtable_t by_tid;

static node_t *
node_create(thread_id_t tid)
{
    node_t *n = dr_global_alloc(sizeof(*n));
    n->tid = tid;
    n->parent = NULL;
    n->parent_known = false;
    n->state = NODE_LIVE;
    n->acc = 0;
    n->own = NULL;
    n->clone_flags = 0;
    hashtable_add(&by_tid, (void *)(ptr_uint_t)tid, n);
    return n;
}

/* The node that an ended thread's total goes to: the nearest ancestor of `n` that still runs or
 * waits for its own parent to become known. NULL when there is none (every ancestor ended and
 * passed its total up as far as it could, or the first thread ended); the total is then of no
 * thread that can read it.
 *
 * Why a total reaches every reader that perf's counter would show it to, for runs that join
 * their threads (the claim in the file comment): a thread T that reads, and a descendant D of T
 * started after T's first read. When D ends, its total goes to its nearest ancestor A that has
 * not ended; A is T or a descendant of T (T has not ended: it reads later). If A is not T, A
 * ends before T's later read (the run joins its threads), and then its total, which holds D's,
 * goes up the same way. Each step goes one ancestor or more up the chain from D to T, which is
 * finite, so D's count is in T's acc by T's read. A node that waits (ended before its parent's
 * clone returned) is passed up when the clone returns (event_post_syscall), which is before the
 * parent can join it. Caller holds `lock`. */
static node_t *
fold_target(node_t *n)
{
    node_t *p = n->parent;
    while (p != NULL && p->state == NODE_ENDED)
        p = p->parent;
    return p;
}

static void
event_thread_init(void *drcontext)
{
    thread_id_t tid = dr_get_thread_id(drcontext);
    dr_mutex_lock(lock);
    node_t *n = hashtable_lookup(&by_tid, (void *)(ptr_uint_t)tid);
    if (n == NULL)
        n = node_create(tid);
    n->own = (volatile uint64 *)(dr_get_dr_segment_base(tls_seg) + tls_offs);
    dr_mutex_unlock(lock);
    drmgr_set_tls_field(drcontext, node_field, n);
}

static void
event_thread_exit(void *drcontext)
{
    /* After a fork, DynamoRIO calls this in the child for each thread the child did not keep
     * (dr_events.h of 11.3.0, dr_register_thread_exit_event); those threads still run in the
     * parent, so nothing is passed up here. */
    if (dr_get_process_id() != dr_get_process_id_from_drcontext(drcontext))
        return;
    node_t *n = drmgr_get_tls_field(drcontext, node_field);
    if (n == NULL)
        return;
    dr_mutex_lock(lock);
    n->acc += *n->own;
    n->own = NULL;
    if (!n->parent_known) {
        /* Ended before its parent's clone returned: wait there (the first thread waits for
         * ever, which is harmless: nothing reads it). */
        n->state = NODE_WAITING;
    } else {
        n->state = NODE_ENDED;
        node_t *to = fold_target(n);
        if (to != NULL)
            to->acc += n->acc;
        hashtable_remove(&by_tid, (void *)(ptr_uint_t)n->tid);
    }
    dr_mutex_unlock(lock);
}

static bool
event_filter_syscall(void *drcontext, int sysnum)
{
    return sysnum == ZED_ICOUNT_SYSNUM || sysnum == SYS_clone
#ifdef SYS_clone3
        || sysnum == SYS_clone3
#endif
        ;
}

static bool
event_pre_syscall(void *drcontext, int sysnum)
{
    node_t *n = drmgr_get_tls_field(drcontext, node_field);
    if (sysnum == ZED_ICOUNT_SYSNUM) {
        if ((uint64)dr_syscall_get_param(drcontext, 0) != ZED_ICOUNT_KEY || n == NULL)
            return true;
        dr_mutex_lock(lock);
        uint64 count = *n->own + n->acc;
        dr_mutex_unlock(lock);
        dr_syscall_set_result(drcontext, (reg_t)count);
        return false; /* skip the call: the result is the count */
    }
    if (n == NULL)
        return true;
    if (sysnum == SYS_clone) {
        /* x86_64: clone(flags, stack, parent_tid, child_tid, tls). */
        n->clone_flags = (uint64)dr_syscall_get_param(drcontext, 0);
    }
#ifdef SYS_clone3
    else if (sysnum == SYS_clone3) {
        /* clone3(struct clone_args *args, size_t size); `flags` is the first u64 of args. */
        uint64 flags = 0;
        size_t got = 0;
        if (!dr_safe_read((void *)dr_syscall_get_param(drcontext, 0), sizeof(flags), &flags,
                          &got) ||
            got != sizeof(flags))
            flags = 0;
        n->clone_flags = flags;
    }
#endif
    return true;
}

static void
event_post_syscall(void *drcontext, int sysnum)
{
    if (sysnum != SYS_clone
#ifdef SYS_clone3
        && sysnum != SYS_clone3
#endif
    )
        return;
    node_t *me = drmgr_get_tls_field(drcontext, node_field);
    if (me == NULL || (me->clone_flags & CLONE_THREAD) == 0)
        return;
    ptr_int_t result = (ptr_int_t)dr_syscall_get_result(drcontext);
    if (result <= 0)
        return; /* failed, or the new thread's own return */
    thread_id_t child = (thread_id_t)result;
    dr_mutex_lock(lock);
    node_t *c = hashtable_lookup(&by_tid, (void *)(ptr_uint_t)child);
    if (c == NULL)
        c = node_create(child); /* its start event has not run yet; it finds this node */
    c->parent = me;
    c->parent_known = true;
    if (c->state == NODE_WAITING) {
        /* It ended before this return: pass its total up now (fold_target's argument). */
        c->state = NODE_ENDED;
        me->acc += c->acc;
        hashtable_remove(&by_tid, (void *)(ptr_uint_t)child);
    }
    dr_mutex_unlock(lock);
}

static void
event_fork_init(void *drcontext)
{
    /* The child of a fork has one thread, and the lock may have been held by a thread the
     * child did not keep: make a new one. The nodes of the other threads stay and are never
     * read. */
    lock = dr_mutex_create();
}

static dr_emit_flags_t
event_bb_analysis(void *drcontext, void *tag, instrlist_t *bb, bool for_trace,
                  bool translating, void **user_data)
{
    /* As samples/inscount.cpp of DynamoRIO 11.3.0 counts (file comment). */
    uint count = 0;
    bool is_emulation = false;
    for (instr_t *instr = instrlist_first(bb); instr != NULL; instr = instr_get_next(instr)) {
        if (drmgr_is_emulation_start(instr)) {
            count++;
            is_emulation = true;
            continue;
        }
        if (drmgr_is_emulation_end(instr)) {
            is_emulation = false;
            continue;
        }
        if (is_emulation || !instr_is_app(instr))
            continue;
        count++;
    }
    *user_data = (void *)(ptr_uint_t)count;
    return DR_EMIT_DEFAULT;
}

static dr_emit_flags_t
event_app_instruction(void *drcontext, void *tag, instrlist_t *bb, instr_t *instr,
                      bool for_trace, bool translating, void *user_data)
{
    if (!drmgr_is_first_instr(drcontext, instr))
        return DR_EMIT_DEFAULT;
    uint count = (uint)(ptr_uint_t)user_data;
    if (count == 0)
        return DR_EMIT_DEFAULT;
    if (drreg_reserve_aflags(drcontext, bb, instr) != DRREG_SUCCESS)
        DR_ASSERT_MSG(false, "zed_icount: cannot reserve the arithmetic flags");
    opnd_t slot = dr_raw_tls_opnd(drcontext, tls_seg, tls_offs);
    opnd_set_size(&slot, OPSZ_8);
    instrlist_meta_preinsert(bb, instr,
                             INSTR_CREATE_add(drcontext, slot, OPND_CREATE_INT32(count)));
    if (drreg_unreserve_aflags(drcontext, bb, instr) != DRREG_SUCCESS)
        DR_ASSERT_MSG(false, "zed_icount: cannot restore the arithmetic flags");
    return DR_EMIT_DEFAULT;
}

static void
event_exit(void)
{
    drmgr_unregister_tls_field(node_field);
    dr_raw_tls_cfree(tls_offs, 1);
    drreg_exit();
    drmgr_exit();
}

DR_EXPORT void
dr_client_main(client_id_t id, int argc, const char *argv[])
{
    dr_set_client_name("zed_icount: instructions per thread for the zed scaling tests",
                       "tools/icount of zed-impl");
    drreg_options_t ops = { sizeof(ops), 1 /* slots */, false };
    if (!drmgr_init() || drreg_init(&ops) != DRREG_SUCCESS)
        DR_ASSERT_MSG(false, "zed_icount: drmgr or drreg did not start");
    if (!dr_raw_tls_calloc(&tls_seg, &tls_offs, 1, 0))
        DR_ASSERT_MSG(false, "zed_icount: no raw TLS slot");
    node_field = drmgr_register_tls_field();
    lock = dr_mutex_create();
    hashtable_init(&by_tid, 8, HASH_INTPTR, false);
    dr_register_exit_event(event_exit);
    dr_register_filter_syscall_event(event_filter_syscall);
    dr_register_fork_init_event(event_fork_init);
    if (!drmgr_register_thread_init_event(event_thread_init) ||
        !drmgr_register_thread_exit_event(event_thread_exit) ||
        !drmgr_register_pre_syscall_event(event_pre_syscall) ||
        !drmgr_register_post_syscall_event(event_post_syscall) ||
        !drmgr_register_bb_instrumentation_event(event_bb_analysis, event_app_instruction,
                                                 NULL))
        DR_ASSERT_MSG(false, "zed_icount: cannot register the events");
}
