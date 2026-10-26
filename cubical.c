/* cubical -- cube-and-conquer that decides where to split from the proof.
 *
 * Runs CaDiCaL through IPASIR and periodically checks the proof the solver is
 * emitting.  A node that splits cuts its subproblem on one variable and puts
 * both halves on the worklist, where an idle worker can take one.
 *
 * Counts come from the DRAT proof, not from ipasir_set_learn: the proof also
 * carries what pre- and inprocessing derive, and the two streams disagree
 * sharply.  Deletions are ignored.  The learn callback is kept only for its
 * per-clause count, the one way to get a per-node conflict count out of either
 * API.
 *
 * Scoring.  Every proof clause carries weight 1 shared evenly over its
 * literals, so an occurrence in a clause of k is worth 1/k:
 *
 *     score(v) = the weights of the occurrences of v and -v, combined
 *     cover(v) = score(v) / N     the share of the collected proof's weight
 *                                 that restricting on v removes
 *
 * The covers of all variables sum to exactly 1, which is what makes two
 * variables at one node comparable.  Do NOT normalise cover by anything that
 * grows with the variable count: the denominator vanishes on wide instances
 * and inverts the ordering.
 *
 * That sum ignores which polarity carries the weight, and a variable whose
 * occurrences are all of one sign removes nothing from the other branch.  -t
 * combines the two polarity weights by their power mean of order t rather than
 * adding them: t=1 the sum, t=0 the geometric mean, t=-inf the minimum.  Below
 * 1 the score is the cover times a penalty for one-sided weight, steeper the
 * lower t goes.  score_of has the details.
 *
 * Two phases.  The same sum is a poor absolute threshold -- it is a share of a
 * node's own proof, so what counts as a large one varies with how wide the
 * instance is -- so nothing here thresholds it against a constant.
 *
 *   Phase 1, the ramp.  Every node above depth ceil(log2(--cores)) runs for
 *   --ramp-conflicts conflicts and then splits on its best variable, whatever
 *   that variable scores.  The top of the tree is therefore a complete binary
 *   tree with a cube per core, so the workers fill by construction -- and the
 *   d scores it measures, all at the same budget on the same instance, are the
 *   sample the next phase calibrates against.
 *
 *   Phase 2, the percentile.  Below the ramp a node splits only once its best
 *   variable beats the --percentile-th percentile of the scores its ancestors
 *   split on.  The bar comes from the instance rather than from a constant, it
 *   rises as a path accumulates good ancestors, and one unusually good
 *   ancestor moves a percentile far less than it would move a maximum.
 *
 * --max-depth stops splitting outright; a node there still solves to a
 * verdict.  --trace prints every poll and acts on none of them.
 *
 * Inheritance.  A child starts from the parent's proof rather than from zero,
 * so a split is decided on the whole path's evidence: CaDiCaL propagates the
 * cube, the clauses it satisfies drop out, the ones it trims get re-weighted,
 * and what survives seeds the child.  --carry-mb bounds what one node holds.
 *
 * Cadence.  Every node polls once the instant it starts, on the set it just
 * inherited -- that is the var0 column, and in phase 2 it is also the first
 * poll that may split, so a node holding enough inherited proof splits without
 * spending a conflict on it.  After that a ramp node jumps straight to its
 * budget and a phase-2 node re-checks every --poll-every conflicts.  Checks
 * are cheap: the counts are maintained incrementally and evaluate () is one
 * pass over the touched variables.
 *
 * Acting is floored in clauses: --min-split refuses a split on a set holding
 * fewer, whatever the cadence says, since a node can burn conflicts without
 * the proof growing.  cs_evict never drops a set below the floor either, or
 * capping one under it would make every check refuse for good.
 *
 * README.md covers what the defaults were measured on and which to move first.
 */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <limits.h>
#include <errno.h>
#include <time.h>
#include <stdarg.h>
#include <unistd.h>
#include <fcntl.h>
#include <signal.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <sys/resource.h>
#include "ipasir.h"

/* Printed into every log's banner.  The runner names its log files after this,
 * but it cannot check them: the name is written by the script, not the binary,
 * so a stale build would produce logs claiming a version it is not.  That
 * matters here because versions 4 and 5 differ only by a factor of 2 on min
 * and geo -- the output of the wrong one is entirely plausible, just at half
 * the cover it claims.  Emitting it makes every log self-identifying and lets
 * collect.py cross-check the name against the run.  Since 6 the banner carries
 * -t as well, for the same reason: a sweep's cells differ in nothing else. */
#define CUBICAL_VERSION "10"

/* ccadical.h types its handle as CCaDiCaL *, but IPASIR hands back a void *;
 * declaring the few we need keeps the casts out of every call site. */
extern void ccadical_set_option (void *, const char *, int);
extern int  ccadical_get_option (void *, const char *);
extern int  ccadical_trace_proof (void *, FILE *, const char *);
extern void ccadical_close_proof (void *);
extern int  ccadical_fixed (void *, int);
extern int  ccadical_vars (void *);

/* cshim.cpp: CaDiCaL's own unit propagation, which is stronger than
 * propagating over the CNF ourselves -- it also uses everything the shared
 * solver learned at earlier nodes.  vars() and fixed() are only there so
 * init_counts can check the shim's layout assumption. */
extern int cubical_set_option (void *, const char *, int);
extern int cubical_propagate (void *);
extern int cubical_implied (void *, int *, int);
extern int cubical_fixed (void *, int);
extern int cubical_vars (void *);

/* Set a CaDiCaL option, or die saying which one and why.
 *
 * Every option here is load-bearing, which is why none of them is set through
 * ccadical_set_option: that discards Solver::set's answer, so a name CaDiCaL
 * does not have is accepted in silence.  "binary" is the clearest case -- the
 * DRAT reader in this file parses text, so a silently ignored binary=0 would
 * have it counting the bytes of a binary proof as if they were digits, and
 * every score in the run would be noise that looks like a number.
 *
 * Returns 0 on success so the caller can unwind its own allocations. */
static int set_option (void *solver, const char *name, int val)
{
    /* Two checks, because each catches what the other misses.
     *
     * set() returns false for a name CaDiCaL does not have, which reading the
     * value back cannot detect: get_option answers 0 for an unknown name, so
     * "--opt luckyy=0" reads back as exactly the 0 that was asked for.
     *
     * set() returns TRUE for a value outside the option's range, and silently
     * leaves the option where it was -- "--opt lucky=99" comes back as
     * lucky=1, the default, with lucky phases still on.  Only the read-back
     * sees that. */
    if (!cubical_set_option (solver, name, val)) {
        fprintf (stderr, "cubical: CaDiCaL has no option '%s'.\n", name);
        fprintf (stderr, "  Check the spelling against `cadical --help`."
                 "  Refusing to run rather than\n  measure a configuration"
                 " that is not the one asked for.\n");
        return -1;
    }
    int got = ccadical_get_option (solver, name);
    if (got != val) {
        fprintf (stderr, "cubical: %s=%d did not take -- CaDiCaL reports"
                 " %s=%d.\n", name, val, name, got);
        fprintf (stderr, "  %d is outside that option's range, so the value"
                 " was left alone.  Refusing\n  to run rather than measure a"
                 " configuration that is not the one asked for.\n", val);
        return -1;
    }
    return 0;
}

/* ------------------------------------------------------------- options -- */

/* ---- phase 1: the ramp --------------------------------------------------
 *
 * Every node shallower than the ramp depth runs for --ramp-conflicts
 * conflicts and then splits on its best-scoring variable, whatever that
 * variable scores.  No threshold applies, so the top of the tree has a fixed
 * shape: a complete binary tree of depth d, hence 2^d subproblems.
 *
 * Two things come out of that.  One is occupancy: every split hands a cube to
 * the shared queue and an idle worker takes it, so the pool fills by
 * construction after d levels rather than after however long a threshold
 * takes to trip.  The other is a sample -- d scores measured on THIS instance
 * at a fixed budget, which is what phase 2's threshold is a percentile of, so
 * nothing has to be calibrated from outside the run.
 *
 * A ramp node still carries its parent's reduced proof in, so its k conflicts
 * are spent on top of the whole path's evidence rather than instead of it.
 * What the budget buys is a view of the subproblem taken at the same cost at
 * every node, which is what makes the d scores comparable to each other.
 *
 * The depth is a function of the core count -- ceil(log2(--cores)), so 32
 * cores ramp to depth 5 and one core ramps not at all -- because the point of
 * the phase is to fill the workers.  --ramp-depth overrides it for an
 * ablation; --ramp-depth 0 turns the phase off entirely. */
static long long opt_rampk = 100000;
static int opt_rampdepth = -1;         /* -1: derive it from --cores */
/* The depth phase 1 ends at: enough levels for the ramp alone to produce a
 * cube per core, which is ceil(log2(cores)).  Derived once, in check_opts,
 * because node_begin reads it per node and --ramp-depth may override it. */
static int g_ramp;

/* ---- phase 2: the percentile --------------------------------------------
 *
 * At or below the ramp depth a node splits only once its best variable's
 * score beats the p-th percentile of the scores its ANCESTORS split on.
 * p = 50 is the median.
 *
 * So the bar is set by the instance and not by a constant: the sample starts
 * as the ramp's measurements and grows by one at every level below it.  It
 * also rises as a path accumulates good ancestors, which is what bounds the
 * depth of the tree -- and a percentile moves far less on one unusually high
 * ancestor than a maximum or a mean would, so a single outlier cannot stop a
 * branch for good.
 *
 * A node with no ancestor scores -- the root -- has a bar of 0, and splits at
 * the first poll that clears --min-split.
 *
 * The scores are kept as floats, in the cube, and so travel with a donated
 * cube like its literals do.  Single precision is six digits more than a
 * comparison against a percentile can use, and it halves what a donation of a
 * deep cube has to copy. */
static int opt_pct = 50;
static int pct_given = 0;      /* so --cover can refuse to share the gate     */

/* The absolute alternative to the percentile: split when the best score beats
 * this, full stop, with no reference to what the path did above.
 *
 * Expressed as a percentage, so it is read in the same units the log's cover%
 * and bar% columns print -- "--cover 2" is the bar the row shows as 2.000.
 * And it is a bar on the SCORE, which is cover times the -t balance factor, so
 * it only means raw proof coverage at -t 1.  cover% is what it is compared
 * against, so matching that column is the useful definition.
 *
 * Why it is worth having, given that the percentile replaced it: the two ask
 * genuinely different questions, and the percentile's weakness is structural
 * rather than a matter of tuning.  Its sample is the path's own ancestors, so
 * at depth 1 the sample is one number and the bar IS the parent's score at any
 * p -- every root split is therefore followed by a child that must beat its
 * parent exactly, which is where the three-node trees come from.  An absolute
 * bar has no such degenerate case and no dependence on depth.  What it gives
 * up is the thing the percentile was introduced for: covers at a node sum to
 * 1, so the mean cover is 1/(variables touched) and a constant bar means
 * something different on a 300-variable formula than on a 30000-variable one.
 * One is instance-relative and blind at depth 1; the other is scale-sensitive
 * and uniform.  Which trade wins is a question for a sweep, which is why both
 * are here rather than one.
 *
 * Negative means unset: the percentile is the default, and the two are refused
 * together rather than silently ordered. */
static double opt_cover = -1.0;

/* The order of the power mean combining a variable's two polarity weights.
 * 1 is the arithmetic mean, which is the plain cover; see score_of. */
static double opt_t = 0.0;        /* -inf .. inf  (0 = geo)                  */
static int    opt_learn = 1;      /* add the negated core of each refutation */
static int    opt_maxdepth = 1000;/* splitting stops here; solving does not  */
/* Let --max-depth yield to demand: a node at the cap may still split while a
 * worker is actually idle.
 *
 * The cap exists to stop paying for splits that buy nothing, and that cost is
 * duplicated WORK -- each child re-derives part of its parent's proof.  Work
 * only matters when the cores are saturated.  With a core idle the trade is
 * different: both children are at least as constrained as the parent, so
 * (bar the split's own overhead) the longest branch can only get shorter,
 * while not splitting leaves that core idle for the rest of the subproblem.
 *
 * Self-limiting, which is why it needs no second ceiling: at most `want`
 * extra splits are licensed at any moment and each one immediately feeds the
 * worker that asked, so `want` falls as they are taken.  Depth is bounded in
 * any case by the variable count -- a cube cannot name a variable twice.
 *
 * Off by default: the cap means one thing or the other, and a run should not
 * have to guess which. */
static int    opt_splitidle = 0;
static int    opt_seed  = 0;      /* forwarded to CaDiCaL's own 'seed'       */
static int    opt_cores = 1;      /* 1 keeps the run exactly sequential      */
static int    opt_share = 1;      /* workers trade refutation cores          */
static int    opt_quiet = 0;
static int    opt_trace = 0;      /* print every poll, never split           */

/* How often the phase-2 criterion is re-asked, in conflicts.
 *
 * Every node also polls once the instant it starts, whatever its phase.  That
 * poll is what records the argmax on the parent's reduced proof before this
 * node has derived anything of its own -- the var0 column -- and in phase 2 it
 * is also the first poll that may split, so a node that already holds enough
 * inherited evidence splits without spending a conflict on it.  After it, a
 * phase-1 node jumps straight to --ramp-conflicts and a phase-2 node
 * re-checks on this cadence until it splits or closes. */
static long long opt_pollint = 10000;

/* The floor on the evidence any split may be decided on, in clauses of
 * collected proof -- inherited and derived alike, since the score is read off
 * the whole set.  Also the floor eviction may never drop a set below: a set
 * capped under it would make every later check refuse for good. */
static long long opt_minsplit = 100000;
static const char *opt_log = NULL;

/* Directory for the DRAT trace; resolved by proof_dir ().  Wants to be a
 * tmpfs, since drain_proof keeps the file resident and punches out what it has
 * consumed.  A container typically caps /dev/shm at 64MB. */
static const char *opt_proofdir = NULL;

/* A ceiling that fires in normal use is not a safety valve: xai-mindset2
 * carries 20.4M clauses (~1.2GB) in the run that solves it, so anything under
 * that silently changes the search -- and the process holds about one set per
 * level of depth.  This bounds what a set may *allocate*, not what it holds:
 * growth stops dead at it rather than doubling past (see cs_reserve), which is
 * what turned an earlier 2GB ceiling into 4GB resident.  The realloc that
 * reaches it needs both buffers, so the transient peak is about 1.7x. */
static long long opt_cap = 2048LL << 20;   /* bytes per set, --carry-mb */

/* What one occurrence in a clause of `len` literals contributes to its
 * variable's score: the clause carries weight 1 and shares it out.  Every
 * increment and decrement of the counts goes through here, and each must use
 * the length the clause had when it was counted -- for an inherited clause
 * that is its *reduced* length, so cs_reduce weights the survivors only once
 * it knows how many there are. */
static double lit_weight (int len)
{
    return 1.0 / (double) len;
}

static int var_of (int lit) { return lit < 0 ? -lit : lit; }

/* ----------------------------------------------------------- plumbing -- */

struct Cube;   /* a worklist entry; defined with the worklist further down */

/* Ctrl-C (or SIGTERM) should still produce a result line and the summary, not
 * a silent death: the handler only raises a flag, on_terminate turns it into
 * an interrupt, and the run reports UNKNOWN through the normal path. */
typedef struct Stats Stats;

/* The only state the workers share.  next hands out the initial cube and stop
 * ends the run early once one of them has a verdict.  Everything else a worker
 * touches is its own copy-on-write image of the parent.
 *
 * The per-worker Stats live in the same mapping, immediately after this
 * header, reached through shared_stats().  They are not a flexible member
 * because on_terminate needs this type complete and Stats is not defined until
 * much further down; pad keeps the array that follows 8-byte aligned. */
/* Room for the shared cores.  They are short -- measured across this
 * benchmark, a core is 3.7 literals at the median and 5.8 at the 90th
 * percentile -- and rare, under one per worker per second, so 8 MB holds
 * several hours of a 64-worker run.  It does not wrap: once full, publishing
 * stops.  Losing late clauses costs some sharing, where wrapping under a
 * reader would hand that reader a clause spliced from two others. */
#define SHARE_INTS (1 << 21)

/* Slots an overloaded worker can leave a cube in for an idle one.
 *
 * A donated cube carries its inherited proof when it fits, and its ancestor
 * scores always.  The proof matters more than it looks: a phase-2 node splits
 * off what it inherited, so a cube handed over without its proof cannot
 * consider splitting until it has re-derived --min-split clauses of its own,
 * which leaves that subtree unparallelisable for as long as that takes.  The
 * set is one flat int array, so carrying it is a memcpy; past the slot it
 * falls back to literals and scores only. */
#define DON_SLOTS  8
#define DON_INTS   (1 << 19)       /* 2 MB of payload per slot */

typedef struct {
    int  state;                /* 0 empty, -1 being filled, 1 ready, -2 taken */
    int  n, depth, nanc;
    long long nmem, ncls;      /* proof ints and clauses; 0 = none carried   */
    double cp;
    /* n literals, then nanc ancestor scores as floats, then the proof if it
     * fitted.  The scores are not optional the way the proof is: a cube that
     * arrived without them would be scored against an empty sample, read a
     * bar of 0, and split on its first poll whatever it found -- so a
     * donation that cannot fit them is refused instead. */
    int  buf[DON_INTS];
} Donation;

typedef struct {
    int next, stop, result, pad;
    int shead;                 /* ints reserved so far, bumped atomically    */
    int sfull;                 /* set once a reservation ran past the end    */
    int want;                  /* workers idle and asking for a cube         */
    int active;                /* workers holding work; 0 means all done     */
    int sbuf[SHARE_INTS];      /* records of [len, worker, lit...]           */
    Donation don[DON_SLOTS];
} Shared;
static Shared *g_sh;           /* non-null only inside a parallel worker     */
static int g_wid = -1;         /* this worker's index, for skipping its own  */
static int g_scur;             /* how far this worker has read the ring      */

static volatile sig_atomic_t g_stop;
static void on_signal (int sig) { (void) sig; g_stop = 1; }

#define STATUS_EVERY 30.0        /* seconds between progress lines on stderr */

static double cpu_time (void)
{
    struct timespec ts;
    clock_gettime (CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

static FILE *g_log = NULL;        /* --cube-log target: always full output   */
static int g_litw = 2;            /* width of one cube literal, from nvars   */
static int g_tty_out, g_tty_err;  /* colour the core on a terminal only      */

/* A literal the refutation needed is green, one it did not is red -- but only
 * on a terminal: --cube-log is read with awk, where an escape sequence breaks
 * every field split, so a file gets a marker character in the same place.
 * NO_COLOR is honoured because this output is piped as often as it is read. */
#define CORE_IN  "\033[32m"
#define CORE_OUT "\033[31m"
#define CORE_OFF "\033[0m"

/* The one place a line is formatted, so the terminal and the log can never
 * disagree; "-q --cube-log f" is silent terminal plus complete file. */
static void emit (const char *fmt, ...)
{
    va_list ap;
    if (!opt_quiet) { va_start (ap, fmt); vprintf (fmt, ap); va_end (ap); }
    if (g_log)      { va_start (ap, fmt); vfprintf (g_log, fmt, ap); va_end (ap); }
}

/* Every allocation here is on a path whose documented failure mode is running
 * out of memory, and a silent NULL turns that into a segfault that loses the
 * whole run's output.  stdout and --cube-log are line-buffered, so by the time
 * this exits everything already reported is on disk. */
static void *xalloc (void *p, size_t n)
{
    void *q = realloc (p, n);
    if (!q) {
        fprintf (stderr, "cubical: out of memory asking for %zu bytes\n", n);
        fflush (stdout);
        if (g_log) fflush (g_log);
        exit (1);
    }
    return q;
}

static void *xzalloc (size_t n)
{
    void *q = xalloc (NULL, n);
    memset (q, 0, n);
    return q;
}

/* ---------------------------------------------------------- clause sets --
 * A stream of length-prefixed clauses.  Both uses are strictly sequential --
 * append while a node collects, read front to back when its children are cut
 * -- so nothing needs random access and a clause can be read in place.
 *
 * The set is bounded: left to grow it accumulates every proof clause on the
 * path from the root, which reached 1.83GB and an OOM kill on xai-mindset2.
 * Past the bound the oldest clauses are dropped and their occurrences taken
 * back out of the counts, so the counts always describe exactly what is
 * present; below it nothing is dropped, so it is a ceiling and not a tuning
 * knob.  Windowing costs nothing we can use: cover is a share, whose standard
 * error over a quarter million clauses is well under 0.1%, and what the set is
 * really for is the reduction -- when the cube satisfies a clause the others in
 * it lose coverage, demoting the variables correlated with the one just
 * branched on -- which works the same in a window as over all history. */
typedef struct {
    int      *mem;            /* the clauses, each a length then its literals */
    long long nmem, mcap;     /* ints used, ints allocated                    */
    long long rpos;           /* the sequential read cursor                   */
    long long hdr;            /* where the open clause's length goes          */
    int       nbuf;           /* literals in the open clause                  */
    long long n;              /* committed clauses                            */
    const int *cur;           /* the clause cs_next just produced             */
} ClauseSet;

/* The ceiling in ints, which is what the set counts in. */
static long long cs_budget (void) { return opt_cap / (long long) sizeof (int); }

/* Room for `k` more ints. */
static void cs_reserve (ClauseSet *s, long long k)
{
    if (s->nmem + k <= s->mcap) return;
    long long lim = cs_budget (), want = s->mcap ? s->mcap : 1 << 12;
    while (want < s->nmem + k) want += want / 2 + 1;        /* 1.5x, not 2x */
    /* Land exactly on the ceiling whenever what is asked for still fits there,
     * so the steady state allocates --carry-mb rather than up to twice it.
     * Beyond it growth continues: the --min-split floor in cs_evict can refuse to
     * drop anything, and a truncated clause would be worse than the overshoot. */
    if (want > lim && s->nmem + k <= lim) want = lim;
    s->mcap = want;
    s->mem = xalloc (s->mem, (size_t) s->mcap * sizeof (int));
}

/* Literals go straight into the set behind a reserved length slot, so
 * committing a clause costs no copy at all. */
static void cs_lit (ClauseSet *s, int l)
{
    cs_reserve (s, 2);
    if (!s->nbuf) s->hdr = s->nmem++;              /* the length slot */
    s->mem[s->nmem++] = l;
    s->nbuf++;
}

/* Commit the open clause.  One that reduced to nothing is never committed,
 * which is also the caller's rollback. */
static void cs_end (ClauseSet *s)
{
    if (!s->nbuf) return;
    s->mem[s->hdr] = s->nbuf;
    s->n++; s->nbuf = 0;
}

static void cs_rewind (ClauseSet *s)
{
    s->rpos = 0;
    s->nbuf = 0;
}

/* Point s->cur at the next clause; returns its length, 0 at end of set.  The
 * pointer is into the set itself, so nothing may be appended while reading. */
static int cs_next (ClauseSet *s)
{
    if (s->rpos >= s->nmem) return 0;
    int len = s->mem[s->rpos++];
    s->cur = s->mem + s->rpos;
    s->rpos += len;
    return len;
}

static void cs_free (ClauseSet *s)
{
    free (s->mem);
    memset (s, 0, sizeof *s);
}

/* ------------------------------------------------------------ per node -- */

/* CaDiCaL writes text DRAT to a file under proof_dir ().  We flush from the
 * polling callback, read what is new through a second descriptor, and punch a
 * hole over what we consumed, so resident size stays bounded however long the
 * proof gets.  Without hole punching the file grows unbounded. */
typedef struct {
    FILE     *f;               /* CaDiCaL's end                              */
    int       fd;              /* ours                                       */
    long long off, punched;    /* consumed, and released                     */
    char     *buf;
    size_t    cap, len;        /* capacity, and bytes of a partial line      */
    int      *lbuf;            /* the clause being parsed, staged so its     */
    long long lcap;            /* weight can wait for its final length      */
    int       discard;         /* drain without counting: what the last node */
                               /* left is not this node's                    */
    int       nopunch;         /* the hole-punch warning is already out      */
} Proof;

static const char *proof_dir (void);     /* defined with the rest of setup */

/* Everything one node accumulates.  Allocated once for the whole run and
 * cleared per node by node_reset. */
typedef struct {
    int        nvars;

    /* The counts: weight of each polarity, over the clauses the set holds. */
    double      *pos, *neg;
    int         *touched;      /* variables seen, in order of first sight --  */
    int          ntouched;     /* the scan order, so ties break stably        */
    signed char *seen;         /* already listed in touched[]?  The counts    */
                               /* cannot say: eviction can zero them          */
    long long    N, nlits;     /* clauses in the set, and their literals      */
    ClauseSet    cap;          /* the proof valid for this node; cap.n == N   */

    /* The cube this node runs under. */
    const struct Cube *cube;   /* so the progress line can be a normal row    */
    signed char *incube;       /* fixed by the cube: not a candidate, or the  */
                               /* tree walks a corridor                       */
    signed char *val;          /* the propagated cube, for cs_reduce          */
    int         *trail;        /* what CaDiCaL implied from it                */
    signed char *core;         /* per cube literal: in the assumption core?   */
    int          ncore;        /* how many were -- -1 until an UNSAT          */

    /* When the next check happens, and what the last one found. */
    long long    keep;         /* clauses eviction may never drop below       */
    long long    next_poll;
    long long    nfresh;       /* clauses this node drained itself, which is  */
                               /* the denominator of the cube shares: unlike  */
                               /* N it never goes down, and unlike N it never */
                               /* counts what was inherited                   */
    int          fire, best;   /* the criterion tripped, on this variable     */
    double       cbest;        /* last score evaluated, for the report        */

    /* The decision this node is under, copied from its cube so the poll does
     * not have to reach back through an incomplete type. */
    int          phase;        /* 1 the ramp, 2 the percentile                */
    int          depth;
    double       thresh;       /* the bar: 0 in phase 1, the percentile in 2  */
    int          nanc;         /* ancestor scores the bar was taken over      */

    /* What this node's FIRST poll said, kept whatever it then does.  That
     * poll runs before the node has derived a conflict of its own, so var0 is
     * the argmax on the parent's proof as reduced by this cube -- the verdict
     * the node inherits -- while best/cbest is the verdict it splits on, k
     * conflicts later in phase 1.  Comparing the two needs no ground truth
     * and no second run: both are measured at the same node, so nothing about
     * the cost of the evidence enters the comparison.  conf0 says how early
     * "first" really was, since the terminator is called on CaDiCaL's
     * schedule and not on ours. */
    int          first_best;
    double       first_cbest;
    long long    first_conf;

    /* What the split this node is about to make actually does, recorded before
     * the row is written.  surv_pos/surv_neg are the two children's surviving
     * clause counts, so max(them)/N is the worst branch -- the critical-path
     * quantity -- and their ratio is the realized balance.  Reconstructing
     * these used to need a --trace run plus a second ordinary run; they cost
     * two passes over the node's set here, once per split. */
    long long    surv_pos, surv_neg;
    int          ntrail;       /* literals carry_in's propagation implied     */
    long long    npoll;        /* polls taken at this node                    */
    int          evicted;      /* cs_evict ran: the set is a window now       */

    /* Reporting. */
    long long    nconf;        /* proof callbacks = conflicts, this node      */
    long long    node;         /* the node running now, for the status line   */
    double       t0, node_t0, last_status;

    Proof        proof;
} Counts;

/* One callback per proof clause is one per conflict, which is the only way to
 * get a per-node conflict count -- CaDiCaL exposes none through either API.
 * Nothing is stored; the proof stays the source of the counts. */
static void count_conflict (void *state, int *clause)
{
    (void) clause;                    /* the signature is CaDiCaL's, not ours */
    ((Counts *) state)->nconf++;
}

/* Drop the oldest quarter of the set and take those occurrences back out of
 * the counts, so the counts keep describing exactly what is present.  A
 * quarter at a time makes the memmove amortised O(1) per clause, and the
 * decrements ride along on a walk of data we are moving anyway.
 *
 * Never evict below c->keep, the --min-split floor: a set capped under it
 * makes every check refuse, so splitting stops for good.  keep is a floor and
 * the ceiling yields to it. */
static void cs_evict (ClauseSet *s, Counts *c)
{
    long long target = s->nmem / 4, at = 0;
    while (at < target && s->n > c->keep) {
        int len = s->mem[at++];
        double w = lit_weight (len);
        for (int i = 0; i < len; i++) {
            int l = s->mem[at + i], v = var_of (l);
            if (l < 0) c->neg[v] -= w; else c->pos[v] -= w;
        }
        at += len;
        s->n--;  c->N--;
        c->nlits -= len;
        c->evicted = 1;        /* the set is a window from here on */
    }
    /* The floor can block the very first clause, and then there is nothing to
     * compact: without this the caller -- which retries on every clause once
     * the ceiling is reached -- would copy the whole set, per proof line. */
    if (!at) return;
    memmove (s->mem, s->mem + at, (size_t) (s->nmem - at) * sizeof (int));
    s->nmem -= at;
}

/* Count one proof line: literals then 0.  'd' lines are deletions.
 *
 * The clause is parsed whole before any of it is counted -- a literal's weight
 * is 1/len, which the terminating 0 is the first thing to reveal.  Staging it
 * also makes the out-of-range case a plain return instead of an undo. */
static void count_line (Counts *c, char *p, char *end)
{
    Proof *pr = &c->proof;
    if (pr->discard) return;
    while (p < end && (*p == ' ' || *p == '\t')) p++;
    if (p >= end || *p == 'd' || *p == 'c' || *p == 'o' || *p == 'i') return;
    int len = 0;
    while (p < end) {
        while (p < end && (*p == ' ' || *p == '\t')) p++;
        if (p >= end) break;
        int neg = 0;
        if (*p == '-') { neg = 1; p++; }
        if (p >= end || *p < '0' || *p > '9') break;
        long v = 0;
        while (p < end && *p >= '0' && *p <= '9') v = v * 10 + (*p++ - '0');
        if (v == 0) break;
        /* Out of the formula's range: drop the whole clause, not the literal.
         * A shortened copy is worse than none -- cs_reduce indexes val[]
         * without a bounds check on the strength of this, and a clause missing
         * a literal can reduce to empty and disappear as if it were satisfied. */
        if (v > c->nvars) return;
        /* A proof clause has no length bound we can rely on: duplicated
         * literals alone can carry it past the variable count. */
        if (len == pr->lcap) {
            pr->lcap = pr->lcap ? 2 * pr->lcap : 64;
            pr->lbuf = xalloc (pr->lbuf, (size_t) pr->lcap * sizeof *pr->lbuf);
        }
        pr->lbuf[len++] = neg ? -(int) v : (int) v;
    }
    if (!len) return;
    double w = lit_weight (len);
    for (int i = 0; i < len; i++) {
        int l = pr->lbuf[i], var = var_of (l);
        if (!c->seen[var]) { c->seen[var] = 1; c->touched[c->ntouched++] = var; }
        if (l < 0) c->neg[var] += w; else c->pos[var] += w;
        cs_lit (&c->cap, l);
    }
    c->N++; c->nfresh++; c->nlits += len;
    cs_end (&c->cap);
    /* The floor is checked here as well as inside cs_evict: once it binds
     * there is nothing eviction can do, and retrying per clause should cost a
     * compare, not a call. */
    if (c->cap.nmem >= cs_budget () && c->cap.n > c->keep)
        cs_evict (&c->cap, c);
}

/* Drain whatever CaDiCaL has written since last time, then release those
 * pages.  Called only from the poll, so never in a tight loop. */
static void drain_proof (Counts *c)
{
    Proof *pr = &c->proof;
    if (!pr->f) return;
    fflush (pr->f);
    for (;;) {
        if (pr->len + 65536 > pr->cap) {
            pr->cap = pr->cap ? 2 * pr->cap : 262144;
            pr->buf = xalloc (pr->buf, pr->cap);
        }
        ssize_t got = read (pr->fd, pr->buf + pr->len, pr->cap - pr->len);
        if (got <= 0) break;
        pr->len += (size_t) got;
        char *p = pr->buf, *end = pr->buf + pr->len, *nl;
        while ((nl = memchr (p, '\n', (size_t) (end - p)))) {
            count_line (c, p, nl);
            p = nl + 1;
        }
        pr->off += p - pr->buf;
        pr->len = (size_t) (end - p);
        if (pr->len) memmove (pr->buf, p, pr->len);   /* keep the partial line */
    }
    /* release the pages we are done with, keeping the file's logical size */
    long long upto = pr->off / 4096 * 4096;
    if (upto > pr->punched) {
        if (fallocate (fileno (pr->f),
                       FALLOC_FL_PUNCH_HOLE | FALLOC_FL_KEEP_SIZE,
                       pr->punched, upto - pr->punched) == 0)
            pr->punched = upto;
        /* Not fatal, but the file then grows with the whole run's proof.
         * Warned once, not per drain. */
        else if (!pr->nopunch) {
            pr->nopunch = 1;
            fprintf (stderr, "cubical: %s cannot punch holes (%s) -- the"
                     " proof file will grow with the run;\n  put --proof-dir"
                     " on a tmpfs such as /dev/shm to keep it bounded\n",
                     proof_dir (), strerror (errno));
        }
    }
}

/* Discard whatever the last node left in the pipe, then clear the counts.
 * Really discard: counting those lines only to wipe them a moment later is
 * work for nothing, and it left the set holding clauses whose counts had
 * already been zeroed, so N and cap.n disagreed. */
static void node_reset (Counts *c)
{
    size_t nv = (size_t) c->nvars + 1;
    c->proof.discard = 1;
    drain_proof (c);
    c->proof.discard = 0;
    memset (c->pos, 0, nv * sizeof *c->pos);
    memset (c->neg, 0, nv * sizeof *c->neg);
    memset (c->seen, 0, nv * sizeof *c->seen);
    c->ntouched = 0;
    c->N = c->nlits = c->nconf = c->nfresh = 0;
    c->fire = c->best = 0;
    c->ncore = -1;             /* or the progress line shows the last node's */
    c->cube = NULL;
    /* 0, not the cadence: every node polls the moment it starts.  That poll
     * is the var0 measurement, and in phase 2 it is also the first poll that
     * may split -- a node holding enough inherited proof should not have to
     * re-derive any of it before it is allowed to act. */
    c->next_poll = 0;
    c->cbest = 0;
    c->npoll = 0;
    c->first_best = 0; c->first_cbest = 0; c->first_conf = -1;
    c->surv_pos = c->surv_neg = -1; c->ntrail = 0;
    c->evicted = 0;
    c->phase = 1; c->depth = 0; c->thresh = 0.0; c->nanc = 0;
}

/* ------------------------------------------------------------ the check -- */

/* A variable's score is the power mean of order t of its two polarity weights,
 * normalised onto [0,1] whatever t is so that --cover means one thing across a
 * sweep:
 *
 *     score(v) = 2 * M_t(p, q) / N,   M_t(p, q) = ((p^t + q^t) / 2)^(1/t)
 *
 * One family, and the three scores this tool used to offer are three of its
 * points: M_1 is the arithmetic mean, so t=1 is the old `sum`, the plain cover;
 * M_0 is the geometric mean sqrt(p q), so t=0 is `geo`; M_t -> min(p, q) as
 * t -> -inf, so -t -inf is `min`.  Nothing in between had a name.
 *
 * Written in the units the decision is made in -- s = p + q, and b = min(p,q)/s
 * the balance, in (0, 1/2] --
 *
 *     score(v) = (s / N) * 2 * M_t(1 - b, b)
 *              = cover(v) * a factor that is 1 at b = 1/2 and falls off it
 *
 * every member of the family is the plain cover times a penalty for the weight
 * sitting lopsidedly on one polarity, and t sets only how steep that penalty
 * is: t=1 does not penalise at all, t=-inf charges in proportion.  The factor
 * is computed in these units rather than from p and q directly because both
 * bases are then in [0,1] with the larger at least 1/2, so no pow() can
 * overflow however large the weights grow -- p^t on raw weights would, for the
 * negative t a sweep spends most of its range on.
 *
 * The scale.  M_t is non-decreasing in t (the power-mean inequality), so for
 * t <= 1 it is at most (p + q)/2 <= N/2, and doubling divides by that maximum
 * -- attained by a variable that both carries all the weight and splits it
 * evenly.  Above t=1 the mean exceeds the arithmetic one and the maximum moves
 * to the one-sided variable instead, so the normaliser does too; balance_max
 * has it.  --cover therefore stays in (0,1] for every t and the cover%% column
 * in the log stays readable across a sweep without rescaling.  What it costs is
 * the direct reading of the raw min: min(p,q)/N was "the proof weight removed
 * from the weaker branch", and normalised it is a fraction of the balanced
 * maximum instead.
 *
 * What normalising does NOT do is make two t comparable at one --cover.  The
 * factor is <= 1 with equality only at b = 1/2, so a lower t scores every
 * imbalanced variable strictly lower and splits strictly less often at a fixed
 * threshold.  A sweep over t at a single --cover measures the shape of the
 * criterion and its strictness together; utils/run_autocube_t_sweep.py pairs
 * each t with a range of thresholds for that reason. */

/* 2 * M_t(1 - b, b), the balance factor above, for b in [0, 1/2]. */
static double balance_factor (double t, double b)
{
    double a = 1.0 - b;
    /* t=0 is a removable singularity of the power mean, taken as the limit, the
     * geometric mean.  The epsilon is not pedantry: the closed form loses it
     * numerically well before t reaches 0, since at tiny t both base^t round to
     * 1 and the 1/t exponent turns that into 2 rather than into the mean.  1e-6
     * is far below any t a sweep can distinguish -- the true factor differs
     * from the geometric mean there in the sixth digit. */
    if (fabs (t) < 1e-6) return 2.0 * sqrt (a * b);
    if (isinf (t))       return 2.0 * (t < 0.0 ? b : a);
    /* A one-sided variable.  For t <= 0 the mean is 0 by the limit, which is
     * also where pow() arrives via 0^negative = +inf, but reaching it through
     * infinity is not worth relying on. */
    if (b <= 0.0)        return t > 0.0 ? 2.0 * pow (0.5, 1.0 / t) : 0.0;
    return 2.0 * pow ((pow (a, t) + pow (b, t)) / 2.0, 1.0 / t);
}

/* The largest balance_factor a variable could reach at this t, which is what
 * the score is normalised by.  For t <= 1 the power-mean inequality puts the
 * maximum at the balanced variable, b = 1/2, where the factor is exactly 1;
 * above t=1 it moves to the one-sided variable, b = 0. */
static double balance_max (double t)
{
    return t > 1.0 ? balance_factor (t, 0.0) : 1.0;
}

/* Both derived from -t once, in check_opts.  score_of runs over every touched
 * variable at every poll, and three pow() calls per variable is worth not
 * paying where the answer is a constant of the run. */
static double g_bnorm = 1.0;   /* 1 / balance_max (opt_t)                   */
static int    g_plain = 1;     /* t == 1: the factor is 1 at every balance  */

static double score_of (double p, double q, long long N)
{
    double s = p + q;
    if (s <= 0.0) return 0.0;
    double cover = s / (double) N;
    if (g_plain) return cover;
    double lo = p < q ? p : q;
    return cover * balance_factor (opt_t, lo / s) * g_bnorm;
}

/* The old --score names, for the one line of the log that has to be readable
 * without the formula in hand.  A sweep walks straight past these, so most runs
 * get no name at all. */
static const char *score_alias (double t)
{
    if (t == 1.0)                 return " (sum)";
    if (fabs (t) < 1e-6)          return " (geo)";
    if (isinf (t) && t < 0.0)     return " (min)";
    return "";
}

/* --trace prints a line per poll and never splits: the point is to watch the
 * criterion rather than act on it.  Alongside the winner it gives the plateau
 * width -- how many candidates sit within 90% and 50% of the best, which is
 * threshold-free and so does not move with --cover -- plus how many clear
 * this node's threshold itself.  A second scan, hence its own function.
 *
 * m90/m50 are the same two tiers weighed in proof rather than counted: the
 * share of the node's clauses carried by the candidates in each.  A count is
 * not comparable across instances -- this benchmark spans 297 to 57489 touched
 * variables, 194x -- while a share is a fraction of a normalised whole and so
 * is dimensionless in both the cover units and the variable count.
 *
 * mtot is every candidate's score added up.  Only at t == 1 is that the plain
 * cover, where each clause hands its literals 1/len apiece and the total comes
 * to 1; at every other t the score carries balance_factor as well, so mtot is
 * 1 minus the mean balance penalty over the candidates -- 0.66 to 0.97 across
 * this benchmark at t = 0.  It is a reading of how lopsided the instance's
 * variables are, not a check that anything sums to 1. */
static void trace_poll (const Counts *c, int best, double cbest, double c2nd)
{
    int n90 = 0, n50 = 0, nabove = 0;
    double m90 = 0, m50 = 0, mtot = 0;
    for (int i = 0; i < c->ntouched; i++) {
        int v = c->touched[i];
        if (c->incube[v]) continue;
        double f = score_of (c->pos[v], c->neg[v], c->N);
        mtot += f;
        if (f >= c->thresh) nabove++;
        if (f >= 0.9 * cbest) { n90++; m90 += f; }
        if (f >= 0.5 * cbest) { n50++; m50 += f; }
    }
    printf ("%-10lld %-10.6f %-10.6f %-10d %-20.2f %-10d %-10d %-10d %-10d"
            " %-10.6f %-10.6f %-10.6f\n",
            c->N, cbest, c2nd, best, (double) c->nlits / (double) c->N,
            c->ntouched, nabove, n90, n50, m90, m50, mtot);
    fflush (stdout);
}

/* The p-th percentile of the ancestor scores, which is the bar a phase-2 node
 * has to beat.  Linear interpolation between the two closest ranks, which is
 * the ordinary definition and the one numpy and R default to -- it matters
 * because the sample is small: at the ramp depth there are exactly d of them,
 * and with an even count a p=50 that picked an order statistic rather than
 * interpolating would read as the lower of the two middle scores and so bias
 * the bar low at every other level.
 *
 * An empty sample is a bar of 0: the root has no ancestors and must be free to
 * split.  A single sample is itself, for every p.
 *
 * O(d log d) on a copy, once per node in node_begin and never in a poll: d is
 * the depth, so even a thousand-level path is a few microseconds against a
 * node that runs for thousands of conflicts. */
static int cmp_flt (const void *a, const void *b)
{
    float x = *(const float *) a, y = *(const float *) b;
    return x < y ? -1 : x > y ? 1 : 0;
}

static double percentile (const float *v, int n, int p)
{
    if (n <= 0) return 0.0;
    if (n == 1) return v[0];
    float *s = xalloc (NULL, (size_t) n * sizeof *s);
    memcpy (s, v, (size_t) n * sizeof *s);
    qsort (s, (size_t) n, sizeof *s, cmp_flt);
    double idx = (double) p / 100.0 * (double) (n - 1);
    int lo = (int) idx;
    if (lo >= n - 1) { double r = s[n - 1]; free (s); return r; }
    double frac = idx - (double) lo;
    double r = s[lo] + frac * ((double) s[lo + 1] - (double) s[lo]);
    free (s);
    return r;
}

/* One poll.  Finds the best candidate, records what the node's first poll saw,
 * and says whether this node should split now.
 *
 * Phase 1 ignores the score entirely and fires once the node has spent its
 * --ramp-conflicts budget: the point of the ramp is a fixed-cost measurement
 * at every node and a tree that fans out to the workers by construction, so
 * the only thing that can stop a split there is --min-split -- there has to be
 * some proof to read the argmax off -- or --max-depth.
 *
 * Phase 2 fires when the best score beats this node's bar, which node_begin
 * took as a percentile over the scores its ancestors split on.
 *
 * --max-depth is checked here rather than at the split, so a node at the cap
 * never terminates its own solve for a split it is not allowed to make: it
 * stops polling and runs to a verdict like any leaf. */
static int evaluate (Counts *c)
{
    if (c->ntouched < 2) return 0;
    int best = 0;
    double cbest = 0, c2nd = 0;
    for (int i = 0; i < c->ntouched; i++) {
        int v = c->touched[i];
        if (c->incube[v]) continue;
        double f = score_of (c->pos[v], c->neg[v], c->N);
        if (f > cbest) { c2nd = cbest; cbest = f; best = v; }
        else if (f > c2nd) c2nd = f;
    }
    c->cbest = cbest;
    if (opt_trace) { trace_poll (c, best, cbest, c2nd); return 0; }
    /* Before every gate below, so var0 is what the node inherited and not what
     * it was first entitled to act on. */
    if (!c->npoll++) {
        c->first_best = best; c->first_cbest = cbest; c->first_conf = c->nconf;
    }
    /* --max-depth, which --split-idle makes conditional on someone starving.
     * g_sh is null outside a parallel worker, so a sequential run always sees
     * the hard cap -- there is no other worker to be idle. */
    if (c->depth >= opt_maxdepth
        && !(opt_splitidle && g_sh && g_sh->want > 0)) return 0;
    if (c->N < opt_minsplit) return 0;           /* nothing to read it off    */
    if (!best) return 0;
    c->best = best;
    if (c->phase == 1) {
        if (c->nconf < opt_rampk) return 0;      /* still buying its view */
        c->fire = 1; return 1;
    }
    if (cbest > c->thresh) { c->fire = 1; return 1; }
    return 0;
}

/* Defined with row(), which needs the Cube type declared further down. */
static void status_line (const Counts *c, double now);

/* Take whatever the other workers have published since last time.  Called
 * between nodes, which is the only point an incremental solver accepts new
 * clauses, and is often enough: nodes are seconds apart and cores arrive at
 * well under one per worker per second. */
static int import_cores (void *solver)
{
    if (!g_sh || !opt_share) return 0;
    int got = 0, head = g_sh->shead;
    while (g_scur < head && g_scur + 2 <= SHARE_INTS) {
        int len = g_sh->sbuf[g_scur];
        if (!len) break;                /* reserved, not yet published */
        if (g_scur + len + 2 > SHARE_INTS) break;
        if (g_sh->sbuf[g_scur + 1] != g_wid) {
            for (int i = 0; i < len; i++)
                ipasir_add (solver, g_sh->sbuf[g_scur + 2 + i]);
            ipasir_add (solver, 0);
            got++;
        }
        g_scur += len + 2;
    }
    return got;
}

static int on_terminate (void *state)
{
    Counts *c = state;
    /* A sibling already decided the formula, so this subtree cannot change the
     * answer.  Checked here rather than between nodes because a single leaf can
     * run for the whole cap. */
    if (g_sh && g_sh->stop) g_stop = 1;
    if (g_stop) return 1;
    drain_proof (c);
    double now = cpu_time ();
    if (now - c->last_status >= STATUS_EVERY) {
        c->last_status = now;
        status_line (c, now);
    }
    if (c->nconf < c->next_poll) return 0;              /* the common case */
    if (evaluate (c)) return 1;
    /* A node at --max-depth can never fire, so it stops looking: the first
     * poll has already recorded var0, and every later one would be a scan over
     * every touched variable for an answer that cannot be acted on.  Not under
     * --trace, where the scan IS the output, and not under --split-idle, where
     * the answer depends on `want` and so can change after this poll.
     * drain_proof above is unaffected, so the trace file still gets punched out
     * on schedule. */
    if (c->depth >= opt_maxdepth && !opt_trace && !opt_splitidle)
        c->next_poll = LLONG_MAX;
    /* A ramp node has one question and one moment to ask it, so it jumps
     * straight to its budget rather than scanning its way there: the polls in
     * between could not act on anything.  Past the budget -- reachable when
     * --min-split has not been met yet -- it falls back on the cadence, which
     * is also what a phase-2 node that did not clear its bar does. */
    else if (c->phase == 1 && c->nconf < opt_rampk) c->next_poll = opt_rampk;
    else c->next_poll = c->nconf + opt_pollint;
    return 0;
}

/* --------------------------------------------------------------- carry -- */

/* The clauses of `in` that survive the assignment in `val`: those with a true
 * literal are satisfied and vanish, false literals drop out of the rest.
 * Everything left is still a clause of the subproblem, so a child can count it
 * as evidence instead of starting from nothing.  With `c` given the survivors
 * are also counted into it.  `in` holds no out-of-range variable -- count_line
 * never admits one.  One sequential pass in, one sequential pass out. */
static void cs_reduce (ClauseSet *in, const signed char *val,
                       ClauseSet *out, Counts *c)
{
    cs_rewind (in);
    for (int len; (len = cs_next (in)); ) {
        int sat = 0;
        for (int i = 0; i < len && !sat; i++) {
            int l = in->cur[i];
            sat = val[var_of (l)] == (l < 0 ? -1 : 1);
        }
        if (sat) continue;
        for (int i = 0; i < len; i++) {
            int l = in->cur[i];
            if (val[var_of (l)] == (l < 0 ? 1 : -1)) continue;     /* falsified */
            cs_lit (out, l);
        }
        /* Counted in a second pass over the survivors, staged at [hdr+1, nmem):
         * what the child holds is the reduced clause, so it is the reduced
         * length that sets the weight -- a ternary clause the cube cuts to a
         * binary one hands its two survivors 1/2 each, not 1/3.  That is the
         * reduction doing its work: trimming a clause promotes what is left. */
        if (c && out->nbuf) {
            double w = lit_weight (out->nbuf);
            for (long long i = out->hdr + 1; i < out->nmem; i++) {
                int l = out->mem[i], v = var_of (l);
                if (!c->seen[v]) { c->seen[v] = 1; c->touched[c->ntouched++] = v; }
                if (l < 0) c->neg[v] += w; else c->pos[v] += w;
            }
            c->N++; c->nlits += out->nbuf;
        }
        cs_end (out);              /* a clause that emptied is never committed */
    }
}

/* How many of `in`'s clauses survive the assignment in `val`, and how many
 * literals they carry.  cs_reduce without the writing: same walk, same rules
 * -- a clause with a true literal is satisfied and vanishes, false literals
 * drop out of the rest, and a clause that empties is not counted.  Used to
 * measure a candidate before committing to it, where building the set would
 * be thrown away.
 *
 * Keeping the literal count too is what makes the answer readable: a node
 * whose survivors are 34 literals long has not been reduced in any way
 * propagation can use, however many clauses died. */
static void cs_survive (ClauseSet *in, const signed char *val,
                        long long *nclause, long long *nlit)
{
    long long nc = 0, nl = 0;
    cs_rewind (in);
    for (int len; (len = cs_next (in)); ) {
        int sat = 0, keep = 0;
        for (int i = 0; i < len && !sat; i++) {
            int l = in->cur[i];
            sat = val[var_of (l)] == (l < 0 ? -1 : 1);
        }
        if (sat) continue;
        for (int i = 0; i < len; i++) {
            int l = in->cur[i];
            if (val[var_of (l)] != (l < 0 ? 1 : -1)) keep++;
        }
        if (!keep) continue;              /* emptied: never a child's clause */
        nc++; nl += keep;
    }
    *nclause = nc; *nlit = nl;
}

/* Bring the parent's proof into this node.  CaDiCaL propagates the cube, then
 * one walk drops what the implications satisfy, trims what they falsify, and
 * counts the rest.  `in` is the parent's set; it is read, never taken, and the
 * caller frees it. */
static void carry_in (Counts *c, void *solver, ClauseSet *in,
                      const int *cube, int n)
{
    /* nt stays 0 if propagation refuted the cube or nothing was carried; the
     * walk then just counts the set, which is what the node needs anyway. */
    int nt = 0;
    if (in && in->n && cubical_propagate (solver) != 20)
        nt = cubical_implied (solver, c->trail, c->nvars + 1);
    /* Recorded for the row: a cube that implies thousands of literals and
     * still removes nothing from the proof is the signature of a candidate
     * set that is one decision wearing several hats -- gate variables, where
     * assuming one fixes the rest.  Measured: 4775 implied on minxorminand,
     * 32243 on ACG-10-10p0, against 1 on the instances cubing helps. */
    c->ntrail = nt;
    for (int i = 0; i < nt; i++) {
        int l = c->trail[i], v = var_of (l);
        if (v <= c->nvars) c->val[v] = l < 0 ? -1 : 1;
    }
    /* Reduce straight into c->cap instead of into a set that then replaces it.
     * propagate() above re-enters the solve path, so it can call the terminator
     * and hence drain the proof: anything it wrote is already in c->cap and
     * already counted.  Those clauses were derived under this very cube, so
     * they must not be reduced by it -- and appending rather than replacing is
     * what stops them being counted once by count_line and again below. */
    if (in) cs_reduce (in, c->val, &c->cap, c);
    for (int i = 0; i < nt; i++) {
        int v = var_of (c->trail[i]);
        if (v <= c->nvars) c->val[v] = 0;
    }
    /* node_reset already asked for a poll at nconf 0 and propagate () above
     * may have overshot it, so ask again from here: every node takes its var0
     * measurement on the set it just inherited, and a phase-2 node that
     * inherited enough of one can split off it without spending a conflict. */
    c->next_poll = 0;

    /* propagate() re-enters the solve path, so set the assumptions again */
    for (int i = 0; i < n; i++) ipasir_assume (solver, cube[i]);
}

/* ------------------------------------------------------------ worklist -- */

/* cp: solve time from the root down to this node, excluding the node itself.
 * A child cannot start before every split above it is decided, so cp plus the
 * node's own time is the earliest it can finish however many cores are
 * available; the largest over all leaves is the run's critical path. */
typedef struct Cube {
    int      *lits;
    int       n, depth;
    long long parent;
    double    cp;
    /* The scores every ancestor split on, root first, which is the sample
     * phase 2 takes its bar from.  nanc is the length and equals depth for a
     * cube built here; a donated cube carries the list with it, so it is
     * depth there too.  float because a percentile comparison cannot use more
     * than six digits and a deep cube is copied on every donation. */
    float    *anc;
    int       nanc;
    ClauseSet *cls;           /* the parent's proof, already reduced by lits  */
    signed char *second;      /* per cube literal: its level took the second */
                              /* branch.  Known when the cube is built, never */
                              /* recomputed -- see split_node and put_row    */
} Cube;

typedef struct { Cube *v; int n, cap; } Stack;

/* Run totals.  crit* describe the critical path: the deepest chain of split
 * decisions plus the leaf at its end, which is what the run would still cost
 * with unlimited cores. */
struct Stats {
    long long nodes, splits, leaves, maxdepth;
    long long totconf, maxleafconf, maxleafnode, critnode;
    long long coreleaves, corelits, decidedlits, emptycore;
    long long nofail, nofailnode;  /* refuted using no assumption, and where  */
    long long learned, learnedlits;
    long long shared_in;       /* cores taken from the other workers         */
    long long donated, taken;  /* cubes handed over, and picked up            */
    double cpu;                /* CPU seconds, this process and its workers   */
    double tsplit, tleaf, crit, crit_above, crit_own;
};

/* The workers' Stats slots, laid out after the Shared header in one mapping. */
static Stats *shared_stats (Shared *sh) { return (Stats *) (sh + 1); }

static void push (Stack *s, const int *lits, int n, int depth,
                  long long parent, double cp)
{
    if (s->n == s->cap) {
        s->cap = s->cap ? 2 * s->cap : 64;
        s->v = xalloc (s->v, (size_t) s->cap * sizeof (Cube));
    }
    Cube *c = &s->v[s->n++];
    c->lits = xalloc (NULL, (size_t) (n ? n : 1) * sizeof (int));
    if (n) memcpy (c->lits, lits, (size_t) n * sizeof (int));   /* root: NULL */
    c->n = n; c->depth = depth; c->parent = parent; c->cp = cp; c->cls = NULL;
    c->anc = NULL; c->nanc = 0;   /* split_node fills them for a real child  */
    c->second = xzalloc ((size_t) (n ? n : 1) * sizeof *c->second);
}

static void pop_free (Cube *c)
{
    free (c->lits); free (c->second); free (c->anc);
    if (c->cls) { cs_free (c->cls); free (c->cls); }
}

/* ----------------------------------------------------------- reporting -- */

/* The cube literals this node actually had to assume.  A second child is not
 * one of them: by the time it runs, a depth-first walk has refuted its
 * sibling's whole subtree, so F and the literals above it already entail this
 * literal -- F & C & l unsatisfiable is exactly F & C |= -l, and -l is what
 * this node assumes.  That holds whatever the solver then does: with
 * --learn-cores there is a clause to propagate it and the solver never decides
 * it at all, and without one the solver rediscovers the same fact the long way,
 * but either way the level settled nothing and there is nothing in it to
 * credit or blame the split heuristic for. */
static int decided (const Cube *cube)
{
    int n = 0;
    for (int i = 0; i < cube->n; i++) n += !cube->second[i];
    return n;
}

/* One line per node: enough by itself to rebuild the tree (id/parent/depth and
 * the literal path), to see what the node cost, and -- for a split -- what
 * fired and on which variable.  Anything constant for the run is in the banner.
 *
 * Each cube literal is annotated `lit(share)`: the percentage of the proof this
 * node derived itself that mentions the literal's *variable*, either polarity.
 * One the refutation barely mentions did not earn its place.  Three details
 * there are load-bearing:
 *
 *  - The denominator is nfresh, not N.  Inherited clauses cannot reach the
 *    numerator (cs_reduce strips the cube's variables out of them), so leaving
 *    them in the denominator scales every share by a factor unrelated to the
 *    literal -- 1x to 144x within one run -- and the column stops comparing
 *    across nodes.  Eviction is the residual mismatch: it drops clauses from
 *    the counts but must not touch nfresh, so past --carry-mb a share reads
 *    low, inventing unused literals rather than hiding them.
 *  - The variable, not the sign the cube fixed it at.  A learned clause is
 *    falsified by the trail it is derived from and the cube sits on that trail,
 *    so the cube's own sign is the one thing conflict analysis can never put in
 *    a clause -- it reports nothing for the literals that worked hardest.
 *  - Fixed widths (g_litw and %5.2f), so a share can be read down one column
 *    as it decays at each node the literal survives to.
 *
 * A node that reached no conflict of its own prints 0 for the whole
 * cube; there 0 means "no evidence yet", and the clauses column tells it apart
 * from a genuine zero.
 *
 * A refuted leaf also carries the exact answer the share estimates: `*` if
 * CaDiCaL's assumption core needed the literal, `.` if not, blank where no
 * core exists.  The core is not minimal, so `.` proves a literal unnecessary
 * while `*` does not prove it necessary -- but where the marker is there it
 * beats the share, which disagrees with it in both directions.
 *
 * `=` instead of either wherever the level took the second branch -- see
 * decided() for why that literal is entailed by the ones above it and so is no
 * assumption of this node's.  It replaces both markers because neither can
 * apply: a literal the refutation never had to assume cannot be one it needed,
 * and calling it unnecessary with `.` blames the split heuristic for a level
 * that was never its choice to get right.  The denominator in the core column
 * drops them for the same reason, so that column reads "of the literals this
 * node decided, how many the refutation used".
 *
 * The share still prints next to `=`, because it is worth seeing: it is the
 * share of a literal conflict analysis resolves straight back out through the
 * clause that forced it, and a column of them running 0.0x down the page is
 * what the second branch of a split actually contributes to a proof. */
/* One row, built whole and written with a single call.
 *
 * It used to fprintf the header and then once per cube literal.  stdout is
 * line buffered so those mostly coalesced -- but the STATUS lines go to
 * stderr, which is unbuffered, making every fragment its own write(), and with
 * --cores several processes share both descriptors.  Rows ended up spliced
 * into one another.  One buffer and one write: two lines can still interleave
 * with each other, but never inside themselves.
 *
 * The worker column is there because with --cores the node ids are unique but
 * not obviously attributable; it reads "-" in a sequential run. */
static void put_row (FILE *f, int colour, long long id, const Cube *cube,
                     const char *event, double node_s, double total_s,
                     const Counts *c, int split_var)
{
    static char *line;
    static size_t cap;
    size_t need = 512 + (size_t) cube->n * (size_t) (g_litw + 48);
    if (need > cap) { cap = need; line = xalloc (line, cap); }
    size_t k = 0;
#define ROW_ADD(...)                                                    \
    do {                                                                \
        int w_ = snprintf (line + k, cap - k, __VA_ARGS__);             \
        if (w_ < 0) break;                                              \
        /* snprintf returns what it WOULD have written, so clamp or the \
         * length outruns the buffer and fwrite reads past the end. */   \
        k = ((size_t) w_ >= cap - k) ? cap - 1 : k + (size_t) w_;       \
    } while (0)

    /* "." and not "" where there is nothing to report: a blank column
     * vanishes under whitespace field splitting, so `awk '{print $21}'` reads
     * a different column on the rows that have a core than on the rows that
     * do not.  A placeholder keeps every row the same field count. */
    char core[16] = ".";
    if (c->ncore >= 0) snprintf (core, sizeof core, "%d/%d", c->ncore,
                                 decided (cube));
    char wc[16];
    if (g_wid >= 0) snprintf (wc, sizeof wc, "%3d", g_wid);
    else            snprintf (wc, sizeof wc, "%3s", "-");

    /* clauses is the whole set the cover was read off, fresh is the part of it
     * this node derived itself: the difference is what it inherited, so the
     * two together say how much of the selection the node actually earned.
     * Past --carry-mb fresh can exceed clauses -- eviction takes clauses out
     * of the set but nfresh only ever counts up. */
    /* ph/bar%: which rule this node was under and what it had to beat.  bar
     * is 0.00 for every phase-1 node by definition, and for the root, so a
     * non-zero bar marks exactly the nodes the percentile could have stopped.
     * nanc is how many ancestor scores it was taken over -- the sample size
     * behind the bar, which at p=50 and nanc 1 or 2 is a coin the log should
     * not hide.
     *
     * var0/cov0/conf0: the argmax on the proof this node INHERITED, taken at
     * its first poll before it has derived anything of its own, with the
     * conflict count at that poll so "before" can be checked rather than
     * assumed.  var/cover% is the argmax it actually split on -- in phase 1
     * that is --ramp-conflicts later, which is the whole measurement the ramp
     * buys.  agree is "=" when the two are the same variable, "x" when the
     * budget changed the node's mind, "-" where there is nothing to compare
     * (no poll yet, or a leaf that split on nothing). */
    /* What the split actually does, which is the part cover only predicts.
     *
     * s+/s- are the two children's surviving proof as a share of this node's
     * set.  max of the two is the worst branch -- the critical path with
     * unlimited cores is max (child cost), so that is the number a split is
     * bought with; their ratio is the realized balance, which the score's own
     * balance factor only proxies (measured, a variable can be 0.36 balanced
     * in occurrences and 0.04 balanced in realized reduction).
     *
     * len is the mean literals per clause in the set the score was read off.
     * A split removes ONE literal from a clause, so on a set averaging 34
     * literals it decomposes nothing propagation can use however many clauses
     * it satisfies -- the two stone instances sit at 34 and 39 against 12-24
     * everywhere cubing works.
     *
     * bal is the chosen variable's polarity balance in the counts, min over
     * max, which is what -t scores.  Held against s+/s- it says whether the
     * score's own balance proxy was right at this node.
     *
     * trail is what propagating this node's cube implied beyond the cube
     * itself.  Thousands implied with nothing removed from the proof is the
     * signature of a candidate set that is one decision in disguise. */
    char sp[16], sn[16], bl[16];
    double sden = c->N > 0 ? 100.0 / (double) c->N : 0.0;
    if (c->surv_pos >= 0) snprintf (sp, sizeof sp, "%6.2f", sden * (double) c->surv_pos);
    else                  snprintf (sp, sizeof sp, "%6s", ".");
    if (c->surv_neg >= 0) snprintf (sn, sizeof sn, "%6.2f", sden * (double) c->surv_neg);
    else                  snprintf (sn, sizeof sn, "%6s", ".");
    if (split_var) {
        double p = c->pos[split_var], q = c->neg[split_var], lo = p < q ? p : q;
        double hi = p < q ? q : p;
        snprintf (bl, sizeof bl, "%5.3f", hi > 0 ? lo / hi : 0.0);
    } else snprintf (bl, sizeof bl, "%5s", ".");
    ROW_ADD ("c %s %7lld %7lld %5d %2d %-6s %10lld %8lld %6.2f %8lld %8.2f"
             " %9.2f %6d %6d %7.3f %7.3f %10lld %7.3f %5d"
             " %6s %6s %5s %8d %5s %6s ",
             wc, id, cube->parent, cube->depth, c->phase, event, c->nconf,
             c->N, c->N > 0 ? (double) c->nlits / (double) c->N : 0.0,
             c->nfresh, node_s, total_s,
             split_var, c->first_best,
             100.0 * c->cbest, 100.0 * c->first_cbest,
             c->first_conf < 0 ? 0 : c->first_conf,
             100.0 * c->thresh, c->nanc,
             sp, sn, bl, c->ntrail,
             c->evicted ? "EVICT" : ".", core);
    /* A node can derive no proof of its own, so there may be no share to take:
     * print zeros rather than divide by zero. */
    double pct = c->nfresh ? 100.0 / (double) c->nfresh : 0.0;
    for (int i = 0; i < cube->n; i++) {
        int l = cube->lits[i], v = var_of (l);
        const char *col = "";
        char mark = ' ';
        if (cube->second[i]) mark = '=';
        else if (c->ncore >= 0) {
            mark = c->core[i] ? '*' : '.';
            if (colour) col = c->core[i] ? CORE_IN : CORE_OUT;
        }
        ROW_ADD (" %s%*d(%5.2f)%s%c", col, g_litw, l,
                 pct * (c->pos[v] + c->neg[v]), *col ? CORE_OFF : "", mark);
    }
    ROW_ADD ("\n");
#undef ROW_ADD
    fwrite (line, 1, k, f);
}

static void row (long long id, const Cube *cube, const char *event,
                 double node_s, double total_s, const Counts *c, int split_var)
{
    if (!opt_quiet)
        put_row (stdout, g_tty_out, id, cube, event, node_s, total_s, c,
                 split_var);
    if (g_log)
        put_row (g_log, 0, id, cube, event, node_s, total_s, c, split_var);
}

/* The periodic progress line: the running node as a row, with STATUS where
 * the outcome will go.  On stderr, so it stays out of --cube-log and never has to
 * be filtered back out; a long node otherwise looks like a hang.  c->cube is
 * null between nodes, and propagate() in carry_in can reach the terminator, so
 * the guard is real. */
static void status_line (const Counts *c, double now)
{
    if (!c->cube) return;
    put_row (stderr, g_tty_err, c->node, c->cube, "STATUS",
             now - c->node_t0, now - c->t0, c, c->best);
}

/* --------------------------------------------------------------- setup -- */

static int read_cnf (const char *path, void *solver, int *nvars, long long *nclauses)
{
    FILE *f = path ? fopen (path, "r") : stdin;
    if (!f) { perror (path ? path : "stdin"); return -1; }
    const char *name = path ? path : "<stdin>";
    int cap = 64, *buf = xalloc (NULL, (size_t) cap * sizeof (int));
    int n = 0, ch, maxvar = 0, decvars = 0, bad = 0;
    long long ncl = 0, declared = -1;
    for (;;) {
        do { ch = fgetc (f); } while (ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r');
        if (ch == EOF) break;
        if (ch == 'c') {                                        /* comment */
            while ((ch = fgetc (f)) != EOF && ch != '\n');
            continue;
        }
        if (ch == 'p') {                     /* header: keep it and check it */
            if (fscanf (f, " cnf %d %lld", &decvars, &declared) != 2) {
                fprintf (stderr, "%s: malformed 'p cnf' header\n", name);
                bad = 1; break;
            }
            while ((ch = fgetc (f)) != EOF && ch != '\n');
            continue;
        }
        ungetc (ch, f);
        int closed = 0;
        for (n = 0;;) {
            int lit;
            if (fscanf (f, "%d", &lit) != 1) {
                fprintf (stderr, feof (f)
                         ? "%s: clause %lld is not terminated by 0\n"
                         : "%s: not a DIMACS literal in clause %lld\n", name, ncl + 1);
                bad = 1;
                break;
            }
            if (lit == 0) { closed = 1; break; }
            if (var_of (lit) > maxvar) maxvar = var_of (lit);
            if (n == cap) { cap *= 2; buf = xalloc (buf, (size_t) cap * sizeof (int)); }
            buf[n++] = lit;
        }
        if (!closed) break;
        for (int i = 0; i < n; i++) ipasir_add (solver, buf[i]);
        ipasir_add (solver, 0);        /* n == 0 is the empty clause: keep it,
                                        * dropping it would turn UNSAT into SAT */
        ncl++;
    }
    free (buf);
    if (path) fclose (f);
    if (bad) return -1;
    if (declared >= 0 && declared != ncl) {
        fprintf (stderr, "%s: header declares %lld clauses but the file has %lld\n",
                 name, declared, ncl);
        return -1;
    }
    if (declared >= 0 && maxvar > decvars) {
        fprintf (stderr, "%s: header declares %d variables but x%d occurs\n",
                 name, decvars, maxvar);
        return -1;
    }
    if (!ncl) { fprintf (stderr, "%s: no clauses\n", name); return -1; }
    *nvars = maxvar;
    *nclauses = ncl;
    return 0;
}

/* Both ends are opened before the path is unlinked, so nothing is left behind
 * if we die. */

/* --proof-dir, else CUBICAL_PROOF_DIR, else /dev/shm, else TMPDIR, else /tmp.
 * Cached, so a worker's reopen lands where check_proof_dir passed. */
static const char *proof_dir (void)
{
    static const char *dir;
    if (dir) return dir;
    if (opt_proofdir) return dir = opt_proofdir;
    if ((dir = getenv ("CUBICAL_PROOF_DIR")) && *dir) return dir;
    if (!access ("/dev/shm", W_OK | X_OK)) return dir = "/dev/shm";
    if ((dir = getenv ("TMPDIR")) && *dir) return dir;
    return dir = "/tmp";
}

/* Keyed on the pid, so a forked worker's path differs from its parent's. */
static void proof_path (char *buf, size_t n)
{
    snprintf (buf, n, "%s/cubical.%d.drat", proof_dir (), (int) getpid ());
}

/* Called before the solver is created: an unusable directory is one line at
 * startup rather than a failed fopen mid-search. */
static int check_proof_dir (void)
{
    const char *dir = proof_dir ();
    if (access (dir, W_OK | X_OK)) {
        fprintf (stderr, "cubical: proof directory %s is not writable: %s\n"
                 "  pass --proof-dir <dir> or set CUBICAL_PROOF_DIR\n",
                 dir, strerror (errno));
        return -1;
    }
    return 0;
}

/* Give this worker a proof file of its own.
 *
 * It cannot simply call open_proof again: CaDiCaL accepts trace_proof (and
 * "binary") only directly after initialisation, and a worker's solver has
 * already solved every node of the frontier.  So the tracer keeps the FILE it
 * was handed at startup, and freopen re-points that same FILE at a new file --
 * the solver writes exactly where it always did, and the bytes land here
 * instead of interleaving with every sibling's into the parent's trace.
 *
 * The drain state is reset with it: offsets into the old file mean nothing in
 * the new one, and node_reset will discard whatever is pending anyway. */
static int reopen_proof (Proof *pr)
{
    char ppath[PATH_MAX];
    proof_path (ppath, sizeof ppath);
    if (!freopen (ppath, "w+", pr->f)) { perror (ppath); return -1; }
    close (pr->fd);
    if ((pr->fd = open (ppath, O_RDONLY)) < 0) { perror (ppath); return -1; }
    unlink (ppath);
    free (pr->buf);
    pr->buf = NULL;
    pr->cap = pr->len = 0;
    pr->off = pr->punched = 0;
    pr->discard = 0;
    return 0;
}

static int open_proof (void *solver, Proof *pr)
{
    char ppath[PATH_MAX];
    proof_path (ppath, sizeof ppath);
    pr->f = fopen (ppath, "w+");
    pr->fd = pr->f ? open (ppath, O_RDONLY) : -1;
    if (!pr->f || pr->fd < 0) { perror (ppath); return -1; }
    unlink (ppath);
    if (!ccadical_trace_proof (solver, pr->f, ppath)) {
        fprintf (stderr, "cubical: could not connect the proof\n");
        return -1;
    }
    return 0;
}

/* Size the counters to the formula and hand CaDiCaL its callbacks. */
static int init_counts (Counts *c, void *solver, int nvars)
{
    size_t nv = (size_t) nvars + 1;
    c->nvars = nvars;
    c->ncore = -1;
    c->keep  = opt_minsplit;
    c->core    = xzalloc (nv * sizeof *c->core);
    c->pos     = xzalloc (nv * sizeof *c->pos);
    c->neg     = xzalloc (nv * sizeof *c->neg);
    c->touched = xalloc (NULL, nv * sizeof *c->touched);
    c->seen    = xzalloc (nv * sizeof *c->seen);
    c->incube  = xzalloc (nv * sizeof *c->incube);
    c->val     = xzalloc (nv * sizeof *c->val);
    c->trail   = xalloc (NULL, (nv + 1) * sizeof *c->trail);
    /* The shim reaches the Solver by assuming ccadical's Wrapper layout.
     * Check it against an accessor whose answer has content: vars() is the
     * formula's variable count, which we already know, so a wrong offset
     * cannot pass by agreeing on zero -- which, before the first solve, is
     * all fixed() returns for any variable that is not an input unit. */
    if (cubical_vars (solver) != nvars || ccadical_vars (solver) != nvars) {
        fprintf (stderr, "cubical: shim sees %d variables and ccadical sees "
                 "%d, but the formula has %d; refusing to run\n",
                 cubical_vars (solver), ccadical_vars (solver), nvars);
        return -1;
    }
    for (int v = 1; v <= nvars && v <= 64; v++)
        if (cubical_fixed (solver, v) != ccadical_fixed (solver, v)) {
            fprintf (stderr, "cubical: shim disagrees with ccadical_fixed "
                             "on x%d; refusing to run\n", v);
            return -1;
        }
    /* INT_MAX: every clause must be reported or the count is not conflicts.
     * CaDiCaL copies each into a buffer to hand it over, which is the price
     * of the counter -- nothing is kept. */
    ipasir_set_learn (solver, c, INT_MAX, count_conflict);
    ipasir_set_terminate (solver, c, on_terminate);
    return 0;
}

static void counts_free (Counts *c)
{
    free (c->proof.buf); free (c->proof.lbuf);
    free (c->core); free (c->pos); free (c->neg);
    free (c->touched); free (c->seen); free (c->incube);
    free (c->val); free (c->trail);
    cs_free (&c->cap);
}

/* --------------------------------------------------------------- output -- */

static void usage (void)
{
    printf (
"usage: cubical [options] [file.cnf]   (version " CUBICAL_VERSION ")\n"
"\n"
"Reads DIMACS CNF from file.cnf, or from stdin if omitted.  Exit status\n"
"is 10 SATISFIABLE, 20 UNSATISFIABLE, 0 if the search did not finish.\n"
"\n"
"splitting\n"
"  --ramp-conflicts <k> 100000   phase 1: conflicts a node above the ramp\n"
"                                depth runs before it splits on its best\n"
"                                variable, whatever that variable scores\n"
"  --ramp-depth <d>       auto   depth phase 1 ends and phase 2 begins.\n"
"                                auto is ceil(log2(--cores)), so the ramp\n"
"                                alone fills the workers; 0 turns it off\n"
"  --percentile <p>         50   phase 2: split only if the best variable\n"
"                                beats the p-th percentile of the scores\n"
"                                this node's ancestors split on.  50 is the\n"
"                                median; higher splits less\n"
"  --cover <pct>            off   phase 2, the absolute alternative: split\n"
"                                only if the best score beats pct, with no\n"
"                                reference to the path above.  Same units as\n"
"                                the log's cover%% and bar%% columns.  Not\n"
"                                combinable with --percentile\n"
"  -t <t>                    0   order of the power mean combining a\n"
"                                variable's two polarity weights: 1\n"
"                                arithmetic, 0 geometric, -inf minimum.\n"
"                                Lower t penalises imbalance, so splits less\n"
"  --min-split <n>      100000   do not split a node holding fewer clauses of\n"
"                                collected proof, inherited or derived\n"
"  --max-depth <n>        1000   stop splitting at this depth; a node there\n"
"                                still solves to a verdict\n"

"  --split-idle            off   let --max-depth yield to demand: a node at\n"
"                                the cap may still split while a worker is\n"
"                                idle, since an extra split costs work and\n"
"                                work is only scarce when cores are busy\n"
"\n"
"polling\n"
"  --poll-every <n>      10000   conflicts between phase-2 checks.  Every\n"
"                                node also polls once the moment it starts,\n"
"                                whatever its phase\n"
"\n"
"proof\n"
"  --carry-mb <n>         2048   ceiling in MB on the proof carried into a\n"
"                                node, per worker; past it the oldest clauses\n"
"                                are dropped\n"
"  --proof-dir <d>    /dev/shm   directory for CaDiCaL's DRAT trace, else\n"
"                                $TMPDIR, else /tmp.  $CUBICAL_PROOF_DIR\n"
"                                sets the same thing\n"
"\n"
"solving\n"
"  --cores <n>               1   solve on n worker processes; 1 is sequential\n"
"                                and reproducible\n"
"  --share <0|1>             1   with --cores, workers exchange refutation\n"
"                                cores\n"
"  --learn-cores            on   add the negated assumption core to the\n"
"                                formula after each refutation;\n"
"                                --no-learn-cores disables\n"
"  --seed <n>                0   CaDiCaL random seed\n"
"  --opt name=<int>              set any other CaDiCaL option; at most 32\n"
"\n"
"output\n"
"  --cube-log <f>                write the node log to f as well as stdout\n"
"  --trace                       print one line per poll and never split;\n"
"                                implies --quiet\n"
"  -q, --quiet                   write nothing to stdout\n"
"  -h, --help\n"
"  --version\n");
}

/* Everything constant for the whole run, once, instead of a column repeated on
 * every line. */
static void banner (const Counts *c, int nvars, long long nclauses)
{
    (void) c;
    /* Digits of the largest variable, plus one for the sign, so no cube
     * literal can push its own share out of column. */
    g_litw = 1 + snprintf (NULL, 0, "%d", nvars);      /* plus a sign column */
    if (opt_trace) {
        printf ("c trace output\n");
        printf ("%-10s %-10s %-10s %-10s %-20s %-10s %-10s %-10s %-10s"
                " %-10s %-10s %-10s\n",
                "N", "cbest", "c2nd", "best", "avg lits/clause", "touched",
                "above", "n90", "n50", "m90", "m50", "mtot");
    }
    /* Format is fixed in its first two fields: the sweep plotters read the
     * version and t off this line, and a sweep's cells differ in nothing else.
     *
     * The criterion field names whichever criterion is ACTUALLY driving the
     * run.  It used to print percentile=%d unconditionally, which under
     * --cover reported percentile=50 -- the default, never consulted -- so a
     * cover run was indistinguishable from a median-percentile one on the line
     * every reader looks at first.  `c phase 2` below always spelled it out,
     * but nothing that skims a log reads that far.  --cover is echoed in the
     * units it was GIVEN in (a percentage; it is stored as a fraction). */
    if (opt_cover >= 0.0)
        emit ("c cubical   version %s  t=%g%s  cover=%.4g%% (--cover)"
              "  seed=%d\n",
              CUBICAL_VERSION, opt_t, score_alias (opt_t),
              100.0 * opt_cover, opt_seed);
    else
        emit ("c cubical   version %s  t=%g%s  percentile=%d  seed=%d\n",
              CUBICAL_VERSION, opt_t, score_alias (opt_t), opt_pct, opt_seed);
    emit ("c formula   %d vars  %lld clauses\n", nvars, nclauses);
    /* The two phases in the order a node meets them, with the cube count the
     * ramp produces on its own: that is the number to hold against --cores
     * when a run comes out with idle workers. */
    if (g_ramp > 0)
        emit ("c phase 1   ramp to depth %d (%s), %lld conflicts per node,"
              " always split -> %.0f cubes\n", g_ramp,
              opt_rampdepth >= 0 ? "--ramp-depth" : "from --cores",
              opt_rampk, pow (2.0, (double) g_ramp));
    else
        emit ("c phase 1   no ramp (%s)\n",
              opt_rampdepth == 0 ? "--ramp-depth 0" : "one core needs none");
    if (opt_cover >= 0.0)
        emit ("c phase 2   split above an absolute score of %.3f%% (--cover),"
              " the same bar at every node and depth, re-checked every %lld"
              " conflicts\n", 100.0 * opt_cover, opt_pollint);
    else
        emit ("c phase 2   split above the %d-th percentile of the ancestors'"
              " scores, re-checked every %lld conflicts\n",
              opt_pct, opt_pollint);
    emit ("c limits    min-split %lld  max-depth %d%s  carry %lld MB/%s\n",
          opt_minsplit, opt_maxdepth,
          opt_splitidle ? " (yields while a worker is idle)" : "",
          opt_cap >> 20, opt_cores > 1 ? "worker" : "node");
    emit ("c proof     DRAT trace under %s, unlinked\n", proof_dir ());
    if (opt_cores > 1)
        emit ("c workers   %d; node ids are id*%d+worker\n",
              opt_cores, opt_cores);
    if (opt_learn)
        emit ("c learn     negated assumption cores added as irredundant"
              " clauses\n");
    if (opt_cores > 1 && opt_share)
        emit ("c share     refutation cores traded through %d MB of shared"
              " memory\n", (int) (SHARE_INTS * sizeof (int) >> 20));
    emit ("c legend    ph = 1 ramp (always splits, so bar 0) or 2 percentile."
          "  The two\n"
          "c           variable columns sit together so a disagreement is"
          " visible: var is\n"
          "c           what this node split on and var0 the argmax on the proof"
          " it INHERITED,\n"
          "c           read at conf0 conflicts, before it derived any of its"
          " own.\n"
          "c           cover%%/cov0 are var's and var0's\n"
          "c           scores; bar%% is what var had to beat and nanc the"
          " ancestor scores\n"
          "c           it was taken over, which at 1 or 2 the log should not"
          " hide.\n"
          "c             clauses = the set the score was read off, len its mean"
          " literals per\n"
          "c           clause, fresh the part this node derived itself and the"
          " denominator\n"
          "c           of the cube shares.  A split removes ONE literal from a"
          " clause, so on\n"
          "c           a long-clause set it decomposes nothing propagation can"
          " use.\n"
          "c             s+%%/s-%% = the two children's surviving proof.  max of"
          " them is the\n"
          "c           WORST branch, which is the critical path the split is"
          " bought with;\n"
          "c           their ratio is the realized balance.  bal =\n"
          "c           var's polarity balance in the COUNTS, which is what -t"
          " scores --\n"
          "c           held against s+/s- it says whether that proxy was right"
          " here.\n"
          "c             trail = literals this node's cube implied beyond"
          " itself; thousands\n"
          "c           implied with nothing removed marks candidates that are"
          " one decision\n"
          "c           in disguise.  cube lit(share%%): share = %% of this"
          " node's own proof\n"
          "c           naming that variable.  = entailed second branch, not"
          " assumed here.\n"
          "c           On a refuted leaf * = core literal, . = not (green/red"
          " on a tty).\n"
          "c           STATUS on stderr = the node in progress.\n");
    emit ("c\n");
    emit ("c %3s %7s %7s %5s %2s %-6s %10s %8s %6s %8s %8s %9s %6s %6s"
          " %7s %7s %10s %7s %5s %6s %6s %5s %8s %5s %6s %s\n",
          "wrk", "node", "parent", "depth", "ph", "event", "conflicts",
          "clauses", "len", "fresh", "node-s", "total-s",
          "var", "var0", "cover%", "cov0", "conf0", "bar%", "nanc",
          "s+%", "s-%", "bal", "trail", "evict", "core",
          " cube: lit(share%)");
}

/* The run, in the same one-place-per-line style as row(). */
static void summary (const Stats *s, double total, int result)
{
    emit ("c\n");
    emit ("c nodes       %8lld   (%lld splits, %lld leaves)\n",
          s->nodes, s->splits, s->leaves);
    emit ("c max depth   %8lld\n", s->maxdepth);
    emit ("c conflicts   %8lld   (hardest leaf: %lld conf at node %lld)\n",
          s->totconf, s->maxleafconf, s->maxleafnode);
    /* total is wall clock; tsplit and tleaf are summed over the workers, so
     * with --cores they routinely exceed it.  Saying which is which stops the
     * components looking like they overflow the whole. */
    if (s->cpu > 0.0)
        emit ("c time        %8.2fs  wall  (%.2fs splitting + %.2fs in leaves,"
              " summed over workers)\n", total, s->tsplit, s->tleaf);
    else
        emit ("c time        %8.2fs  (%.2fs splitting, %.2fs in leaves)\n",
              total, s->tsplit, s->tleaf);
    if (s->cpu > 0.0 && total > 0.0)
        emit ("c busy        %8.2f   cores on average, of %d (%.0f%% of what"
              " was asked for)\n", s->cpu / total, opt_cores,
              100.0 * s->cpu / total / opt_cores);
    emit ("c crit path   %8.2fs  (%.2fs deciding the splits above node %lld,"
          " %.2fs in it)\n", s->crit, s->crit_above, s->critnode, s->crit_own);
    /* How much of the cube each refutation actually needed -- the one number
     * that judges the splitting rather than the solving.  The gap is literals
     * the tree spent a level on and the proof then ignored, so a cube of 5
     * closed by a core of 2 says three levels -- eight times the leaves --
     * bought nothing on that path.  Decided literals only -- see decided().
     * Counting the second branch of each split made this track the shape of the
     * tree instead of the choice of variable: those literals are entailed
     * before their node starts, so they can never be in a core, and the deeper
     * the tree the more of them a cube holds.  Having them in the denominator
     * was the difference between reading these splits as half wasted and
     * reading them, correctly, as spending nothing they did not use. */
    if (s->coreleaves)
        emit ("c core        %8.2f   of %.2f decided cube literals needed per"
              " refuted leaf (%.2f dead)%s\n",
              (double) s->corelits / (double) s->coreleaves,
              (double) s->decidedlits / (double) s->coreleaves,
              (double) (s->decidedlits - s->corelits) / (double) s->coreleaves,
              s->emptycore ? ", some refuted with no assumption at all" : "");
    if (opt_learn)
        emit ("c learned     %8lld   core clauses added to the formula"
              " (%.2f literals each)\n", s->learned,
              s->learned ? (double) s->learnedlits / (double) s->learned : 0.0);
    if (s->nofail)
        emit ("c nofail      %8lld   refuted using no assumption at all, first"
              " at node %lld of %lld\n", s->nofail, s->nofailnode, s->nodes);
    if (s->shared_in)
        emit ("c shared      %8lld   cores taken from other workers%s\n",
              s->shared_in, g_sh && g_sh->sfull ? ", ring filled" : "");
    if (s->donated || s->taken)
        emit ("c donated     %8lld   cubes handed to an idle worker (%lld taken)\n",
              s->donated, s->taken);
    emit ("c\n");
    emit ("s %s\n", result == 10 ? "SATISFIABLE"
                    : result == 20 ? "UNSATISFIABLE" : "UNKNOWN");
}

/* ----------------------------------------------------------- arguments -- */

static const char *onames[32];
static int ovals[32], nopt;

/* Used for every float option.  strtod and not atof: atof returns 0 for
 * anything it cannot parse and 0 is a valid t, so "-t <typo>" would select the
 * geometric mean instead of being rejected.  strtod reads "inf" and "-inf"
 * itself; nan must be rejected, since it makes every comparison in evaluate ()
 * false and so never splits. */
static int parse_num (const char *v, double *out)
{
    char *end;
    double x = strtod (v, &end);
    if (end == v || *end || isnan (x)) return -1;
    *out = x;
    return 0;
}

/* Likewise for the integer options.  --seed and --share have no range for
 * check_opts to catch a misread 0 against. */
static int parse_int (const char *v, long long lo, long long hi, long long *out)
{
    char *end;
    errno = 0;
    long long x = strtoll (v, &end, 10);
    if (end == v || *end || errno || x < lo || x > hi) return -1;
    *out = x;
    return 0;
}

/* The two criteria are alternatives for the same decision, and each has a
 * range outside which it could never fire -- which would look like a run that
 * simply never splits.  Reject those here instead. */
static int ramp_depth (void)
{
    if (opt_rampdepth >= 0) return opt_rampdepth;
    int d = 0;
    while (d < 30 && (1 << d) < opt_cores) d++;
    return d;
}

static int check_opts (void)
{
    /* Every t that parse_num accepts is meaningful, both infinities included,
     * so there is nothing to reject -- only the two constants score_of reads
     * instead of recomputing them per variable. */
    g_bnorm = 1.0 / balance_max (opt_t);
    g_plain = (opt_t == 1.0);
    /* A donation packs the ancestor scores into the same int buffer as the
     * literals, one slot each, so the two types have to be the same width.
     * They are on every target this builds for; checked here rather than
     * trusted, since the failure would be a silently mis-parsed payload and
     * so a wrong bar on a donated subtree. */
    if (sizeof (float) != sizeof (int)) {
        fprintf (stderr, "cubical: float and int differ in size on this"
                 " target, which the donation payload assumes\n");
        return -1;
    }
    /* A non-positive ceiling makes every clause overflow the set, so cs_evict
     * would run on each one and the --min-split floor would refuse every
     * time. */
    if (opt_cap < (1LL << 20)) {
        fprintf (stderr, "cubical: --carry-mb must be at least 1\n");
        return -1;
    }
    if (opt_pollint < 1 || opt_minsplit < 1) {
        fprintf (stderr, "cubical: --poll-every and --min-split must be at"
                 " least 1\n");
        return -1;
    }
    if (opt_rampk < 1) {
        fprintf (stderr, "cubical: --ramp-conflicts must be at least 1 --"
                 " use --ramp-depth 0 to turn the ramp off\n");
        return -1;
    }
    /* 0 and 100 are the sample's min and max, which are meaningful bars: 0
     * splits wherever any ancestor was ever beaten, 100 demands the best
     * ancestor be beaten.  Outside that there is no sample to interpolate
     * into. */
    if (opt_pct < 0 || opt_pct > 100) {
        fprintf (stderr, "cubical: --percentile %d is outside [0, 100]\n",
                 opt_pct);
        return -1;
    }
    /* cs_evict may not drop below --min-split, so a set that cannot hold that
     * many clauses can never drop one and cs_reserve grows past --carry-mb
     * instead.  Six ints per clause is the low end of what the sets hold. */
    if (opt_minsplit * 6 * (long long) sizeof (int) > opt_cap) {
        fprintf (stderr, "cubical: --min-split %lld clauses needs more than"
                 " --carry-mb %lld to stay inside the ceiling\n",
                 opt_minsplit, opt_cap >> 20);
        return -1;
    }
    if (opt_maxdepth < 1) {
        fprintf (stderr, "cubical: --max-depth must be at least 1\n");
        return -1;
    }
    /* Each worker carries its own proof set, so --carry-mb is a per-worker
     * ceiling and the run's footprint is cores x that plus one solver each. */
    if (opt_cores < 1) {
        fprintf (stderr, "cubical: --cores must be at least 1\n");
        return -1;
    }
    /* Two bars, one gate.  Refused rather than ordered: whichever won, the
     * other option would be sitting in the command line doing nothing, and a
     * sweep that thinks it moved the percentile while --cover is in force
     * produces a column of identical numbers with no hint why. */
    if (opt_cover >= 0.0 && pct_given) {
        fprintf (stderr, "cubical: --cover and --percentile are the two"
                 " alternatives for the phase-2 bar -- pass one\n");
        return -1;
    }

    g_ramp = ramp_depth ();
    /* A ramp deeper than the cap would ask for splits --max-depth refuses,
     * and a forced split that cannot happen is not a phase, it is a stall:
     * those nodes would solve to a verdict at the cap and the tree would stop
     * there with no percentile ever consulted.  Clamped rather than refused,
     * since --max-depth is the harder of the two statements. */
    if (g_ramp > opt_maxdepth) {
        fprintf (stderr, "cubical: ramp depth %d is past --max-depth %d --"
                 " ramping to %d instead\n", g_ramp, opt_maxdepth,
                 opt_maxdepth);
        g_ramp = opt_maxdepth;
    }
    return 0;
}

/* 0 = go, 1 = exit success, -1 = exit failure.  Every option taking a value
 * requires one and every numeric value must parse; both used to fall back on
 * the default, which runs a configuration other than the one asked for. */
static int parse_args (int argc, char **argv, const char **path)
{
#define ARG() (i + 1 < argc ? argv[++i] : NULL)
#define NEED(v) do { if (!((v) = ARG ())) goto missing; } while (0)
#define INT(dst, l, h) do {                              \
        long long n;                                     \
        NEED (v);                                        \
        lo = (l); hi = (h);                              \
        if (parse_int (v, lo, hi, &n) < 0) goto notint;   \
        (dst) = n;                                       \
    } while (0)
    char *a = NULL, *v = NULL;
    long long lo = 0, hi = 0;
    for (int i = 1; i < argc; i++) {
        a = argv[i];
        /* 0 is accepted here and refused in check_opts, which can say what to
         * use instead: a zero budget reads as "turn the ramp off", and the
         * knob that does that is --ramp-depth. */
        if      (!strcmp (a, "--ramp-conflicts"))
                                              INT (opt_rampk, 0, LLONG_MAX);
        else if (!strcmp (a, "--ramp-depth"))  INT (opt_rampdepth, 0, INT_MAX);
        else if (!strcmp (a, "--percentile")) {
            INT (opt_pct, 0, 100); pct_given = 1;
        }
        /* Taken as a percentage and stored as the fraction the score is in, so
         * the value a run is given is the value its rows print as bar%. */
        else if (!strcmp (a, "--cover")) {
            NEED (v);
            double pc;
            if (parse_num (v, &pc) < 0 || !(pc >= 0.0) || pc > 100.0) {
                fprintf (stderr, "cubical: --cover wants a percentage in"
                         " [0,100], not '%s'\n", v);
                return -1;
            }
            opt_cover = pc / 100.0;
        }
        else if (!strcmp (a, "-t")) {
            NEED (v);
            if (parse_num (v, &opt_t) < 0) {
                fprintf (stderr, "cubical: -t wants a number, 'inf' or"
                         " '-inf', not '%s'\n", v);
                return -1;
            }
        }
        else if (!strcmp (a, "--learn-cores"))    opt_learn = 1;
        else if (!strcmp (a, "--no-learn-cores")) opt_learn = 0;
        /* Capped where the shift would overflow into a negative ceiling. */
        else if (!strcmp (a, "--carry-mb")) {
            long long mb;
            INT (mb, 1, LLONG_MAX >> 20);
            opt_cap = mb << 20;
        }
        else if (!strcmp (a, "--poll-every"))  INT (opt_pollint, 1, LLONG_MAX);
        else if (!strcmp (a, "--min-split"))   INT (opt_minsplit, 1, LLONG_MAX);
        else if (!strcmp (a, "--max-depth"))   INT (opt_maxdepth, 1, INT_MAX);
        else if (!strcmp (a, "--split-idle"))    opt_splitidle = 1;
        else if (!strcmp (a, "--no-split-idle")) opt_splitidle = 0;
        else if (!strcmp (a, "--cube-log"))  { NEED (v); opt_log = v; }
        else if (!strcmp (a, "--proof-dir")) { NEED (v); opt_proofdir = v; }
        else if (!strcmp (a, "--cores"))       INT (opt_cores, 1, INT_MAX);
        else if (!strcmp (a, "--share"))       INT (opt_share, 0, 1);
        else if (!strcmp (a, "--seed"))        INT (opt_seed, INT_MIN, INT_MAX);
        /* CaDiCaL rejects an unknown name, so only the shape is checked
         * here.  A dropped --opt would run the wrong configuration. */
        else if (!strcmp (a, "--opt")) {
            NEED (v);
            char *eq = strchr (v, '=');
            long long n;
            if (!eq || parse_int (eq + 1, INT_MIN, INT_MAX, &n) < 0) {
                fprintf (stderr, "cubical: --opt wants name=<integer>, not"
                         " '%s'\n", v);
                return -1;
            }
            if (nopt == (int) (sizeof onames / sizeof *onames)) {
                fprintf (stderr, "cubical: at most %d --opt settings\n",
                         (int) (sizeof onames / sizeof *onames));
                return -1;
            }
            *eq = 0; onames[nopt] = v; ovals[nopt++] = (int) n;
        }
        else if (!strcmp (a, "--trace")) { opt_trace = 1; opt_quiet = 1; }
        else if (!strcmp (a, "-q") || !strcmp (a, "--quiet")) opt_quiet = 1;
        else if (!strcmp (a, "-h") || !strcmp (a, "--help")) { usage (); return 1; }
        else if (!strcmp (a, "--version")) {
            printf ("cubical %s\n", CUBICAL_VERSION);
            return 1;
        }
        else if (a[0] == '-' && a[1]) {
            fprintf (stderr, "cubical: unknown option %s"
                     " (--help lists them)\n", a);
            return -1;
        }
        /* A second path is a typo, not a second formula. */
        else if (*path) {
            fprintf (stderr, "cubical: more than one input file"
                     " (%s and %s)\n", *path, a);
            return -1;
        }
        else *path = a;
    }
#undef INT
#undef NUM
#undef NEED
#undef ARG
    return check_opts ();

missing:
    fprintf (stderr, "cubical: %s wants a value\n", a);
    return -1;
notint:
    fprintf (stderr, "cubical: %s wants an integer in [%lld, %lld], not"
             " '%s'\n", a, lo, hi, v);
    return -1;
}

/* ------------------------------------------------------------ the tree -- */

/* Clear the counts, set the cube as assumptions and bring the parent's proof
 * in. */
static void node_begin (Counts *c, void *solver, Cube *cube)
{
    /* Drop the last node's set before the reset, so the proof tail the reset
     * drains cannot be appended to a set that is about to be freed. */
    cs_free (&c->cap);
    node_reset (c);
    for (int i = 0; i < cube->n; i++) {
        c->incube[var_of (cube->lits[i])] = 1;
        ipasir_assume (solver, cube->lits[i]);
    }
    c->cube = cube;           /* before carry_in, whose propagate() can poll */
    /* All of these before carry_in too: propagate () re-enters the solve path
     * and so can reach the terminator, which polls -- and a poll that ran
     * against the previous node's phase and bar would decide this node on
     * them. */
    c->phase = cube->depth < g_ramp ? 1 : 2;
    c->depth = cube->depth;
    c->nanc  = cube->nanc;
    c->thresh = c->phase == 1 ? 0.0
              : opt_cover >= 0.0 ? opt_cover
              : percentile (cube->anc, cube->nanc, opt_pct);
    carry_in (c, solver, cube->cls, cube->lits, cube->n);
    if (cube->cls) {                                 /* read, not taken */
        cs_free (cube->cls); free (cube->cls); cube->cls = NULL;
    }
}

/* Which of the cube's literals the refutation actually needed.  Only
 * meaningful right here: valid after an UNSAT and before the next assume,
 * since CaDiCaL clears the failed flags when the next incremental phase
 * starts.  The first ipasir_failed call is what makes CaDiCaL run failing() at
 * all -- it computes the core, checks it and drops it -- so nothing here is
 * paid unless we ask.  It hands the core to the proof tracer too, but DRAT
 * overrides neither add_assumption_clause nor conclude_unsat, so the stream we
 * read is untouched. */
/* Hand one cube to an idle worker.
 *
 * The shallowest cube on the stack goes, not the deepest: it roots the largest
 * subtree, so the copy is amortised over the most work, and it is the one
 * furthest from where this worker is now -- it keeps its own hot region and
 * the solver state that suits it.
 *
 * Returns 1 if the cube was taken over, in which case the caller must drop it
 * from its own stack without freeing the payload twice. */
static int donate (Cube *cube)
{
    if (!g_sh) return 0;
    /* One float per ancestor, one int per literal: sizeof (float) ==
     * sizeof (int) on every target this builds for, which a static assert in
     * check_opts pins down rather than leaving to the reader. */
    long long fixed = (long long) cube->n + cube->nanc;
    long long nmem = cube->cls ? cube->cls->nmem : 0;
    if (fixed + nmem > DON_INTS) nmem = 0;            /* literals and scores */
    if (fixed > DON_INTS) return 0;                   /* cannot go at all    */

    for (int i = 0; i < DON_SLOTS; i++) {
        Donation *d = &g_sh->don[i];
        if (!__sync_bool_compare_and_swap (&d->state, 0, -1)) continue;
        d->n = cube->n; d->depth = cube->depth; d->cp = cube->cp;
        d->nanc = cube->nanc;
        d->nmem = nmem; d->ncls = nmem ? cube->cls->n : 0;
        memcpy (d->buf, cube->lits, (size_t) cube->n * sizeof (int));
        if (cube->nanc)
            memcpy (d->buf + cube->n, cube->anc,
                    (size_t) cube->nanc * sizeof (float));
        if (nmem) memcpy (d->buf + fixed, cube->cls->mem,
                          (size_t) nmem * sizeof (int));
        __sync_synchronize ();
        d->state = 1;                                  /* publishes the slot */
        return 1;
    }
    return 0;                                          /* every slot busy */
}

/* Take a donated cube, if one is waiting.  Builds it on `out` with freshly
 * owned memory, so it lives and dies like any other cube on this worker's
 * stack. */
static int accept_donation (Cube *out)
{
    if (!g_sh) return 0;
    for (int i = 0; i < DON_SLOTS; i++) {
        Donation *d = &g_sh->don[i];
        if (!__sync_bool_compare_and_swap (&d->state, 1, -2)) continue;
        memset (out, 0, sizeof *out);
        out->n = d->n; out->depth = d->depth; out->cp = d->cp;
        out->parent = -1;                      /* its parent ran elsewhere */
        out->lits = xalloc (NULL, (size_t) d->n * sizeof (int));
        memcpy (out->lits, d->buf, (size_t) d->n * sizeof (int));
        out->nanc = d->nanc;
        if (d->nanc) {
            out->anc = xalloc (NULL, (size_t) d->nanc * sizeof (float));
            memcpy (out->anc, d->buf + d->n, (size_t) d->nanc * sizeof (float));
        }
        /* second says "this level's sibling subtree was refuted before this
         * node started", which holds only while one depth-first stack owns the
         * whole tree.  A donated cube is taken from the BOTTOM of the donor's
         * stack and its siblings are still being explored, so the flags cannot
         * be carried: they would claim an entailment that has not happened and
         * quietly drop those literals out of the core denominator.  Zeroed, so
         * the taker counts every literal as one it decided -- conservative,
         * and the only thing it can honestly say.
         *
         * CaDiCaL's fixed() is not an alternative: it reports level-0 units,
         * and an entailed second literal is usually not one, so it marks far
         * fewer literals than the tree does. */
        out->second = xzalloc ((size_t) d->n * sizeof *out->second);
        if (d->nmem) {
            ClauseSet *cs = xzalloc (sizeof *cs);
            cs->mem = xalloc (NULL, (size_t) d->nmem * sizeof (int));
            memcpy (cs->mem, d->buf + d->n + d->nanc,
                    (size_t) d->nmem * sizeof (int));
            cs->nmem = cs->mcap = d->nmem;
            cs->n = d->ncls;
            out->cls = cs;
        }
        __sync_synchronize ();
        d->state = 0;                                  /* frees the slot */
        return 1;
    }
    return 0;
}

/* Publish one refutation core for the other workers.
 *
 * The clause is the negation of the assumptions the refutation actually used,
 * which the formula entails -- the same clause --learn-cores adds locally, and
 * sound for exactly the same reason.  So it needs no provenance: any worker
 * can add it to its own solver at any time.
 *
 * Reserve first, then fill, then publish the length last behind a barrier: a
 * reader must never see a length for literals that are not written yet.  A
 * record reserved earlier but published later simply stalls the readers at
 * that slot until it lands, which costs nothing but a little delay. */
static void share_core (const Cube *cube, const signed char *core, int nfail)
{
    if (!g_sh || !opt_share || nfail <= 0 || g_sh->sfull) return;
    int need = nfail + 2;
    int pos = __sync_fetch_and_add (&g_sh->shead, need);
    if (pos + need > SHARE_INTS) { g_sh->sfull = 1; return; }
    int k = pos + 2;
    for (int i = 0; i < cube->n; i++)
        if (core[i]) g_sh->sbuf[k++] = -cube->lits[i];
    g_sh->sbuf[pos + 1] = g_wid;
    __sync_synchronize ();
    g_sh->sbuf[pos] = nfail;            /* publishes the record */
}

static void read_core (Counts *c, void *solver, const Cube *cube, Stats *st)
{
    int nfail = 0;
    c->ncore = 0;
    for (int i = 0; i < cube->n; i++) {
        /* failed() alone, with nothing filtered out of it: the clause below is
         * only entailed if it negates every assumption the refutation used, so
         * dropping one here would learn a clause the formula does not imply.
         * The count is a different question -- it judges the splitting, and a
         * second child decided nothing to judge -- so ncore leaves those out
         * while the clause keeps them.  In every run checked, failed() never
         * reported one anyway: an entailed literal is satisfied before it is
         * ever assumed, and failing() skips a satisfied assumption. */
        c->core[i] = ipasir_failed (solver, cube->lits[i]) ? 1 : 0;
        nfail += c->core[i];
        c->ncore += c->core[i] && !cube->second[i];
    }
    st->coreleaves++;
    st->corelits += c->ncore;
    st->decidedlits += decided (cube);
    if (cube->n && !c->ncore) st->emptycore++;
    /* No assumption at all was used, so the refutation did not depend on this
     * cube: the formula on its own is unsatisfiable and every other cube is
     * moot.  Counted here to find out how often that happens before acting
     * on it. */
    if (cube->n && !nfail) {
        if (!st->nofail) st->nofailnode = st->nodes;
        st->nofail++;
    }
    /* The formula with the core literals is unsatisfiable, so it entails their
     * negations as a clause.  CaDiCaL derives that clause and drops it, since
     * "the conflict is forced already by some other clauses" (assume.cpp) --
     * but those are learned, hence redundant, hence what reduce() deletes,
     * where an ipasir_add clause is irredundant and permanent.  Adding it
     * turns a decaying implication spread over many learned clauses into one
     * clause of ncore literals, frequently two.
     *
     * Two loops, not one: every literal must leave failed() before the first
     * add(), which moves the solver out of the state where the flags are
     * queryable.  Not the empty core either -- the clause would be the empty
     * one, which is sound but a route nothing here takes yet. */
    share_core (cube, c->core, nfail);
    if (opt_learn && nfail) {
        for (int i = 0; i < cube->n; i++)
            if (c->core[i]) ipasir_add (solver, -cube->lits[i]);
        ipasir_add (solver, 0);
        st->learned++; st->learnedlits += nfail;
    }
}

/* The two children's surviving clause counts for the variable actually
 * chosen, so every split row carries the worst branch and the realized
 * balance.  Two passes over the set, once per split, against a node that has
 * run thousands of conflicts. */
static void measure_split (Counts *c, int var)
{
    long long nc, nl;
    c->val[var] = -1; cs_survive (&c->cap, c->val, &nc, &nl); c->surv_neg = nc;
    c->val[var] =  1; cs_survive (&c->cap, c->val, &nc, &nl); c->surv_pos = nc;
    c->val[var] = 0;
}

/* Both halves of the split go back on the worklist: a child cube is the
 * parent's plus one literal, so grow the parent's array by one and let push()
 * copy out of it.  -v first, so the +v branch, pushed last, is explored
 * first. */
static void split_node (Stack *work, Cube *cube, Counts *c, int var,
                        long long id, double cp)
{
    cube->lits = xalloc (cube->lits, ((size_t) cube->n + 1) * sizeof (int));
    for (int sgn = 0; sgn < 2; sgn++) {
        cube->lits[cube->n] = sgn ? var : -var;
        push (work, cube->lits, cube->n + 1, cube->depth + 1, id, cp);
        Cube *child = &work->v[work->n - 1];
        /* The branch each level took, carried down unchanged: sgn 0 is -var,
         * pushed first and so popped second.  Nothing recomputes this. */
        memcpy (child->second, cube->second, (size_t) cube->n * sizeof *child->second);
        child->second[cube->n] = sgn == 0;
        /* This node's ancestors, plus this node: the sample the child's bar
         * is a percentile of.  Appended and never rewritten, so a path's
         * sample is exactly the scores the splits above it were taken at --
         * including the ramp's, which is how phase 1 tunes phase 2. */
        child->nanc = cube->nanc + 1;
        child->anc = xalloc (NULL, (size_t) child->nanc * sizeof *child->anc);
        if (cube->nanc)
            memcpy (child->anc, cube->anc,
                    (size_t) cube->nanc * sizeof *child->anc);
        child->anc[cube->nanc] = (float) c->cbest;
        ClauseSet *t = xzalloc (sizeof *t);
        c->val[var] = sgn ? 1 : -1;                    /* the child's share */
        cs_reduce (&c->cap, c->val, t, NULL);
        c->val[var] = 0;
        child->cls = t;
    }
}

/* One depth-first sweep of `work`.
 *
 * Extracted from main so a parallel worker can run the same engine on its own
 * stack.  `want` > 0 pauses and returns 1 once the stack holds that many
 * cubes; 0 runs to the end.  --cores passes 1, which returns before any node
 * runs so the workers can be forked with only the root on the stack.
 * `wid`/`nw` renumber nodes as id*nw + wid so ids stay unique across workers
 * and a row's parent still resolves -- with nw == 1 that is the identity, so
 * a sequential run prints exactly what it always did.
 *
 * 10 SAT, 20 the stack emptied, 0 gave up or was stopped, 1 paused at `want`. */
static int run_tree (Stack *work, Counts *c, void *solver, Stats *st,
                     double t0, int want, int wid, int nw)
{
    while (work->n && !g_stop) {
        if (want && work->n >= want) return 1;
        st->shared_in += import_cores (solver);
        /* Only while someone is actually idle, and only if something would be
         * left here afterwards -- handing over the one cube we have would just
         * move the work, not share it. */
        if (g_sh && g_sh->want > 0 && work->n >= 2 && donate (&work->v[0])) {
            __sync_fetch_and_sub (&g_sh->want, 1);
            st->donated++;
            /* pop_free, not a field-by-field free: the taker built its own
             * copy of every buffer, so this one owns all of them still --
             * and a new field on Cube is otherwise leaked here and nowhere
             * else, which is how the ancestor scores were leaked once. */
            pop_free (&work->v[0]);
            memmove (work->v, work->v + 1, (size_t) (work->n - 1) * sizeof (Cube));
            work->n--;
            if (!work->n) break;
        }
        Cube cube = work->v[--work->n];
        long long nid = ++st->nodes;
        if (nw > 1) nid = nid * nw + wid;
        c->node = nid;
        if (cube.depth > st->maxdepth) st->maxdepth = cube.depth;
        node_begin (c, solver, &cube);

        double ts = c->node_t0 = cpu_time ();
        int res = ipasir_solve (solver);
        double dt = cpu_time () - ts;

        c->ncore = -1;
        if (res == 20) read_core (c, solver, &cube, st);
        st->totconf += c->nconf;
        for (int i = 0; i < cube.n; i++)             /* no poll can run now */
            c->incube[var_of (cube.lits[i])] = 0;

        /* Four outcomes, one report line.  A split is the only one that is
         * not a leaf, so the only one that does not end a branch of the
         * critical path here.  A node at --max-depth never fires -- evaluate
         * refuses before it can -- so it arrives here solved, not unfinished,
         * and there is no capped case to special-case. */
        int split = res != 10 && res != 20 && c->fire ? c->best : 0;
        /* After the solve returned, so the set is quiet and nothing here can
         * re-enter the solver, and before row (), so the measurement is in
         * the line that reports the split. */
        if (split) measure_split (c, split);
        if (split) { st->splits++; st->tsplit += dt; }
        else if (cube.cp + dt > st->crit) {
            st->crit = cube.cp + dt; st->crit_above = cube.cp;
            st->crit_own = dt; st->critnode = nid;
        }
        row (nid, &cube, res == 10 ? "SAT" : res == 20 ? "UNSAT"
                       : split ? "SPLIT" : "STOP", dt, cpu_time () - t0, c, split);

        if (split) split_node (work, &cube, c, split, nid, cube.cp + dt);
        c->cube = NULL;
        pop_free (&cube);

        if (split) continue;
        if (res == 20) {                             /* refuted: a leaf */
            st->leaves++; st->tleaf += dt;
            if (c->nconf > st->maxleafconf) {
                st->maxleafconf = c->nconf; st->maxleafnode = nid;
            }
            continue;
        }
        /* Neither solved nor refuted, and the node did not fire: the only
         * remaining way out of a solve is g_stop, which main reports as an
         * interrupt.  --max-depth cannot land here -- evaluate refuses to
         * fire at the cap, so a node there runs to a verdict. */
        return res == 10 ? 10 : 0;
    }
    return g_stop ? 0 : 20;
}

static void merge_stats (Stats *a, const Stats *b)
{
    a->nodes += b->nodes; a->splits += b->splits; a->leaves += b->leaves;
    a->totconf += b->totconf;
    a->coreleaves += b->coreleaves; a->corelits += b->corelits;
    a->decidedlits += b->decidedlits; a->emptycore += b->emptycore;
    if (b->nofail && (!a->nofail || b->nofailnode < a->nofailnode))
        a->nofailnode = b->nofailnode;
    a->nofail += b->nofail;
    a->learned += b->learned; a->learnedlits += b->learnedlits;
    a->shared_in += b->shared_in;
    a->donated += b->donated; a->taken += b->taken;
    /* cpu is deliberately not merged: the parent measures it once, for all. */
    a->tsplit += b->tsplit; a->tleaf += b->tleaf;
    if (b->maxdepth > a->maxdepth) a->maxdepth = b->maxdepth;
    if (b->maxleafconf > a->maxleafconf) {
        a->maxleafconf = b->maxleafconf; a->maxleafnode = b->maxleafnode;
    }
    /* The run's critical path is the longest of the workers'. */
    if (b->crit > a->crit) {
        a->crit = b->crit; a->crit_above = b->crit_above;
        a->crit_own = b->crit_own; a->critnode = b->critnode;
    }
}

/* Fork `--cores` workers.  One starts with the root; the rest wait, and get
 * cubes as the first worker splits and donates.
 *
 * Processes, not threads: the engine is single-threaded with file-scope state
 * and CaDiCaL is not reentrant across one instance, so forking sidesteps the
 * whole class of problem.  It also pays off -- a worker inherits the parsed
 * formula copy-on-write, so nothing is re-parsed.
 *
 * A worker runs the entire subtree under the cube it holds, which keeps
 * incremental learning along that branch -- the thing a per-cube hand-off
 * would lose -- and gives up work only when someone else has none.
 *
 * The one piece fork would corrupt is the proof: parent and child would share
 * one file description and interleave into it.  Each child closes the
 * inherited trace and opens its own -- open_proof keys the path on getpid(),
 * so the new one is distinct by construction. */
static int run_parallel (Stack *work, Counts *c, void *solver, Stats *st,
                         double t0)
{
    int nw = opt_cores, nfront = work->n;
    size_t sz = sizeof (Shared) + (size_t) nw * sizeof (Stats);
    Shared *sh = mmap (NULL, sz, PROT_READ | PROT_WRITE,
                       MAP_SHARED | MAP_ANONYMOUS, -1, 0);
    if (sh == MAP_FAILED) { perror ("mmap"); return 0; }
    memset (sh, 0, sz);
    sh->result = 20;

    emit ("c parallel   %d workers, starting from the root\n", nw);
    fflush (stdout);
    if (g_log) fflush (g_log);

    for (int w = 0; w < nw; w++) {
        pid_t pid = fork ();
        if (pid < 0) { perror ("fork"); break; }
        if (pid) continue;

        /* ---- worker ---- */
        g_sh = sh;
        g_wid = w;
        g_scur = 0;
        if (reopen_proof (&c->proof) < 0) _exit (1);

        Stats my;
        memset (&my, 0, sizeof my);
        Stack one;
        memset (&one, 0, sizeof one);
        one.v = xalloc (NULL, sizeof (Cube));
        one.cap = 1;
        int idle = 0;

        /* active counts the workers holding work.  A worker that runs dry
         * cannot just exit -- someone still busy may donate a moment later --
         * but it must not wait forever either.  Dropping out of active before
         * looking, and giving up only once active reaches zero, is what makes
         * that safe: a donation can only come from a worker that is still
         * counted, so active == 0 means no more can arrive. */
        __sync_fetch_and_add (&sh->active, 1);
        for (;;) {
            if (sh->stop) break;
            int got = 0;
            int idx = __sync_fetch_and_add (&sh->next, 1);
            if (idx < nfront) {
                one.v[0] = work->v[idx];   /* the child's own COW copy */
                one.n = 1; got = 1;
            } else {
                __sync_fetch_and_sub (&sh->next, 1);   /* undo the overshoot */
                if (accept_donation (&one.v[0])) { one.n = 1; got = 1; my.taken++; }
            }

            if (got) {
                if (idle) { __sync_fetch_and_add (&sh->active, 1); idle = 0; }
                int r = run_tree (&one, c, solver, &my, t0, 0, w, nw);
                /* A model settles the formula, so it is published
                 * unconditionally and overwrites anything already there.
                 *
                 * 0 is the case that needs care: run_tree returns it both for
                 * a worker that gave up on its own AND for one whose solve the
                 * terminator cut short because someone else had already set
                 * sh->stop.  Publishing it unconditionally let the second kind
                 * overwrite the very verdict that stopped it, which reported
                 * SATISFIABLE formulas as UNKNOWN whenever the race landed
                 * that way -- 4 of 14 formulas in a parallel fuzz run.  The
                 * compare-and-swap is what distinguishes them: only a worker
                 * that is the first to stop the run may say it reached no
                 * verdict. */
                if (r == 10) {
                    sh->result = 10;
                    __sync_synchronize ();
                    sh->stop = 1;
                    break;
                }
                if (r == 0) {
                    if (__sync_bool_compare_and_swap (&sh->stop, 0, 1))
                        sh->result = 0;
                    break;
                }
                continue;
            }

            if (!idle) {                      /* going idle: stop counting */
                __sync_fetch_and_sub (&sh->active, 1);
                __sync_fetch_and_add (&sh->want, 1);
                idle = 1;
            }
            if (!sh->active) break;           /* nobody left to donate */
            struct timespec ts = { 0, 2 * 1000 * 1000 };   /* 2 ms */
            nanosleep (&ts, NULL);
        }
        if (idle) __sync_fetch_and_sub (&sh->want, 1);
        else __sync_fetch_and_sub (&sh->active, 1);
        free (one.v);
        shared_stats (sh)[w] = my;
        if (g_log) fclose (g_log);
        fflush (stdout);
        _exit (0);                        /* never the parent's cleanup */
    }

    /* Every worker must exit 0.  sh->result starts at 20, so a worker that
     * died -- a failed reopen, a signal, the OOM killer -- would otherwise
     * leave the parent reporting UNSATISFIABLE for a search that never ran. */
    int wst, died = 0, reaped = 0;
    while (wait (&wst) > 0) {
        reaped++;
        if (!WIFEXITED (wst) || WEXITSTATUS (wst)) died++;
    }
    for (int w = 0; w < nw; w++) merge_stats (st, &shared_stats (sh)[w]);
    /* What the workers actually cost, against the clock.  Summing their own
     * measured solve times would miss everything outside a solve -- carrying
     * proof in, waiting for a donation -- and that is exactly the time this
     * number exists to expose. */
    struct rusage ru;
    st->cpu = 0;
    if (!getrusage (RUSAGE_CHILDREN, &ru))
        st->cpu += ru.ru_utime.tv_sec + 1e-6 * ru.ru_utime.tv_usec
                 + ru.ru_stime.tv_sec + 1e-6 * ru.ru_stime.tv_usec;
    if (!getrusage (RUSAGE_SELF, &ru))
        st->cpu += ru.ru_utime.tv_sec + 1e-6 * ru.ru_utime.tv_usec
                 + ru.ru_stime.tv_sec + 1e-6 * ru.ru_stime.tv_usec;

    /* One line per worker: an average hides a straggler, and a straggler is
     * the thing that caps a run like this. */
    emit ("c\nc %-7s %9s %9s %9s %9s %9s\n", "worker", "nodes", "splits",
          "leaves", "taken", "cores-in");
    for (int w = 0; w < nw; w++) {
        const Stats *b = &shared_stats (sh)[w];
        emit ("c %-7d %9lld %9lld %9lld %9lld %9lld\n", w,
              b->nodes, b->splits, b->leaves, b->taken, b->shared_in);
    }
    int r = sh->result;
    if (died || reaped < nw) {
        fprintf (stderr, "cubical: %d of %d workers failed -- no verdict\n",
                 died + (nw - reaped), nw);
        r = 0;
    }
    munmap (sh, sz);
    return r;
}

int main (int argc, char **argv)
{
    const char *path = NULL;
    int rc = parse_args (argc, argv, &path);
    if (rc) return rc < 0 ? 1 : 0;
    setvbuf (stdout, NULL, _IOLBF, 0);
    if (!getenv ("NO_COLOR")) { g_tty_out = isatty (1); g_tty_err = isatty (2); }

    /* Opened and line-buffered before anything is emitted, so the log really
     * does get the full output, and before any node runs, so a kill or a crash
     * loses at most the line in flight. */
    if (opt_log) {
        if (!(g_log = fopen (opt_log, "w"))) { perror (opt_log); return 1; }
        setvbuf (g_log, NULL, _IOLBF, 0);
    }

    /* Before the solver exists: nothing in it is needed to check this. */
    if (check_proof_dir () < 0) return 1;

    void *solver = ipasir_init ();
    /* Must precede every clause and solve: CaDiCaL only accepts it directly
     * after initialisation, which is also why open_proof cannot set it when a
     * worker reopens its trace. */
    int optbad = set_option (solver, "binary", 0) < 0
              || set_option (solver, "seed", opt_seed) < 0;
    for (int i = 0; i < nopt && !optbad; i++) {
        if (set_option (solver, onames[i], ovals[i]) < 0) { optbad = 1; break; }
        /* What CaDiCaL holds, read back, rather than what was asked for.  The
         * two agree -- set() said so -- and printing the authoritative one
         * means the log cannot claim a setting the solver does not have. */
        emit ("c option: %s=%d\n", onames[i],
              ccadical_get_option (solver, onames[i]));
    }
    if (optbad) {
        if (g_log) fclose (g_log);
        ipasir_release (solver);
        return 1;
    }

    /* Bad input unwinds rather than leaking the solver, so that `make debug`
     * reports no leaks on it. */
    Counts c;
    memset (&c, 0, sizeof c);
    int nvars = 0;
    long long nclauses = 0;
    if (open_proof (solver, &c.proof) < 0
        || read_cnf (path, solver, &nvars, &nclauses) < 0
        || init_counts (&c, solver, nvars) < 0) {
        if (g_log) fclose (g_log);
        if (c.proof.f) { ccadical_close_proof (solver); close (c.proof.fd); }
        counts_free (&c);
        ipasir_release (solver);
        return 1;
    }

    banner (&c, nvars, nclauses);

    signal (SIGINT, on_signal);
    signal (SIGTERM, on_signal);

    Stack work;
    memset (&work, 0, sizeof work);
    push (&work, NULL, 0, 0, -1, 0.0);

    Stats st;
    memset (&st, 0, sizeof st);
    double t0 = cpu_time ();
    int result = 20;

    c.t0 = c.last_status = t0;

    if (opt_cores > 1) {
        /* Fork before solving anything.  There used to be a frontier phase
         * here -- split sequentially until there were as many cubes as
         * workers, then hand them out -- which made the start of a run
         * special.  It is not: once idle workers can pull cubes out of busy
         * ones, one worker holding the root and the rest waiting is just the
         * steady state with the counters at their starting values, and the
         * pool fills itself from there.  Every cube built before the fork was
         * a sequential split nobody else could help with.  Measured on
         * 6g-17c at 4 cores: forking immediately 45.7s at 3.28 cores busy,
         * after 2 cubes 64.6s at 2.81, after 4 cubes 68.2s at 2.72. */
        result = run_tree (&work, &c, solver, &st, t0, 1, 0, 1);
        if (result == 1)
            result = run_parallel (&work, &c, solver, &st, t0);
        else
            /* Only reachable if a signal arrived before the first node. */
            emit ("c parallel   stopped before any worker started\n");
    } else
        result = run_tree (&work, &c, solver, &st, t0, 0, 0, 1);
    if (g_stop) {                    /* the tree is incomplete: not a verdict */
        fprintf (stderr, "c ... interrupted\n");
        result = 0;
    }
    summary (&st, cpu_time () - t0, result);

    if (g_log) fclose (g_log);
    ccadical_close_proof (solver);
    close (c.proof.fd);
    for (int i = 0; i < work.n; i++) pop_free (&work.v[i]);
    free (work.v);
    counts_free (&c);
    ipasir_release (solver);
    return result;
}
