# cubical

A cube-and-conquer SAT solver that decides where to split by reading the
solver's own proof.

Classical cube-and-conquer picks a splitting heuristic up front and cuts the
formula into a fixed number of cubes before solving any of them. cubical runs
CaDiCaL through IPASIR, watches the DRAT clauses the solver emits, and decides
each split from the proof the solver has produced so far. It runs in two
phases: a short ramp that splits unconditionally until there is a cube per
core, and then a main phase whose threshold is, by default, a percentile of what the splits
above it scored, so the bar comes from the instance rather than from a
constant.

The result is a tree whose shape is decided by the formula, a threshold with
nothing to calibrate from outside the run, and a per-node log that says what
each split was bought with.

- Reads DIMACS CNF, answers `s SATISFIABLE` / `s UNSATISFIABLE`.
- Parallel search on forked workers with work stealing (`--cores`).
- One line of log per node, with the evidence behind every split.

## Build

```sh
make
```

That is the whole thing. cubical links CaDiCaL statically through IPASIR, so
the first `make` clones CaDiCaL (pinned to `rel-3.0.1`) into `third_party/` and
builds it; later builds reuse it. You need `gcc`, `g++`, `make` and `git`, and
network access on the first build only.

To build against a CaDiCaL you already have:

```sh
make CADICAL_DIR=/path/to/cadical
```

That checkout is used as it is, and configured and built in place if it has no
`build/libcadical.a` yet. `IPASIR_INC` and `IPASIR_LIB` override the include
directory and the library path separately, for a layout that is not CaDiCaL's
own.

Other targets: `make debug` builds `cubical-debug` with ASan and UBSan (under
its own name, so a sanitiser build cannot be left behind and measured as if it
were the real one), `make clean` removes cubical's build products, and `make
distclean` also removes `third_party/`.

### Requirements

Linux. cubical uses `fallocate(FALLOC_FL_PUNCH_HOLE)` to release the part of
the proof trace it has already consumed, and `/dev/shm` to keep that trace in
RAM. Both are Linux-specific. See [the proof trace](#the-proof-trace) for what
to do when `/dev/shm` is unavailable or too small.

## Run

```sh
./cubical formula.cnf                 # defaults
./cubical --opt lucky=0 formula.cnf   # passes lucky=0 to CaDiCaL as an option (should be much faster on many cubes)
./cubical --cores 8 formula.cnf       # eight workers
./cubical --percentile 75 formula.cnf # a stricter phase-2 bar
./cubical -t -inf formula.cnf         # score on the weaker polarity only
./cubical --trace formula.cnf         # what would it split on, and when?
cat formula.cnf | ./cubical           # stdin works too
```

Exit status is **10** for `SATISFIABLE`, **20** for `UNSATISFIABLE`, and **0**
if the search did not finish (interrupted, or a worker died). `./cubical
--help` lists every option with its full description; this README covers the
model behind them and how to read the output.

## How it decides to split

Every clause in the collected proof carries weight 1, shared evenly over its
literals, so an occurrence in a clause of *k* literals is worth 1/*k*. For a
variable *v*:

```
score(v) = the weights of the occurrences of v and -v, combined
cover(v) = score(v) / N      the share of the collected proof's weight
                             that restricting on v removes
```

The covers of all variables at one node sum to exactly 1. That is what makes
two variables at a node comparable — and also why the default phase-2 bar is a
percentile of the path's own scores rather than a constant: the mean cover is
mechanically `1 / (variables touched)`, which spans two orders of magnitude
across a benchmark, so a constant bar asks a different question on every
instance. `--cover` offers the constant anyway, because the percentile buys
that scale invariance at the price of a blind spot at depth 1; the two are
alternatives to be measured against each other, not a right and a wrong answer.

The counts come from the DRAT stream and not from `ipasir_set_learn`, because
the proof also carries what CaDiCaL's pre- and inprocessing derive, and the two
streams disagree sharply.

**`-t` — how much imbalance costs.** The plain cover ignores *which* polarity
carries the weight, and a variable whose occurrences all have one sign removes
nothing from the other branch. `-t` combines the two polarity weights by their
power mean of order *t* instead of adding them:

| `-t` | score | behaviour |
| --- | --- | --- |
| `1` | arithmetic mean | the plain cover; imbalance is free |
| `0` | geometric mean | **default** |
| `-inf` | minimum | the weight removed from the *weaker* branch |

Any *t* in `[-inf, inf]` is accepted. Below 1 the score is the cover times a
penalty for one-sided weight, steeper the lower *t* goes. Past about `-8` the
result is within a few percent of `-inf`. Above 1 imbalance is *rewarded*,
which exists as a control and not as an expectation. Every *t* is normalised
onto the same scale, so the percentile reads the same way whatever *t* is.

### Phase 1: the ramp

Every node shallower than the ramp depth runs for `--ramp-conflicts` conflicts
and then splits on its best-scoring variable, **whatever that variable
scores**. No threshold applies.

The ramp depth is `ceil(log2(--cores))`, so 32 cores ramp to depth 5 and one
core does not ramp at all. `--ramp-depth` overrides it; `--ramp-depth 0` turns
the phase off.

Two things come out of the phase:

- **Occupancy.** The top of the tree is a complete binary tree of depth *d*,
  hence 2^*d* subproblems, so the workers fill by construction rather than
  after however long a threshold takes to trip. Every split hands a cube to
  the shared queue and an idle worker takes it.
- **A sample.** *d* scores measured on this instance at the same budget at
  every node. That is what phase 2's threshold is a percentile of, which is
  how the bar ends up instance-specific with nothing supplied from outside.

A ramp node still carries its parent's reduced proof in, so its conflicts are
spent on top of the whole path's evidence rather than instead of it. What the
budget buys is a view of each subproblem taken at the same cost, which is what
makes the *d* scores comparable to one another.

Note that `--min-split` can delay a ramp split past its budget: a node holding
less than that much proof has too little to read an argmax off, and the root
starts with none at all, so the root typically splits when it reaches
`--min-split` clauses rather than at `--ramp-conflicts`.

### Phase 2: the bar

At or below the ramp depth a node splits only once its best variable's score
beats the `--percentile`-th percentile of the scores its **ancestors** split
on. 50, the default, is the median.

```
bar(node) = percentile_p( score at which each ancestor split )
```

The sample starts as the ramp's measurements and grows by one at every level
below it. So the bar rises as a path accumulates good ancestors, which is what
bounds the depth of the tree — and a percentile moves far less on one
unusually good ancestor than a maximum or a mean would, so a single outlier
cannot stop a branch for good.

A node with no ancestor scores — the root, when there is no ramp — has a bar of
0 and splits at the first poll that clears `--min-split`.

Each node's bar is in the `bar%` column of the log and the sample size behind
it is in `nanc`, so a tree can be re-derived from its own log.

#### `--cover`, the absolute alternative

`--cover <pct>` replaces the percentile with a constant: split when the best
score beats `pct`, with no reference to the path above. It is in the same units
as the log's `cover%` and `bar%` columns, so `--cover 2` is the bar a row shows
as `2.000`, and it is a bar on the *score* — cover times the `-t` balance
factor — so it means raw proof coverage only at `-t 1`.

The two are refused together rather than silently ordered, since whichever lost
would sit in the command line doing nothing and a sweep would get a column of
identical numbers with no hint why.

They ask genuinely different questions, and each has a structural weakness the
other does not:

| | `--percentile` | `--cover` |
| --- | --- | --- |
| bar at the root | 0 — always splits | the same bar as everywhere |
| bar at depth 1 | **the parent's score exactly**, at any `p` | the same bar as everywhere |
| scales with instance size | yes, it is the path's own numbers | no |
| depends on depth | yes, rises as a path accumulates ancestors | no |

The percentile's depth-1 case is the one worth knowing: its sample is the path's
own ancestors, so at `nanc = 1` the sample is a single number and the bar *is*
the parent's score whatever `p` says. Every root split is therefore followed by
a child that has to beat its parent exactly, which is where the three-node trees
come from. An absolute bar has no degenerate case and no depth dependence; what
it gives up is the scale invariance below. Which trade wins is a question for a
sweep.

### Cadence, and inheritance

**Every node polls once the instant it starts**, on the proof it has just
inherited. That poll is what the `var0`/`cov0`/`conf0` columns report — the
argmax the node inherits, before it has derived a conflict of its own — and in
phase 2 it is also the first poll that may split, so a node holding enough
inherited proof splits without spending a conflict on it. After it, a ramp node
jumps straight to its budget and a phase-2 node re-checks every `--poll-every`
conflicts until it splits or closes.

**A child inherits its parent's proof** rather than starting at zero, so a
split is decided on the whole path's evidence. CaDiCaL propagates the cube, the
clauses it satisfies drop out, the ones it trims are re-weighted, and what
survives seeds the child. `--carry-mb` bounds what one node may hold.

**`--max-depth` stops splitting outright.** A node at the cap never fires, so
it solves to a verdict like any leaf rather than leaving the subtree
unfinished. It is a safety valve on the tree's size, not a strategy.

### Watching the criterion without acting on it

`--trace` prints one line per poll and never splits, which is how the covers on
an instance get looked at directly.

```
$ ./cubical --trace formula.cnf
c trace output
N          cbest      c2nd       best       avg lits/clause      touched    above      n90        n50
2008       0.068798   0.035251   89         9.96                 87         55         1          2
7456       0.041203   0.034212   2          11.78                90         65         1          5
```

`N` is the clauses the covers were read off, `cbest` and `c2nd` the best and
runner-up, `best` the winning variable, and `n90`/`n50` how many variables sit
within 90% and 50% of the best — a wide `n90` means the argmax is not telling
you much.

## Reading the output

Everything on stdout is a DIMACS comment (`c …`) except the final `s` line, so
the output is safe to pipe anywhere that expects solver output. The banner
echoes every setting that affects the search — version, `-t`, the percentile,
both phases, the cadence, the proof directory — so a log identifies the run
that produced it. Then one line per node:

```
c wrk    node  parent depth ph event   conflicts  clauses    len    fresh   node-s   total-s    var   var0  cover%    cov0      conf0    bar%  nanc    s+%    s-%   bal    trail evict   core  cube: lit(share%)
c   0       8      -1     0  1 SPLIT        2002     2009  13.98     2009     0.02      0.04    164    164   2.072   2.072       2002   0.000     0  79.24  89.30 0.556        0     .      . 
c   0      16       8     1  1 SPLIT        2001     3596  12.50     2004     0.02      0.06     20    108   3.101   2.090          0   0.000     1  88.26  72.30 0.443        1     .      .   164( 5.20) 
c   6      14      -1     1  1 SPLIT        2003     3797  13.81     2003     0.02      0.06     14     14   1.901   1.993          0   0.000     1  89.73  81.01 0.514        1     .      .  -164( 4.08) 
c   0      24      16     2  1 SPLIT        2002     5291  11.74     2117     0.03      0.09    108    108   3.018   2.410          0   0.000     2  71.29  89.53 0.369        2     .      .   164( 5.64)    20( 5.72) 
```

| column | meaning |
| --- | --- |
| `wrk` | worker index, or `-` when sequential |
| `node`, `parent`, `depth` | position in the tree. A donated cube's parent ran on another worker and reads `-1` |
| `ph` | `1` the ramp (always splits, so `bar%` is 0) or `2` the percentile |
| `event` | `SPLIT`, `UNSAT`, `SAT`, or `STOP` when a limit ended the node |
| `conflicts` | conflicts this node spent |
| `clauses` | the proof set the score was read off |
| `fresh` | the part of it this node derived itself, so `clauses - fresh` is what it inherited — and `fresh` is the denominator of the shares |
| `node-s`, `total-s` | seconds in this node, and since the run started |
| `len` | mean literals per clause in that set. A split removes ONE literal from a clause, so on a long-clause set it decomposes nothing propagation can use |
| `var`, `var0` | the variable split on, and the argmax on the proof this node **inherited** — adjacent so a disagreement is visible at a glance |
| `cover%`, `cov0` | their two scores |
| `conf0` | conflicts at the first poll, where `var0`/`cov0` were read, so "before it derived anything" can be checked rather than assumed |
| `bar%` | the score this node had to beat. `0.000` for every phase-1 node, and for the root under `--percentile`; constant everywhere under `--cover` |
| `nanc` | ancestor scores the bar was taken over — the sample behind it, which at 1 or 2 is a coin the log should not hide. Not used by `--cover` |
| `s+%`, `s-%` | the two children's surviving proof. `max` of them is the WORST branch, which is the critical path the split is bought with; their ratio is the realized balance |
| `bal` | `var`'s polarity balance in the counts, which is what `-t` scores — held against `s+`/`s-` it says whether that proxy was right here |
| `trail` | literals this node's cube implied beyond itself. Thousands implied with nothing removed from the proof is the signature of a candidate set that is one decision in disguise |
| `evict` | `EVICT` when `--carry-mb` made the set a window, so the shares read low; `.` otherwise |
| `core` | on a refuted leaf, `needed/decided` — of the cube literals this node actually decided, how many the refutation used; `.` where there is no refutation |
| `cube:` | one column per cube literal, as `lit(share%)` |

`var0` against `var` is the measurement the ramp pays for: in phase 1 they are
`--ramp-conflicts` apart, so comparing the two columns says how often a
budget's worth of fresh proof changes the choice the parent's proof alone would
have made. In phase 2
most nodes split at their first poll and the two agree trivially — a row there
with `conf0` of 0 and `fresh` of 0 is a node that split off its inherited proof
without spending a conflict.

A `bar%` above `cover%` on a non-`SPLIT` row is the percentile having stopped
that node: it polled, came up short, and ran to a verdict instead.

The cube columns line up across nodes, so a literal's share can be read down the
page; one the refutation barely mentions did not earn its split. A literal
marked `=` is the second branch of its split — its sibling's subtree was already
refuted, so the formula and the literals above it entail it and this node
assumed nothing there. On a terminal the core literals are green and the rest
red; in `--cube-log` they are marked `*` and `.`.

The 22 fields up to and including `core` are at fixed positions on every node
row — `evict` and `core` print `.` rather than blank for exactly that reason, so
`awk '{print $22}'` reads the same column whether or not the node was refuted.
Only the `cube:` columns vary in width, and a literal there is two
whitespace-separated fields (`293( 3.64)`), so split on `(` if you need them.

A `STATUS` line on **stderr** is the node in progress, in the same columns.
Use `--cube-log <file>` to write the whole log to a file and `-q` to keep stdout
empty, or `NO_COLOR=1` to drop the colouring.

### The summary

```
c nodes            807   (403 splits, 404 leaves)
c max depth         29
c conflicts     497059   (hardest leaf: 1967 conf at node 617)
c time            3.56s  (2.10s splitting, 1.29s in leaves)
c crit path       0.16s  (0.14s deciding the splits above node 762, 0.02s in it)
c core            2.33   of 2.76 decided cube literals needed per refuted leaf (0.43 dead)
c learned          403   core clauses added to the formula (2.33 literals each)
```

`crit path` is the headline number for a sequential run: it is the makespan with
unlimited workers, so it is the speedup the tree makes available. `core` is the
one number that judges the *splitting* rather than the solving — the gap between
decided literals and needed ones is levels the tree paid for and the proof then
ignored. With `--cores` you also get `busy` (cores used on average) and a line
per worker, because an average hides a straggler and a straggler is what caps a
run like this.

## Parallel search

`--cores n` forks *n* worker processes before anything is solved. One takes the
root and the rest wait; each then runs the whole subtree beneath whatever cube
it holds, and hands over its shallowest cube when another worker has none.

The ramp depth is derived from *n* for exactly this reason: phase 1 produces
2^`ramp-depth` cubes unconditionally, so the pool fills from the queue rather
than waiting on a threshold. A donated cube carries its ancestor scores with
it, so a worker that picks one up applies the same phase-2 bar the donor's
subtree would have. It carries the donor's reduced proof too when that fits in
the slot; past it the taker starts from no inherited proof and so has to derive
`--min-split` clauses of its own before it may split, which shows up in the log
as a node whose `fresh` equals its `clauses`.

Forking rather than threading is deliberate: a worker inherits the parsed
formula and every clause learned so far copy-on-write, and keeps incremental
learning along its own branch. The engine is also single-threaded with
file-scope state and CaDiCaL is not reentrant across one instance, so forking
sidesteps that whole class of problem.

With `--share 1` (the default) workers publish each refutation core through
shared memory and pick up the others'. The clause shared is the one
`--learn-cores` adds locally — the negation of the assumptions a refutation used
— which the formula entails, so it is sound in any worker. Without it each
worker rediscovers what its siblings have already refuted.

**A parallel run is not reproducible**, because which worker picks up which cube
depends on how they interleave. A sequential run is: for a fixed `--seed` and
fixed options, `--cores 1` gives the same tree every time. Reach for `--cores 1`
when comparing settings.

## The proof trace

CaDiCaL writes text DRAT to a file that cubical reads back through a second
descriptor, punching holes behind what it has consumed, so what is resident
stays small however long the proof gets. The file is unlinked as soon as both
ends are open, so nothing is left behind even on a crash, and each forked worker
reopens its own — a shared trace would interleave.

That file wants to be RAM, which is why `/dev/shm` is the default. Two things
can go wrong with it:

- **It is missing or not writable.** cubical falls back to `$TMPDIR`, then
  `/tmp`, and refuses to start with one clear line if even that fails.
- **It is too small.** A container typically caps `/dev/shm` at 64 MB, which a
  burst between two drains can overrun.

Point `--proof-dir <dir>` (or `$CUBICAL_PROOF_DIR`) at somewhere with room.
The banner says which directory a run used. If the filesystem you choose cannot
punch holes, cubical says so once: the trace will then grow with the whole
run's proof, which on a long run is tens of gigabytes.

## Defaults

| option | default | notes |
| --- | --- | --- |
| `--ramp-conflicts` | `100000` | phase 1 budget per node |
| `--ramp-depth` | auto | `ceil(log2(--cores))`; `0` turns the ramp off |
| `--percentile` | `50` | the median of the ancestors' scores |
| `--cover` | off | absolute bar instead, in `cover%` units; excludes `--percentile` |
| `-t` | `0` | geometric mean |
| `--poll-every` | `10000` | conflicts between phase-2 checks |
| `--min-split` | `100000` | clauses of proof a split needs behind it |
| `--max-depth` | `1000` | a safety valve; it should never bind |
| `--learn-cores` | on | `--no-learn-cores` turns it off |
| `--carry-mb` | `2048` | per node, and per worker under `--cores` |
| `--cores` | `1` | sequential, and reproducible |
| `--share` | `1` | with `--cores` |
| `--seed` | `0` | forwarded to CaDiCaL |

A few of the choices are worth knowing about because the obvious alternative is
wrong:

- **The percentile is the default, and an absolute bar is the option.** Covers
  at a node sum to 1, so the mean cover is `1 / (variables touched)` and a
  constant bar asks a different question on a 300-variable formula than on a
  30000-variable one — which is why `--percentile` is the default rather than
  `--cover`. Normalising by a statistic of the candidates does not fix that
  either: dividing by their mean multiplies by the variable count, which
  measures how wide the instance is, not how well it partitions. But the
  percentile pays for its scale invariance with a blind spot at depth 1 (see
  above), so `--cover` is kept as the alternative to measure against rather
  than ruled out on the argument alone.
- **The ramp depth follows the core count and nothing else.** Its job is to put
  a cube on every worker; sizing it to anything else gives up either occupancy
  or the sample phase 2 calibrates from.
- **The polling cadence is constant, not CaDiCaL's.** An earlier version copied
  CaDiCaL's inprocessing schedule, which on every formula put the first check a
  few thousand clauses in. A score read off that little proof is noise. Hence
  `--min-split` as a floor in clauses and a flat `--poll-every` — later checks
  are cheap, since the counts are maintained incrementally.
- **`--carry-mb` is not a knob to turn down.** A ceiling that fires in normal
  use is not a safety valve; it silently changes the search. It bounds what a
  node may *allocate*, and the realloc that reaches it needs both buffers, so
  the transient peak is about 1.7×.
- **`--min-split` and `--carry-mb` interact.** Eviction may not drop a set below
  `--min-split`, so a ceiling too small to hold that many clauses would make
  every check refuse for good. cubical rejects that combination at startup
  rather than running it.

## Layout

| file | |
| --- | --- |
| `cubical.c` | the whole engine: proof counting, scoring, the tree, the worker pool |
| `cshim.cpp` | the one thing IPASIR does not expose — CaDiCaL's own unit propagation, via `Solver::propagate()` and `Solver::implied()`, so cube propagation is as strong as the solver's rather than a private propagator over the original CNF |
| `Makefile` | the build, including the CaDiCaL bootstrap |

`cubical.c` is written to be read: the reasoning behind each decision is in a
comment next to it, starting with the long header comment at the top of the
file.
