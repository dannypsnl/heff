// boc's side, for the C backend: behaviour-oriented concurrency as the
// runtime's own effect.  It runs heff on threads of the system truly at
// once, so it says so:
#define HEFF_THREADS 1
// A cown is a foreign value: a turnstile (the last request queued at
// it), the value it holds, and the behaviours waiting for it to be
// written (`once`), each read and written by the one behaviour holding
// it, once it is first at the turnstile.  A behaviour is queued and run
// as the paper has it (Cheeseman et al., OOPSLA 2023, as Verona keeps
// it): a request at each of its cowns, in the order of their addresses,
// queued by swapping each in as the last, the one before it -- once
// that one's behaviour is done queueing at all of its own -- told it is
// next.  It runs once it is first at every one: a count of the cowns it
// still waits at, and one more until its queueing is done.  Done, it
// lets the next through at each, or, where none is behind it, takes its
// request out as the last by a compare-and-swap -- or, one coming
// meanwhile, waits for it to say so.  No mutex but the pool's, around
// the behaviours ready to run, which its threads take in turn, sleeping
// on its condition while there are none.  A behaviour readied by one a
// thread of the pool runs is kept in that thread's slot, the next it
// runs, where the slot is empty: none woken, the mutex not taken -- a
// chain of behaviours each readying the next runs on one thread.  One
// that has run 64 (`BC_BATCH`) from its slot in a row puts the next
// behind the others ready, where any are.  A body is never stopped
// partway, so the one kept would wait for the end of the body running:
// the thread counts the body's operations of this effect, and at the
// 256th (`BC_FUEL`) puts the one kept with the others ready, waking a
// thread to take it.
//
// The body is a computation of the program's, `Turn -> m Unit`, `m` the
// monad of the handler in force at the `when`, which wrapped it there
// (`hmap`): given its turn, it takes what the cowns hold (`Taken`), runs
// what the program gave `when` on it, and gives what that comes to
// (`Given`) -- each an operation the program does at once where its
// world is known (heff.compile.direct: `heff_bocTaken`,
// `heff_bocGiven`), a slot of this thread's (`bc_taken`, `bc_given`)
// read or written; the turn, nothing here.  The cowns, as the program
// gave them -- a cown, or a tuple (`MkPair`) of cowns and tuples -- say
// the tuple: the runner reads each cown, builds the tuple of what they
// hold as theirs is built, runs the body, and, the body done, takes
// what it gave apart the same way, writing back each cown its bit of
// the behaviour's `ws` says.  No operation of the program's for any of
// it, and nothing built at run time between the body and the runtime.
// A condition (`once`) is checked of the tuple first: where it does
// not hold, the behaviour lets go of its cowns, untouched, and waits,
// parked on those its `rs` says, until a body writes one; then it is
// queued again, behind that one, on all of them.  One still waiting
// once every other behaviour of its pool is done is dropped, its body
// never run.
//
// What a cown holds is the cown's: read by the behaviour holding it as
// a thread's own, not shared, marked `OWNED` (`heff_own_at`) once a body
// has written it, where the body's log (`HeffOwnLog`, the behaviour's
// while it runs) keeps what the body counted up of it.  The write back
// is kept by the log too, and done once the body is: a body that fails,
// or does not write a cown, leaves it as it was.  An array a cown holds,
// held by the log and by the body alone, the body writes in place
// (`heff_own_set`), the log keeping what was there, put back where the
// cown is to hold what it held.  A value of a word read and written
// keeps nothing in the log.
//
// A body that fails leaves its cowns as they were, and why is said on
// stderr, on the thread, before the cowns are let go; the program ends
// by 1 (`bc_failures`).
//
// The program has one pool (`bc_program`), opened by its first operation
// of boc's outside every worker, and drained once the program's
// computation has returned (`heff_returned`).  Which pool a `when`
// spawns in is this thread's (`bc_current`): the program's, or the pool
// whose worker this is.  So no operation carries a pool.
// Each body starts its chain of calls last from naught (`heff_dep`), as
// a bounce's step does, not one past the last body's.

#include <stdatomic.h>
#include <sched.h>
#ifndef _WIN32
#include <unistd.h>
#endif

static char *bc_strdup(const char *s) {
  char *c = heff_alloc(strlen(s) + 1);
  strcpy(c, s);
  return c;
}

static int64_t bc_cores(void) {
#if defined(_WIN32)
  SYSTEM_INFO si;
  GetSystemInfo(&si);
  return si.dwNumberOfProcessors > 0 ? (int64_t)si.dwNumberOfProcessors : 1;
#elif defined(_SC_NPROCESSORS_ONLN)
  long c = sysconf(_SC_NPROCESSORS_ONLN);
  return c > 0 ? (int64_t)c : 1;
#else
  return 1;
#endif
}

static void bc_relax(void) {
#if defined(__aarch64__)
  __asm__ __volatile__("yield");
#elif defined(__x86_64__) || defined(__i386__)
  __asm__ __volatile__("pause");
#endif
}

// (`f a0 a1`, asked for here, a failure caught: as `heff_try`, two
// arguments given at once, so a body of two parameters -- its turn and
// what comes after it -- is called, not made a partial application)
static const char *bc_try2(V f, V a0, V a1, V *out) {
  jmp_buf here;
  jmp_buf *volatile up = heff_catch;
  volatile long dep = heff_dep;
  volatile size_t open = heff_nopen;
  heff_catch = &here;
  if (HEFF_SETJMP(here) == 0) {
    V a[2] = { a0, a1 };
    *out = heff_tr(heff_apply(f, 2, a));
    heff_catch = up;
    return NULL;
  }
  heff_catch = up;
  heff_dep = dep;
  heff_reopen(open);
  return heff_caught;
}

// (what an operation's `Some` holds, where `bc_open` puts it)
static HEFF_TLS V bc_held;

static V bc_open_fn(V self, V *a) {
  (void)self;
  bc_held = a[0];
  return NTAG(TAG_MkUnit);
}

static Clo bc_open_clo = {{0x80000000u, K_CLO, 0}, bc_open_fn, 1, 0};

// (what `s` holds, its types erased; `s` consumed)
static V bc_open(V s) {
  heff_drop(heff_answer(s, (V)&bc_open_clo));
  return bc_held;
}

// Cowns and behaviours ------------------------------------------------------

#define BC_POLLERS 1024

typedef struct BcBehaviour BcBehaviour;
typedef struct BcCown BcCown;
typedef struct BcPool BcPool;
typedef struct BcWait BcWait;
typedef struct BcPark BcPark;
typedef struct BcAct BcAct;

typedef struct {
  _Atomic(BcBehaviour *) next;
  atomic_bool queued;
  BcCown *t;
} BcRequest;

// (a behaviour parked on cowns, to be queued again by the first body to
// write one of them -- 1 while it waits, 2 while one queues it, 0 once
// it is queued, or dropped -- held by each cown's list it is in, and by
// its pool's list while it waits)
struct BcWait {
  atomic_int state;
  atomic_int refs;
  BcBehaviour *b;
  BcWait *prev, *next;
};

// (a cown's list of those waiting on it, the last parked first)
struct BcPark {
  BcWait *w;
  BcPark *next;
};

struct BcCown {
  _Atomic(BcRequest *) last;
  V v;               // the holder's
  BcPark *waiting;   // the holder's
};

struct BcBehaviour {
  atomic_int waits;
  BcPool *pool;
  V cs;      // the cowns, a cown or a tuple of them
  V body;    // Turn -> m Unit
  V cond;    // Nothing, or Just (t -> Bool)
  int64_t ws, rs;
  BcBehaviour *after;
  BcAct *act;  // an act awaited outside every worker: run by one
  int n;
  int moved;
  BcRequest *req;  // `few`, where the cowns are as few
  BcRequest few[2];
};

struct BcPool {
  pthread_mutex_t mu;
  pthread_cond_t work, idle;
  BcBehaviour *front, *back;
  atomic_llong live;
  int sleeping, stopping, n;
  // (the threads started, at most `n`, and those that look for a
  // behaviour not sleeping -- spinning before they sleep, or just
  // started -- which take one put with those ready without a wake)
  int started, ready;  // `ready`: how many are put with those ready, under `mu`
  atomic_int looking;
  pthread_t *threads;
  BcWait *parked;  // those waiting, under `mu`
  // (the reactor groups of the workers waiting in their reactors, acts
  // pending there, to be woken there where a behaviour is ready)
  int npolling;
  int64_t polling[BC_POLLERS];
};

static void bc_wait_less(BcWait *w) {
  if (atomic_fetch_sub_explicit(&w->refs, 1, memory_order_acq_rel) == 1) free(w);
}

// (a cown holding `v`, shared; `v` consumed)
// (a cown on a cache line of its own: each spawn on it swaps `last`, and
// a line two cowns shared would be written by the spawns on both)
#define BC_LINE 128
static BcCown *bc_cown(V v) {
  BcCown *c = aligned_alloc(BC_LINE, BC_LINE);
  if (!c) heff_fail("out of memory");
  atomic_init(&c->last, NULL);
  c->v = heff_share(v);
  c->waiting = NULL;
  return c;
}

// (the program's last reference to the cown gone: no behaviour holds it,
// since each holds a reference)
static void bc_cown_let_go(void *x) {
  BcCown *c = x;
  for (BcPark *p = c->waiting, *next; p; p = next) {
    next = p->next;
    bc_wait_less(p->w);
    free(p);
  }
  heff_drop(c->v);
  free(c);
}

static int bc_is_cown(V v) {
  return IS_OBJ(v) && v && OBJ(v)->kind == K_FGN && ((Fgn *)v)->let_go == bc_cown_let_go;
}

#define BC_COWN(v) ((BcCown *)((Fgn *)(v))->p)

// (none: a behaviour on no cown, `()`, boc's own -- what an act's
// `with` of no cown spawns)
#define BC_NONE(cs) ((cs) == NTAG(TAG_MkUnit))

// (how many cowns `cs` is, a cown or a tuple of them)
static int bc_count(V cs) {
  if (bc_is_cown(cs)) return 1;
  if (BC_NONE(cs)) return 0;
  if (heff_tag_of(cs) != TAG_MkPair) heff_fail("boc: a behaviour on what is not a cown, nor a tuple of them");
  return bc_count(heff_field(cs, 0)) + bc_count(heff_field(cs, 1));
}

// (... each, in the order of the tuple, from `*i`)
static void bc_each(V cs, BcRequest *req, int *i) {
  if (bc_is_cown(cs)) {
    req[(*i)++].t = BC_COWN(cs);
    return;
  }
  if (BC_NONE(cs)) return;
  bc_each(heff_field(cs, 0), req, i);
  bc_each(heff_field(cs, 1), req, i);
}

// (whether the `i`th cown's bit is set: all of them where the bits are
// -1)
static inline int bc_bit(int64_t bits, int i) {
  return bits < 0 ? 1 : i < 62 && ((bits >> i) & 1);
}

// The pool counts what is queued, running or pending (`live`) a batch
// at a time, not one at a time, each a write all threads make to one
// line: a thread takes `BC_CREDIT` at once and spends them as it
// spawns, and what is done on it -- a behaviour, an act -- is its
// credit again, given back a batch at a time where it has too many.
// So `live` is what is queued, running or pending and the credit the
// threads hold; a thread gives back all it holds before it waits --
// to sleep, in its reactor -- and the program's before the end, so
// that `live` comes to 0 once nothing is left.
#define BC_CREDIT 64
static HEFF_TLS int64_t bc_credit;

// (one more queued, running or pending)
static inline void bc_pool_more(BcPool *pl) {
  if (bc_credit > 0) {
    bc_credit--;
    return;
  }
  atomic_fetch_add_explicit(&pl->live, BC_CREDIT, memory_order_acq_rel);
  bc_credit = BC_CREDIT - 1;
}

// (what this thread holds given back, before it waits: where nothing is
// left then, the end told)
static void bc_settle(BcPool *pl) {
  int64_t c = bc_credit;
  bc_credit = 0;
  if (c && atomic_fetch_sub_explicit(&pl->live, c, memory_order_acq_rel) == c) {
    pthread_mutex_lock(&pl->mu);
    pthread_cond_broadcast(&pl->idle);
    pthread_mutex_unlock(&pl->mu);
  }
}

// (one done: this thread's credit; a batch given back where it holds
// two, never all it holds, so `live` stays above 0 here)
static void bc_pool_less(BcPool *pl) {
  if (++bc_credit > 2 * BC_CREDIT) {
    atomic_fetch_sub_explicit(&pl->live, BC_CREDIT, memory_order_acq_rel);
    bc_credit -= BC_CREDIT;
  }
}

#define BC_BATCH 64
#define BC_FUEL 256
#define BC_SPINS 4000

// (the pool whose worker this thread is, if one; its slot; the fuel of
// the body it runs; and the pool a `when` here spawns in)
static HEFF_TLS BcPool *bc_running;
static HEFF_TLS BcBehaviour *bc_slot;
static HEFF_TLS int bc_fuel, bc_in_body;
static HEFF_TLS BcPool *bc_current;

// (what the behaviour runs and holds made another thread's to take: by
// the thread whose it is, once)
static void bc_movable(BcBehaviour *b) {
  if (b->moved) return;
  b->body = heff_move(b->body);
  b->cond = heff_move(b->cond);
  b->cs = heff_share(b->cs);
  b->moved = 1;
}

static void bc_thread_more(BcPool *pl);

// (the behaviour put behind those ready, a sleeping thread woken; where
// none sleeps or waits in its reactor, more are ready than threads look
// for one, and fewer than the machine's cores are started, one more
// started for it)
static void bc_queued(BcBehaviour *b) {
  BcPool *pl = b->pool;
  bc_movable(b);
  b->after = NULL;
  pthread_mutex_lock(&pl->mu);
  if (pl->back) pl->back->after = b;
  else __atomic_store_n(&pl->front, b, __ATOMIC_RELAXED);
  pl->back = b;
  pl->ready++;
  int64_t wake = 0;
  if (pl->sleeping > 0) pthread_cond_signal(&pl->work);
  else if (pl->npolling > 0) wake = pl->polling[--pl->npolling];
  else if (pl->started < pl->n && pl->ready > atomic_load_explicit(&pl->looking, memory_order_acquire))
    bc_thread_more(pl);
  pthread_mutex_unlock(&pl->mu);
  if (wake) heff_reactor_wake_group(wake);
}

// (whether this worker is looking at its reactor: where an act's rest
// readies a behaviour into its slot, the look comes back, not waiting
// on, so that the behaviour runs now)
static HEFF_TLS int bc_polling;

// (the behaviour ready: in this thread's slot, where it runs the pool's
// behaviours and the slot is empty, else queued)
static void bc_ready(BcBehaviour *b) {
  if (bc_running == b->pool && !bc_slot) {
    bc_slot = b;
#ifndef _WIN32
    if (bc_polling) heff_woken = 1;
#endif
  } else bc_queued(b);
}

static void bc_through(BcBehaviour *b) {
  if (atomic_fetch_sub_explicit(&b->waits, 1, memory_order_acq_rel) == 1) bc_ready(b);
}

// (a behaviour's room: one this thread let go of, kept for the next, a
// few hundred at most -- a chain of behaviours on one thread mallocs
// none -- else the system's)
#define BC_KEPT 256
static HEFF_TLS BcBehaviour *bc_spare;
static HEFF_TLS int bc_nspare;

static BcBehaviour *bc_behaviour_room(void) {
  BcBehaviour *b = bc_spare;
  if (b) {
    bc_spare = b->after;
    bc_nspare--;
    return b;
  }
  return heff_alloc(sizeof(BcBehaviour));
}

static void bc_behaviour_free(BcBehaviour *b) {
  if (b->req != b->few) free(b->req);
  if (bc_nspare >= BC_KEPT) {
    free(b);
    return;
  }
  b->after = bc_spare;
  bc_spare = b;
  bc_nspare++;
}

// (... and what it holds let go of, where it still holds it)
static void bc_behaviour_drop(BcBehaviour *b) {
  if (b->cs) heff_drop(b->cs);
  if (b->body) heff_drop(b->body);
  if (b->cond) heff_drop(b->cond);
  bc_behaviour_free(b);
}

static int bc_by_address(const void *x, const void *y) {
  uintptr_t a = (uintptr_t)((const BcRequest *)x)->t, b = (uintptr_t)((const BcRequest *)y)->t;
  return a < b ? -1 : a > b;
}

// (the behaviour queued at its cowns, which it is now first at or
// behind the last at each: counted one more of its pool's beforehand)
static void bc_enqueue(BcBehaviour *b) {
  int n = b->n;
  for (int i = 0; i < n; i++) {
    atomic_init(&b->req[i].next, NULL);
    atomic_init(&b->req[i].queued, 0);
  }
  atomic_init(&b->waits, n + 1);
  for (int i = 0; i < n; i++) {
    BcRequest *r = &b->req[i];
    BcRequest *before = atomic_exchange_explicit(&r->t->last, r, memory_order_acq_rel);
    if (!before) {
      atomic_fetch_sub_explicit(&b->waits, 1, memory_order_acq_rel);
      continue;
    }
    bc_movable(b);
    while (!atomic_load_explicit(&before->queued, memory_order_acquire)) bc_relax();
    atomic_store_explicit(&before->next, b, memory_order_release);
  }
  for (int i = 0; i < n; i++) atomic_store_explicit(&b->req[i].queued, 1, memory_order_release);
  bc_through(b);
}

static void bc_failed(BcPool *pl, const char *why);

// (where in `cs` the cown `t` is, from `*i`: the first two times, the
// first cown counted 1)
static void bc_where(V cs, BcCown *t, int *i, int at[2]) {
  if (bc_is_cown(cs)) {
    ++*i;
    if (BC_COWN(cs) == t && !at[1]) at[at[0] != 0] = *i;
    return;
  }
  if (BC_NONE(cs)) return;
  bc_where(heff_field(cs, 0), t, i, at);
  bc_where(heff_field(cs, 1), t, i, at);
}

static const char *bc_th(int n) {
  if (n % 100 / 10 == 1) return "th";
  return n % 10 == 1 ? "st" : n % 10 == 2 ? "nd" : n % 10 == 3 ? "rd" : "th";
}

// (a behaviour asked for on the cowns `cs`, `t` among them twice: a
// failure, said as a body's is, where in `cs` it is)
static void bc_twice(BcPool *pl, V cs, BcCown *t) {
  int i = 0, at[2] = {0, 0};
  bc_where(cs, t, &i, at);
  char why[160];
  snprintf(why, sizeof why,
           "boc: the same cown twice in one `with`, its %d%s and %d%s cowns: the behaviour not spawned",
           at[0], bc_th(at[0]), at[1], bc_th(at[1]));
  bc_failed(pl, why);
}

// (`body` queued on the cowns `cs`, in the pool, `cond` what it waits
// for, `ws` the cowns it writes back, `rs` those its condition reads;
// all consumed.  The same cown twice is found here, as the cowns are
// put in order: a failure, the behaviour never queued, the spawner
// going on)
static void bc_behave(BcPool *pl, V cs, V body, V cond, int64_t ws, int64_t rs) {
  int n = bc_count(cs);
  if (n > 62 && (ws >= 0 || rs > 0)) heff_fail("boc: a behaviour on more than 62 cowns, some not written");
  BcBehaviour *b = bc_behaviour_room();
  b->req = n <= 2 ? b->few : heff_alloc((size_t)n * sizeof(BcRequest));
  int i = 0;
  bc_each(cs, b->req, &i);
  if (n == 2) {
    i = 1;
    if (b->req[0].t == b->req[1].t) goto twice;
    if ((uintptr_t)b->req[0].t > (uintptr_t)b->req[1].t) {
      BcCown *t = b->req[0].t;
      b->req[0].t = b->req[1].t;
      b->req[1].t = t;
    }
  } else if (n > 2) {
    qsort(b->req, (size_t)n, sizeof(BcRequest), bc_by_address);
    for (i = 1; i < n; i++)
      if (b->req[i].t == b->req[i - 1].t) goto twice;
  }
  b->n = n;
  b->pool = pl;
  b->cs = cs;
  b->body = body;
  b->cond = cond;
  b->ws = ws;
  b->rs = rs;
  b->act = NULL;
  b->moved = 0;
  bc_pool_more(pl);
  bc_enqueue(b);
  return;
twice:
  bc_twice(pl, cs, b->req[i].t);
  bc_behaviour_free(b);
  heff_drop(cs);
  heff_drop(body);
  heff_drop(cond);
}

static void bc_behaved_all(BcBehaviour *b) {
  for (int i = 0; i < b->n; i++) {
    BcRequest *r = &b->req[i];
    BcBehaviour *next = atomic_load_explicit(&r->next, memory_order_acquire);
    if (!next) {
      BcRequest *mine = r;
      if (atomic_compare_exchange_strong_explicit(&r->t->last, &mine, NULL, memory_order_acq_rel, memory_order_acquire))
        continue;
      while (!(next = atomic_load_explicit(&r->next, memory_order_acquire))) bc_relax();
    }
    bc_through(next);
  }
}

// Waiting (`once`) ---------------------------------------------------------

// (the behaviour, its condition not holding, parked on the cowns `rs`
// says, the `i`th of the tuple `cs` from `*i`: it holds them, so their
// lists are its)
static void bc_park_on(V cs, BcWait *w, int64_t rs, int *i) {
  if (bc_is_cown(cs)) {
    if (bc_bit(rs, (*i)++)) {
      BcCown *c = BC_COWN(cs);
      BcPark *p = heff_alloc(sizeof(BcPark));
      p->w = w;
      p->next = c->waiting;
      c->waiting = p;
      atomic_fetch_add_explicit(&w->refs, 1, memory_order_relaxed);
    }
    return;
  }
  if (BC_NONE(cs)) return;
  bc_park_on(heff_field(cs, 0), w, rs, i);
  bc_park_on(heff_field(cs, 1), w, rs, i);
}

// (the behaviour, its condition not holding, as it is to be queued
// again: one of its own, what it runs and holds handed to it, so that
// the one running lets go of its cowns as it is, whenever it is queued)
static BcBehaviour *bc_again(BcBehaviour *b) {
  bc_movable(b);
  BcBehaviour *nb = bc_behaviour_room();
  nb->req = b->n <= 2 ? nb->few : heff_alloc((size_t)b->n * sizeof(BcRequest));
  for (int i = 0; i < b->n; i++) nb->req[i].t = b->req[i].t;
  nb->n = b->n;
  nb->pool = b->pool;
  nb->cs = b->cs;
  nb->body = b->body;
  nb->cond = b->cond;
  nb->ws = b->ws;
  nb->rs = b->rs;
  nb->act = NULL;
  nb->moved = 1;
  b->cs = b->body = b->cond = 0;
  return nb;
}

static void bc_park(BcBehaviour *b) {
  BcPool *pl = b->pool;
  BcWait *w = heff_alloc(sizeof(BcWait));
  atomic_init(&w->state, 1);
  atomic_init(&w->refs, 1);
  w->b = b;
  int i = 0;
  bc_park_on(b->cs, w, b->rs, &i);
  pthread_mutex_lock(&pl->mu);
  w->prev = NULL;
  w->next = pl->parked;
  if (pl->parked) pl->parked->prev = w;
  pl->parked = w;
  pthread_mutex_unlock(&pl->mu);
}

// (the pool's list without `w`, under its mutex)
static void bc_unparked(BcPool *pl, BcWait *w) {
  if (w->prev) w->prev->next = w->next;
  else pl->parked = w->next;
  if (w->next) w->next->prev = w->prev;
}

// (the behaviour parked queued again, behind the one writing a cown it
// waits on, where it still waits: counted its pool's again before it
// says it no longer waits, so that `drain` does not end meanwhile)
static void bc_wake(BcWait *w) {
  int one = 1;
  if (!atomic_compare_exchange_strong_explicit(&w->state, &one, 2, memory_order_acq_rel, memory_order_acquire))
    return;
  BcBehaviour *b = w->b;
  BcPool *pl = b->pool;
  bc_pool_more(pl);
  pthread_mutex_lock(&pl->mu);
  bc_unparked(pl, w);
  pthread_mutex_unlock(&pl->mu);
  atomic_store_explicit(&w->state, 0, memory_order_release);
  bc_wait_less(w);
  bc_enqueue(b);
}

// (those waiting on the cowns written woken, the `i`th of the tuple
// from `*i`: in the order they came to wait)
static void bc_woken(V cs, int64_t ws, int *i) {
  if (bc_is_cown(cs)) {
    BcCown *c = BC_COWN(cs);
    if (bc_bit(ws, (*i)++) && c->waiting) {
      BcPark *p = c->waiting, *order = NULL;
      c->waiting = NULL;
      while (p) {
        BcPark *next = p->next;
        p->next = order;
        order = p;
        p = next;
      }
      while (order) {
        BcPark *next = order->next;
        bc_wake(order->w);
        bc_wait_less(order->w);
        free(order);
        order = next;
      }
    }
    return;
  }
  if (BC_NONE(cs)) return;
  bc_woken(heff_field(cs, 0), ws, i);
  bc_woken(heff_field(cs, 1), ws, i);
}

// What a cown holds, owned ----------------------------------------------------

// (the log's entry for the cown, where it has one)
static HeffOwnRoot *bc_own_entry(HeffOwnLog *g, BcCown *c) {
  for (int64_t j = 0; j < g->nr; j++)
    if (g->roots[j].cell == c) return &g->roots[j];
  return NULL;
}

// (the log's entry for the cown, made where there is none: the
// behaviour holds the cown, so the entry holds nothing of it)
static HeffOwnRoot *bc_own_root(HeffOwnLog *g, BcCown *c) {
  HeffOwnRoot *had = bc_own_entry(g, c);
  if (had) return had;
  if (!g->roots) {
    g->roots = g->first;
    g->cr = sizeof g->first / sizeof g->first[0];
  } else if (g->roots == g->first && g->nr == g->cr) {
    g->roots = malloc(sizeof g->first);
    if (!g->roots) heff_fail("out of memory");
    memcpy(g->roots, g->first, sizeof g->first);
  }
  g->roots = heff_own_room(g->roots, g->nr, &g->cr, sizeof(HeffOwnRoot));
  HeffOwnRoot *e = &g->roots[g->nr++];
  e->cell = c;
  e->held = 0;
  e->v = c->v;
  e->put = 0;
  e->written = 0;
  return e;
}

// (what the cown holds, one more count of it: held by the log once
// too, where it is the cown's.  A number of a word, or a constructor
// without fields, is no object: nothing of it to keep)
static V bc_get_owned(HeffOwnLog *g, BcCown *c) {
  V now = c->v;
  if ((!IS_OBJ(now) || !now) && !bc_own_entry(g, c)) return now;
  V v = bc_own_root(g, c)->v;
  if (!IS_OBJ(v) || !v) return v;
  uint32_t rc = heff_rc(OBJ(v));
  if (heff_owned(rc)) OBJ(v)->rc = heff_own_touch(OBJ(v), rc) + 1;
  else heff_dup(v);
  return v;
}

// (... it is to hold `v` once the body is done; `v` consumed)
static void bc_set_owned(HeffOwnLog *g, BcCown *c, V v) {
  // (no object written over another: written now, nothing kept)
  if ((!IS_OBJ(v) || !v) && !bc_own_entry(g, c)) {
    V now = c->v;
    if (!IS_OBJ(now) || !now) {
      c->v = v;
      return;
    }
  }
  HeffOwnRoot *e = bc_own_root(g, c);
  if (e->written) heff_drop(e->put);
  e->put = v;
  e->written = 1;
}

// (what the body wrote of `r` put back as it was in `s` -- `r`, or a
// copy of it -- the last first, each entry done with)
static void bc_own_unwrite(HeffOwnLog *g, Arr *r, Arr *s) {
  unsigned w = heff_arr_width[HEFF_ARR_KIND(r)];
  for (int64_t j = g->ns; j-- > 0;) {
    HeffOwnSet *e = &g->sets[j];
    if (e->r != r) continue;
    if (HEFF_ARR_KIND(r) == HEFF_ARR_V) heff_drop(s->a[e->i]);
    memcpy((char *)s->a + e->i * w, &e->old, w);
    e->r = NULL;
  }
}

// (the cown holding the array as it was before the body wrote it: in
// place, where only what holds it there and the log do; else a copy,
// shared, put in the slot -- or the cown -- that held it, what else
// holds it keeping it as the body made it)
static void bc_own_restore(HeffOwnLog *g, HeffOwnArr *e) {
  Arr *r = e->r;
  if (HEFF_COUNT(heff_rc(&r->h)) == 2) {
    bc_own_unwrite(g, r, r);
    return;
  }
  Arr *s = heff_arr_alloc(r->n, HEFF_ARR_KIND(r));
  heff_arr_move(s, 0, r, 0, r->n);
  bc_own_unwrite(g, r, s);
  V c = heff_share((V)s);
  if (e->at) *e->at = c;
  else ((BcCown *)g->roots[e->root].cell)->v = c;
  heff_drop((V)r);
}

// (a behaviour's body done, or failed, and its log finished, with no
// log of its own: what it was to write let go of where it failed; each
// array it wrote in place, of what a cown not written holds, put back;
// each cown written; and what it counted up shared where more than one
// holds it)
static void bc_own_done(HeffOwnLog *g, int failed) {
  if (!g->nr && !g->nt) return;
  if (failed)
    for (int64_t j = 0; j < g->nr; j++)
      if (g->roots[j].written) {
        heff_drop(g->roots[j].put);
        g->roots[j].written = 0;
      }
  for (int64_t j = 0; j < g->na; j++)
    if (!g->roots[g->arrs[j].root].written) bc_own_restore(g, &g->arrs[j]);
  for (int64_t j = 0; j < g->ns; j++) {
    HeffOwnSet *e = &g->sets[j];
    if (e->r && HEFF_ARR_KIND(e->r) == HEFF_ARR_V) heff_own_at(&e->r->a[e->i]);
  }
  for (int64_t j = 0; j < g->nr; j++) {
    HeffOwnRoot *e = &g->roots[j];
    if (!e->written) continue;
    BcCown *c = e->cell;
    V old = c->v;
    c->v = e->put;
    heff_drop(old);
    heff_own_at(&c->v);
  }
  for (int64_t j = 0; j < g->ns; j++) {
    HeffOwnSet *e = &g->sets[j];
    if (e->r && HEFF_ARR_KIND(e->r) == HEFF_ARR_V) heff_drop((V)e->old);
  }
  for (int64_t j = 0; j < g->nt; j++) {
    V o = g->touched[j];
    uint32_t rc = heff_rc(OBJ(o));
    if (heff_owned(rc)) {
      OBJ(o)->rc = rc &= ~HEFF_TOUCHED_BIT;
      if (HEFF_COUNT(rc) > 2) heff_share(o);
    }
    heff_drop(o);
  }
  free(g->touched);
  if (g->roots != g->first) free(g->roots);
  free(g->arrs);
  free(g->sets);
}

// (what the cowns `cs` hold, a tuple as they are: each read by the log)
static V bc_contents(HeffOwnLog *g, V cs) {
  if (bc_is_cown(cs)) return bc_get_owned(g, BC_COWN(cs));
  if (BC_NONE(cs)) return cs;
  V f[2] = { bc_contents(g, heff_field(cs, 0)), bc_contents(g, heff_field(cs, 1)) };
  return heff_tag_n(TAG_MkPair, 2, f);
}

// (what the body came to, `v`, taken apart as the cowns are, the `i`th
// written back where its bit of `ws` says, from `*i`; `v` consumed)
static void bc_written(HeffOwnLog *g, V cs, V v, int64_t ws, int *i) {
  if (bc_is_cown(cs)) {
    if (bc_bit(ws, (*i)++)) bc_set_owned(g, BC_COWN(cs), v);
    else heff_drop(v);
    return;
  }
  if (BC_NONE(cs)) {
    heff_drop(v);
    return;
  }
  V l = heff_dup(heff_field(v, 0)), r = heff_dup(heff_field(v, 1));
  heff_drop(v);
  bc_written(g, heff_field(cs, 0), l, ws, i);
  bc_written(g, heff_field(cs, 1), r, ws, i);
}

// Running ---------------------------------------------------------------------

// (what the cowns of the behaviour this thread runs hold, for its body
// to take (`Taken`), and what they are to hold after it, as its body
// gives it (`Given`))
static HEFF_TLS V bc_taken, bc_given;

static V bc_dropped(V self, V *a) {
  (void)self;
  heff_drop(a[0]);
  return NTAG(TAG_MkUnit);
}

static Clo bc_dropped_clo = {{0x80000000u, K_CLO, 0}, bc_dropped, 1, 0};

// (how many behaviours and acts failed: the program ends by 1 where any
// did)
static atomic_int bc_failures;

// (a behaviour or an act failed, why: said on stderr, as a failure of
// the program's is, the others going on)
static void bc_failed(BcPool *pl, const char *why) {
  (void)pl;
  atomic_fetch_add_explicit(&bc_failures, 1, memory_order_relaxed);
  fflush(stdout);
  if (strcmp(why, "heff:abandon") == 0) fputs("heff:abandon\n", stderr);
  else fprintf(stderr, "heff: %s\n", why);
}

// Acts awaited ----------------------------------------------------------------

// An act awaited (`Awaits`) is a computation of the program's, `Turn ->
// m Unit`, run outside every behaviour: the act, then what comes once
// it has its value -- the behaviour after it spawned -- its own rest.
// Each worker of a pool has a group of the runtime's reactor
// (`bc_group`), opened as it starts its first act.  An act awaited by a
// behaviour a worker runs is given that worker (its `bc_inbox`), and
// started there once the behaviour is done, in its group: run until it
// is done, or until an operation of it would wait (a read, a sleep),
// which is then pending in the worker's reactor, the rest of the act
// kept with it.  So the act's rest -- the `when` of the behaviour after
// it -- runs on the worker that started it, and that behaviour is the
// one the worker runs next, in its slot: no other thread between an
// act and its behaviour.  An act awaited outside every worker (by a
// `main`) is a behaviour on no cown, whose worker
// takes the act as its own.
//
// A worker with nothing to run waits in its reactor where acts of its
// are pending, said to be (`polling`) so that a behaviour put with
// those ready wakes it there (`heff_reactor_wake_group`), else on the
// pool's condition; and it looks at its reactor, not waiting, after
// every 64 behaviours (`BC_POLL_EVERY`), so that acts done meanwhile
// are not passed over.  The pool counts an act given a worker and not
// yet started, and a worker with acts pending (`bc_holding`): the
// program ends once no behaviour is queued or runs and no act is
// pending.  An act that fails -- abandons, or fails in the runtime --
// fails as a body does: why is said (the group's function for
// failures), and what was to come after it does not.
//
// An act awaited with a custodian current is in that custodian's
// custody, as std.reactor's `giving` has it: started in a group of its
// own within the worker's, which a thing the custodian has among its
// things gives up as it is shut down -- what of the act is pending let
// go of, undone, and the behaviour after it never spawned.  One that
// has come to its value is not given up.  Two acts raced (`Races`) are
// each in a group of their own, given the race as their turn: the
// first to come to its value asks it (`Won`), and is told so, and the
// other's group is closed, its wait undone; the other, coming to its
// value too, is told it is not the first.  Both are on one worker, so
// the race is that worker's alone.

#define BC_POLL_EVERY 64

// (an act awaited: its computation, of the program's, given the
// custodian current at its await, as a body is; or, `race`, two of
// them; and that custodian, its foreign value, or 0)
struct BcAct {
  BcAct *next;
  V arm[2];
  int race;
  V custody;
};

// (a race's: whether one of its acts has come to its value first, and
// their groups)
typedef struct {
  int won;
  int64_t g[2];
} BcRace;

static void bc_race_let_go(void *p) { free(p); }

// (this worker's acts awaited, to be started, the first first; its
// group, 0 before its first act; and whether it counts as one of its
// pool's for acts pending in its reactor)
static HEFF_TLS BcAct *bc_inbox, *bc_inbox_last;
static HEFF_TLS int64_t bc_group;
static HEFF_TLS int bc_holding;

// (the act given this worker, counted its pool's until it is started.
// Given it by an act's rest, which runs as the worker looks at its
// reactor, the look comes back, not waiting on, so that the act starts
// now -- not once an act of the worker's is done)
static void bc_inboxed(BcPool *pl, BcAct *a) {
  bc_pool_more(pl);
  a->next = NULL;
  if (bc_inbox_last) bc_inbox_last->next = a;
  else bc_inbox = a;
  bc_inbox_last = a;
#ifndef _WIN32
  if (bc_polling) heff_woken = 1;
#endif
}

// (an act awaited where no worker of its pool is: a behaviour on no
// cown, whose worker takes it)
static void bc_act_behaviour(BcPool *pl, BcAct *a) {
  a->arm[0] = heff_move(a->arm[0]);
  if (a->race) a->arm[1] = heff_move(a->arm[1]);
  if (a->custody) a->custody = heff_move(a->custody);
  BcBehaviour *b = bc_behaviour_room();
  b->req = b->few;
  b->n = 0;
  b->pool = pl;
  b->cs = NTAG(TAG_MkUnit);
  b->body = 0;
  b->cond = 0;
  b->ws = b->rs = 0;
  b->act = a;
  b->moved = 1;
  bc_pool_more(pl);
  bc_enqueue(b);
}

// (an act awaited, `arm1` 0, or two raced: in the pool of here, given
// this worker where it is one of that pool's, else a behaviour; the
// arms consumed)
static void bc_await(BcPool *pl, V arm0, V arm1) {
  BcAct *a = heff_alloc(sizeof(BcAct));
  a->arm[0] = arm0;
  a->arm[1] = arm1;
  a->race = arm1 != 0;
  V env = heff_custody_env;
  a->custody = env && heff_tag_of(env) == TAG_Just ? heff_dup(heff_field(env, 0)) : 0;
  if (bc_running == pl) bc_inboxed(pl, a);
  else bc_act_behaviour(pl, a);
}

// (an act that failed: `failed` given why; what the group finishes
// with, nothing)
static V bc_act_failed(V self, V *a) {
  size_t len;
  char *why = heff_bytes(a[0], &len);
  heff_drop(a[0]);
  heff_drop(self);
  bc_failed(bc_running, why);
  free(why);
  return NTAG(TAG_MkUnit);
}

// (an act begun: its computation given its turn, and its end)
static V bc_act_begun(V self, V *a) {
  V *e = heff_env(self);
  V act = heff_dup(e[0]), args[2] = { heff_dup(e[1]), heff_dup(e[2]) };
  heff_drop(self);
  heff_drop(a[0]);
  return heff_tail(act, 2, args);
}

// (the end of an act in a group of its own: the group closed, given up
// no more, before what gives it up, in the closure's room, is let go
// of)
static V bc_act_ended(V self, V *a) {
  heff_reactor_close(INT_OF(heff_env(self)[0]));
  heff_drop(self);
  return a[0];
}

// (the thing `thing` in the custody of the custodian `cv`: ended at once
// where it is shut down.  Where no program's world has custodians,
// there is none)
static void bc_owned_by(V cv, V thing) {
#ifdef HEFF_CUSTODY_LOCK
  HeffCustody *c = heff_foreign_ptr(cv);
  char *ended = NULL;
  HEFF_CUSTODY_LOCK();
  V was = heff_custody_owned(c, cv, (Fgn *)thing, &ended);
  HEFF_CUSTODY_UNLOCK();
  if (ended) {
    heff_custody_failed(c, ended);
    free(ended);
  }
  if (was) heff_drop(was);
#else
  (void)cv;
  (void)thing;
#endif
}

// (whether this worker counts as one of its pool's: so while acts of it
// are pending)
static void bc_hold_update(BcPool *pl) {
  int now = bc_group && heff_reactor_pending(bc_group) > 0;
  if (now == bc_holding) return;
  bc_holding = now;
  if (now) bc_pool_more(pl);
  else bc_pool_less(pl);
}

// (the act started, in this worker's group, or one of its own within
// it: run until it is done or pending.  Of a race, both, each in one of
// its own, the second not begun where the first came to its value at
// once.  `a` let go of)
static void bc_start(BcAct *a) {
  if (!bc_group) bc_group = heff_reactor_open(heff_clo(bc_act_failed, 1, 0, NULL));
  int arms = a->race ? 2 : 1;
  BcRace *rc = NULL;
  V race = NTAG(TAG_MkUnit);
  if (a->race) {
    rc = heff_alloc(sizeof(BcRace));
    rc->won = 0;
    race = heff_foreign(rc, bc_race_let_go);
  }
  int64_t gs[2];
  V ends[2];
  for (int i = 0; i < arms; i++) {
    int64_t g = bc_group;
    if (a->race || a->custody) {
      g = heff_reactor_open_within(bc_group);
      V gv = NTAG(TAG_MkUnit);
      if (a->custody) {
        gv = heff_reactor_giving(g, NTAG(TAG_MkUnit));
        bc_owned_by(a->custody, gv);
      }
      V e[2] = { heff_int(g), gv };
      ends[i] = heff_clo(bc_act_ended, 1, 2, e);
    } else ends[i] = heff_clo(heff_kept, 1, 0, NULL);
    gs[i] = g;
    if (rc) rc->g[i] = g;
  }
  for (int i = 0; i < arms; i++) {
    if (rc && rc->won) {
      heff_drop(a->arm[i]);
      heff_drop(ends[i]);
      continue;
    }
    V e[3] = { a->arm[i], heff_dup(race), ends[i] };
    V begin = heff_clo(bc_act_begun, 1, 3, e);
    V r;
    if (!heff_group_step(gs[i], begin, NTAG(TAG_MkUnit), &r) && r != HEFF_PENDING) heff_drop(r);
  }
  heff_drop(race);
  if (a->custody) heff_drop(a->custody);
  free(a);
}

// (the acts given this worker started, in the order given, each then no
// longer counted as given)
static void bc_start_all(BcPool *pl) {
  while (bc_inbox) {
    BcAct *a = bc_inbox;
    bc_inbox = a->next;
    if (!bc_inbox) bc_inbox_last = NULL;
    bc_start(a);
    bc_hold_update(pl);
    bc_pool_less(pl);
  }
}

// (this worker's reactor looked at, waiting where `wait` until an act of
// it is done or a behaviour is ready: the rest of each act done run)
static void bc_poll(BcPool *pl, int wait) {
  bc_polling = 1;
  heff_drop(heff_reactor_finished(bc_group, wait));
  bc_polling = 0;
  bc_hold_update(pl);
}

// (the race `tn`'s act asking, its value come to, whether it is the
// first: where it is, the other's group closed, what of it is pending
// let go of)
static int bc_won(V tn) {
  BcRace *rc = heff_foreign_ptr(tn);
  if (rc->won) return 0;
  rc->won = 1;
  heff_reactor_close(rc->g[heff_group == rc->g[0] ? 1 : 0]);
  return 1;
}

// (the behaviour run, here: its condition checked of what its cowns
// hold, and where it holds, or there is none, its body run, given that,
// and what it gives back written back; then let go of -- or, its
// condition not holding, parked.  One that is an act awaited where no
// worker was: the act given this worker)
static void bc_run_behaviour(BcBehaviour *b) {
  BcPool *pl = b->pool;
  if (b->act) {
    bc_inboxed(pl, b->act);
    b->act = NULL;
    bc_behaviour_free(b);
    bc_pool_less(pl);
    return;
  }
  bc_fuel = 0;
  bc_in_body = 1;
  // (the log's lists empty, its room for the first cowns' entries not
  // cleared: none is read before it is written)
  HeffOwnLog log, *outer = heff_own_log;
  memset(&log, 0, __builtin_offsetof(HeffOwnLog, first));
  heff_own_log = &log;
  long dep = heff_dep;
  heff_dep = 0;
  V contents = bc_contents(&log, b->cs);
  const char *why = NULL;
  int holds = 1;
  V out;
  if (b->cond != NTAG(TAG_Nothing)) {
    V p = heff_dup(heff_field(b->cond, 0));
    why = heff_try(p, heff_dup(contents), &out);
    if (!why) holds = out == NTAG(TAG_True);
  }
  if (!why && holds) {
    V taken = bc_taken, given = bc_given;
    bc_taken = contents;
    bc_given = 0;
    // (the body consumed by its run, where the behaviour runs it once)
    V body = b->body;
    if (b->cond == NTAG(TAG_Nothing)) b->body = 0;
    else body = heff_dup(body);
    why = bc_try2(body, NTAG(TAG_MkUnit), (V)&bc_dropped_clo, &out);
    V result = bc_given;
    if (bc_taken) heff_drop(bc_taken);
    bc_taken = taken;
    bc_given = given;
    if (!why) {
      heff_drop(out);
      if (result) {
        int i = 0;
        bc_written(&log, b->cs, result, b->ws, &i);
      } else why = "boc: a body ended without a value";
    } else if (result) heff_drop(result);
  } else heff_drop(contents);
  heff_own_log = NULL;
  bc_own_done(&log, why != NULL || !holds);
  heff_own_log = outer;
  heff_dep = dep;
  if (why) bc_failed(pl, why);
  else if (!holds) bc_park(bc_again(b));
  else if (b->ws) {
    int i = 0;
    bc_woken(b->cs, b->ws, &i);
  }
  bc_in_body = 0;
  bc_behaved_all(b);
  bc_behaviour_drop(b);
  bc_pool_less(pl);
}

typedef struct { BcPool *pl; char *dir; } BcWorkerStart;

static void *bc_worker(void *u) {
  BcWorkerStart *s = u;
  BcPool *pl = s->pl;
  heff_dir_take(s->dir);
  free(s);
  bc_running = pl;
  bc_current = pl;
  atomic_fetch_sub_explicit(&pl->looking, 1, memory_order_acq_rel);
  int row = 0, since = 0;
  for (;;) {
    BcBehaviour *kept = bc_slot;
    if (kept) {
      bc_slot = NULL;
      if (row >= BC_BATCH && __atomic_load_n(&pl->front, __ATOMIC_RELAXED))
        bc_queued(kept);
      else {
        row = row >= BC_BATCH ? 1 : row + 1;
        bc_run_behaviour(kept);
        since++;
        continue;
      }
    }
    row = 0;
    // (the acts the behaviours run here awaited started, outside them)
    if (bc_inbox) {
      bc_start_all(pl);
      continue;
    }
    // (acts pending, looked at now and then: their rest run)
    if (bc_holding && since >= BC_POLL_EVERY) {
      since = 0;
      bc_poll(pl, 0);
      continue;
    }
    // (a while looked at before sleeping: a behaviour readied soon after
    // by another thread taken without a wake; not where acts are pending,
    // which are waited for in the reactor instead)
    if (!bc_holding) {
      atomic_fetch_add_explicit(&pl->looking, 1, memory_order_acq_rel);
      for (int i = 0; i < BC_SPINS && !__atomic_load_n(&pl->front, __ATOMIC_RELAXED)
                      && !__atomic_load_n(&pl->stopping, __ATOMIC_RELAXED); i++)
        bc_relax();
      atomic_fetch_sub_explicit(&pl->looking, 1, memory_order_acq_rel);
    }
    bc_settle(pl);
    pthread_mutex_lock(&pl->mu);
    if (!pl->front && !pl->stopping && bc_holding) {
      // (waiting in the reactor, said to be, so that a behaviour ready
      // wakes it there; where too many are, not waiting)
      int on = pl->npolling < BC_POLLERS;
      if (on) pl->polling[pl->npolling++] = bc_group;
      pthread_mutex_unlock(&pl->mu);
      since = 0;
      bc_poll(pl, on);
      if (on) {
        pthread_mutex_lock(&pl->mu);
        for (int i = 0; i < pl->npolling; i++)
          if (pl->polling[i] == bc_group) {
            pl->polling[i] = pl->polling[--pl->npolling];
            break;
          }
        pthread_mutex_unlock(&pl->mu);
      } else sched_yield();
      continue;
    }
    while (!pl->front && !pl->stopping) {
      pl->sleeping++;
      pthread_cond_wait(&pl->work, &pl->mu);
      pl->sleeping--;
    }
    BcBehaviour *b = pl->front;
    if (!b) {
      pthread_mutex_unlock(&pl->mu);
      break;
    }
    __atomic_store_n(&pl->front, b->after, __ATOMIC_RELAXED);
    if (!pl->front) pl->back = NULL;
    pl->ready--;
    pthread_mutex_unlock(&pl->mu);
    bc_run_behaviour(b);
    since++;
  }
  // (its group closed: nothing of it is pending, or the pool would not
  // have stopped)
  if (bc_group) {
    heff_reactor_close(bc_group);
    bc_group = 0;
  }
  // (the behaviours' room this thread kept given back)
  while (bc_spare) {
    BcBehaviour *next = bc_spare->after;
    free(bc_spare);
    bc_spare = next;
  }
  bc_nspare = 0;
  heff_thread_end();
  return NULL;
}

// (one more thread of the pool's started, looking until it runs: `mu`
// held, so that the end, under it, joins every one started.  Threads
// are started as behaviours are put with those ready and none is free
// to take them, up to as many as the machine has cores; a thread
// started waits, once it has nothing to run, as long as the pool is)
static void bc_thread_more(BcPool *pl) {
  BcWorkerStart *s = heff_alloc(sizeof(BcWorkerStart));
  s->pl = pl;
  s->dir = heff_dir_copy();
  atomic_fetch_add_explicit(&pl->looking, 1, memory_order_acq_rel);
  if (heff_thread_start(&pl->threads[pl->started], bc_worker, s) != 0) heff_fail("boc: cannot start a thread");
  pl->started++;
}

// (a pool of up to as many threads as the machine has cores, one
// started)
static BcPool *bc_pool(void) {
  int64_t n = bc_cores();
  BcPool *pl = heff_alloc(sizeof(BcPool));
  pthread_mutex_init(&pl->mu, NULL);
  pthread_cond_init(&pl->work, NULL);
  pthread_cond_init(&pl->idle, NULL);
  pl->front = pl->back = NULL;
  atomic_init(&pl->live, 0);
  pl->sleeping = 0;
  pl->stopping = 0;
  pl->n = (int)n;
  pl->parked = NULL;
  pl->npolling = 0;
  pl->threads = heff_alloc((size_t)n * sizeof(pthread_t));
  pl->started = 0;
  pl->ready = 0;
  atomic_init(&pl->looking, 0);
  pthread_mutex_lock(&pl->mu);
  bc_thread_more(pl);
  pthread_mutex_unlock(&pl->mu);
  return pl;
}

// (no behaviour left but those waiting: those dropped, the threads
// stopped and the pool freed.  One being queued again meanwhile is
// waited for, and then what it runs)
static void bc_drain(BcPool *pl) {
  BcWait *dropped = NULL;
  bc_settle(pl);
  pthread_mutex_lock(&pl->mu);
  for (;;) {
    while (atomic_load_explicit(&pl->live, memory_order_acquire) > 0) pthread_cond_wait(&pl->idle, &pl->mu);
    // (what is due on this thread -- the program's -- run first: a
    // custodian's `stop` given by `main`, the custodian shut down by a
    // failure since; what it spawns, or wakes, waited for in turn)
#ifdef HEFF_CUSTODY_LOCK
    if (heff_due_here && __atomic_load_n(&heff_due_here->n, __ATOMIC_ACQUIRE)) {
      pthread_mutex_unlock(&pl->mu);
      heff_due_run();
      bc_settle(pl);
      pthread_mutex_lock(&pl->mu);
      continue;
    }
#endif
    int waking = 0;
    for (BcWait *w = pl->parked, *next; w; w = next) {
      next = w->next;
      int one = 1;
      if (atomic_compare_exchange_strong_explicit(&w->state, &one, 0, memory_order_acq_rel, memory_order_acquire)) {
        bc_unparked(pl, w);
        w->next = dropped;
        dropped = w;
      } else waking = 1;
    }
    if (!waking && atomic_load_explicit(&pl->live, memory_order_acquire) == 0) break;
    pthread_mutex_unlock(&pl->mu);
    sched_yield();
    pthread_mutex_lock(&pl->mu);
  }
  __atomic_store_n(&pl->stopping, 1, __ATOMIC_RELAXED);
  pthread_cond_broadcast(&pl->work);
  int np = pl->npolling;
  int64_t woken[BC_POLLERS];
  memcpy(woken, pl->polling, (size_t)np * sizeof(int64_t));
  pl->npolling = 0;
  pthread_mutex_unlock(&pl->mu);
  for (int i = 0; i < np; i++) heff_reactor_wake_group(woken[i]);
  for (int i = 0; i < pl->started; i++) pthread_join(pl->threads[i], NULL);
  while (dropped) {
    BcWait *next = dropped->next;
    bc_behaviour_drop(dropped->b);
    bc_wait_less(dropped);
    dropped = next;
  }
  pthread_mutex_destroy(&pl->mu);
  pthread_cond_destroy(&pl->work);
  pthread_cond_destroy(&pl->idle);
  free(pl->threads);
  free(pl);
}

// (the program's pool: opened by its first operation of boc's, outside
// every worker, and its behaviours and acts waited for once the
// program's computation has returned (`heff_returned`), then those
// waiting dropped and the threads stopped)
static BcPool *bc_program;
static pthread_mutex_t bc_program_mu = PTHREAD_MUTEX_INITIALIZER;

static int bc_program_end(void) {
  pthread_mutex_lock(&bc_program_mu);
  BcPool *pl = bc_program;
  bc_program = NULL;
  pthread_mutex_unlock(&bc_program_mu);
  if (pl) bc_drain(pl);
  bc_current = NULL;
  return atomic_load_explicit(&bc_failures, memory_order_relaxed) > 0;
}

static BcPool *bc_program_pool(void) {
  pthread_mutex_lock(&bc_program_mu);
  if (!bc_program) {
    bc_program = bc_pool();
    heff_returned = bc_program_end;
  }
  BcPool *pl = bc_program;
  pthread_mutex_unlock(&bc_program_mu);
  return pl;
}

// (how many threads the pool here has: this thread's, else the
// program's; where none is open yet, how many it will have, none
// opened)
static int64_t bc_workers(void) {
  if (bc_current) return bc_current->n;
  pthread_mutex_lock(&bc_program_mu);
  int64_t n = bc_program ? bc_program->n : bc_cores();
  pthread_mutex_unlock(&bc_program_mu);
  return n;
}

// (the pool a `when` here spawns in; a body's operation counted, and at
// its fuel's end the behaviour kept let out)
static BcPool *bc_here(void) {
  BcPool *pl = bc_current;
  if (!pl) pl = bc_current = bc_program_pool();
  if (bc_slot && bc_in_body && ++bc_fuel >= BC_FUEL) {
    BcBehaviour *kept = bc_slot;
    bc_slot = NULL;
    bc_fuel = 0;
    bc_queued(kept);
  }
  return pl;
}

// (a behaviour spawned, a cown made, and what a body takes and gives,
// where the program does it at once: its operation not built, nor what
// comes after it, heff.compile.direct's -- the same as `When`'s,
// `NewCown`'s, `Taken`'s and `Given`'s)
V heff_bocWhen(V cs, V body, V cond, V ws, V rs) {
  BcPool *pl = bc_here();
  bc_behave(pl, cs, heff_carried_fn(body), cond, INT_OF(ws), INT_OF(rs));
  return NTAG(TAG_MkUnit);
}

V heff_bocNew(V v) { return heff_foreign(bc_cown(v), bc_cown_let_go); }

V heff_bocTaken(V tn) {
  (void)tn;
  V v = bc_taken;
  if (!v) heff_fail("boc: what the cowns hold taken where no body runs, or twice");
  bc_taken = 0;
  return v;
}

V heff_bocGiven(V tn, V v) {
  (void)tn;
  if (bc_given) heff_drop(bc_given);
  bc_given = v;
  return NTAG(TAG_MkUnit);
}

static V heff_provider_boc(V p, V k) {
  V x;
  switch (heff_tag_of(p)) {
  case TAG_When: {
    V bh = bc_open(heff_dup(heff_field(p, 0)));
    V body = heff_dup(heff_field(p, 1));
    x = heff_dup(heff_field(p, 2));
    heff_drop(p);
    V cs = heff_dup(heff_field(bh, 0)), cond = heff_dup(heff_field(bh, 1));
    V ws = heff_field(bh, 2), rs = heff_field(bh, 3);
    heff_drop(bh);
    heff_bocWhen(cs, body, cond, ws, rs);
    break;
  }
  case TAG_Taken: {
    V tk = bc_open(heff_dup(heff_field(p, 0)));
    heff_drop(p);
    V g = heff_dup(heff_field(tk, 1));
    heff_drop(tk);
    x = heff_answer(g, heff_bocTaken(NTAG(TAG_MkUnit)));
    break;
  }
  case TAG_Given: {
    V gv = bc_open(heff_dup(heff_field(p, 0)));
    heff_drop(p);
    V v = heff_dup(heff_field(gv, 1));
    x = heff_dup(heff_field(gv, 2));
    heff_drop(gv);
    heff_bocGiven(NTAG(TAG_MkUnit), v);
    break;
  }
  case TAG_NewCown: {
    V mk = bc_open(heff_dup(heff_field(p, 0)));
    heff_drop(p);
    V v = heff_dup(heff_field(mk, 0)), g = heff_dup(heff_field(mk, 1));
    heff_drop(mk);
    x = heff_answer(g, heff_bocNew(v));
    break;
  }
  case TAG_Awaits: {
    V act = heff_carried_fn(heff_dup(heff_field(p, 0)));
    x = heff_dup(heff_field(p, 1));
    heff_drop(p);
    bc_await(bc_here(), act, 0);
    break;
  }
  case TAG_Races: {
    V l = heff_carried_fn(heff_dup(heff_field(p, 0)));
    V r = heff_carried_fn(heff_dup(heff_field(p, 1)));
    x = heff_dup(heff_field(p, 2));
    heff_drop(p);
    bc_await(bc_here(), l, r);
    break;
  }
  case TAG_Won: {
    int first = bc_won(heff_field(p, 0));
    V f = heff_dup(heff_field(p, 1));
    heff_drop(p);
    x = heff_answer(f, NTAG(first ? TAG_True : TAG_False));
    break;
  }
  case TAG_Workers: {
    V f = heff_dup(heff_field(p, 0));
    heff_drop(p);
    x = heff_answer(f, MK_INT(bc_workers()));
    break;
  }
  default:
    heff_fail("not an operation of boc");
    return 0;
  }
  return heff_tail(k, 1, &x);
}
