// heff's runtime for the C backend, bundled whole
// into each program it compiles, before the program's own code and its
// worlds' providers (`M.provider.c` beside `M.hf`).
//
// A value is a word.  Its low bit set, it is an integer (`n << 1 | 1`,
// 62 bits and a sign); its low bits `10`, a tag with no fields (`id << 2
// | 2`); otherwise it points to an object, whose header says what it
// is.  Tags are numbered (`TAG_x`), the ones the runtime knows first
// (below), the program's after them, each by a hash of its name; record
// labels too (`LBL_x`), a record's fields in the order it was written
// with them.  A string is bytes, `len` of them (no NUL after them, and
// any byte may be in them), UTF-8 as the program wrote it -- its runes
// read as `heff_u8_decode` reads them, what is not UTF-8 U+FFFD -- as
// the other backends have it; a provider gives one to the system, and
// makes one of what the system gives, only through the runtime's
// helpers ("What providers share" says which).  `Bytes`
// are kept as a string is, a `Str` of another kind (`K_BYT`), and cross
// by helpers of their own.
//
// An object is counted (Perceus): each owner of it holds a reference,
// `heff_dup` takes one more and `heff_drop` gives one back, the last
// freeing it.  What a function is given it owns: it consumes it (gives
// it to what it calls, keeps it in what it builds) or drops it -- the
// compiler says where; every
// primitive and the runtime's calls consume their arguments too.  What
// is static (a string written in the program, a definition's closure) is
// immortal, its count never changed.  A program runs in a thread of its
// own with a large stack.  A call last of an unknown
// function counts itself and every so often gives back a bounce (`K_BNC`),
// let go of where the value is asked for (`heff_tr`), as the JavaScript
// backend does -- unless it is a jump
// (`HEFF_LAST`), from a lambda to a closure of as many parameters, its
// arguments put where the lambda's were or, more than those, in
// `heff_room`.  A call not last of a closure of as many parameters is
// made where it is (`heff_call`), not through `heff_apply`.

#ifdef _WIN32
#include <direct.h>
#include <fcntl.h>
#include <io.h>
#include <malloc.h>
#define WIN32_LEAN_AND_MEAN
#define NOMINMAX
#include <windows.h>
#else
#include <alloca.h>
#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <sys/wait.h>
#include <unistd.h>
extern char **environ;
#if defined(__APPLE__) || defined(__FreeBSD__) || defined(__NetBSD__) || defined(__OpenBSD__) || defined(__DragonFly__)
#define HEFF_KQUEUE 1
#include <sys/event.h>
#endif
#endif
#include <errno.h>
#include <limits.h>
#include <math.h>
#include <pthread.h>
#include <setjmp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

// (a float's operations each rounded, as JavaScript's are: none of them
// fused into another, `a * b + c` into an FMA -- the program's own,
// written as C's operators where its numbers are unboxed (#39))
#pragma STDC FP_CONTRACT OFF

// (the runtime's state: defined once, in the program's first file; a
// program split into parts (`HEFF_PART`, `heff build`) declares it in the
// others)
#ifdef HEFF_PART
#define HEFF_VAR(decl) extern decl
#else
#define HEFF_VAR(decl) decl
#endif

// (the runtime's functions, but the `static inline` ones: in a program
// split into parts by an emitter that says so (`HEFF_SPLIT`, which it
// puts first), defined once too, in the first part, and in the others
// C's `inline` alone, which makes no function of a definition, and
// `noinline`, which keeps it from being copied into its callers: each a
// call to the first part's -- not a copy of each in each part, 2.6 MB
// of heff's own 15 MB of code, which ran no slower for it (#69); in a
// program of one file, or of an emitter from before, each the file's
// own)
#if defined(HEFF_SPLIT) && defined(HEFF_PART)
#define HEFF_FN inline __attribute__((noinline))
#elif defined(HEFF_SPLIT)
#define HEFF_FN
#else
#define HEFF_FN static
#endif

// Threads (#36).  A program runs in one thread of its own, unless a
// provider runs it in more, truly at once: such a provider says so by
// `#define HEFF_THREADS 1`, a line of its own, which the emitter puts
// before the runtime too (`-DHEFF_THREADS` does the same).  Then each
// thread has the runtime's per-run state for itself (`HEFF_TLS`: its
// pages, its stack of what is given back, its count of calls and
// its room, where a failure of it is caught).  An object is one thread's,
// counted by it alone, not atomically; or shared (`SHARED`, #66),
// counted atomically by every thread that holds it; or immortal,
// counted by none.  What a provider gives another thread it shares
// (`heff_share`), and runs there under `heff_try`, ending the thread by
// `heff_thread_end`.  A definition's value is computed once, under a
// lock, and made immortal (`heff_global`, `heff_freeze`), as is a static
// thunk's (`heff_force_shared`).  Without `HEFF_THREADS`, all of this is
// as one thread has it: `HEFF_TLS` is nothing, no object is shared
// (`SHARED` is 0), and nothing is locked.
#ifdef HEFF_THREADS
#define HEFF_TLS _Thread_local
#else
#define HEFF_TLS
#endif

typedef uintptr_t V;

// (a tuple (#80): what a worker gives back of a
// tag or a record it built, not built -- each value a `V`, or a flat
// number's bits as a flat field's; given back in registers where the C
// ABI lets it, else in its caller's frame, never allocated)
typedef struct { V f[1]; } HeffT1;
typedef struct { V f[2]; } HeffT2;
typedef struct { V f[3]; } HeffT3;
typedef struct { V f[4]; } HeffT4;
typedef struct { V f[5]; } HeffT5;
typedef struct { V f[6]; } HeffT6;
typedef struct { V f[7]; } HeffT7;
typedef struct { V f[8]; } HeffT8;
typedef struct { V f[9]; } HeffT9;
typedef struct { V f[10]; } HeffT10;
typedef struct { V f[11]; } HeffT11;
typedef struct { V f[12]; } HeffT12;

// (a call last whose callee takes what its caller takes -- the same
// parameters, the same result -- made a jump, the caller's frame let go
// of: clang's `musttail`, on the processors it always does it for
// (`HEFF_JUMPS`).  Elsewhere, or with `-DHEFF_NO_JUMPS`, a call, which
// a C compiler may still make a jump: a call of what is not known then
// counted, as any other (`heff_exact`))
#if defined(__clang__) && (defined(__x86_64__) || defined(__aarch64__)) && !defined(HEFF_NO_JUMPS)
#define HEFF_LAST __attribute__((musttail))
#define HEFF_JUMPS 1
#else
#define HEFF_LAST
#define HEFF_JUMPS 0
#endif

// (what is done often and is short, an integer's operation on words,
// inlined where it is used, at any optimisation; what is done seldom
// and is long, its operation on big ones, a call, out of the way, so
// that what is inlined stays short)
#define HEFF_FAST static inline __attribute__((always_inline))
#define HEFF_SLOW HEFF_FN __attribute__((noinline, cold))
#define HEFF_LIKELY(c) __builtin_expect(!!(c), 1)

// The runtime's part in Zig: built by zig into an object of its own and
// linked with the program, each function by the C ABI, given C's plain
// types and leaving allocating and counting to the C here; called, never
// inlined into the program's code.
// (hashes: of bytes, and of an integer, a word's or a big one's, both
// as "Hashes" below says)
uint64_t heff_hash_bytes(const uint8_t *p, int64_t n);
uint64_t heff_int_hash(uintptr_t a);
// (UTF-8: a rune read, the maximal subpart of what is not UTF-8 read as
// U+FFFD, as WHATWG's decoder reads it; a code point's bytes written;
// how long bytes are made text)
int heff_u8_decode(const uint8_t *p, int64_t n, uint32_t *out);
// (... a byte below 0x80 read here, where C inlines it: the decoder is
// an object of its own)
static inline int heff_u8_read(const uint8_t *p, int64_t n, uint32_t *out) {
  if (p[0] < 0x80) { *out = p[0]; return 1; }
  return heff_u8_decode(p, n, out);
}
int heff_u8_encode(uint8_t *o, uint32_t u);
int64_t heff_u8_valid_len(const uint8_t *p, int64_t n, int *own);
// (a float as a literal writes it, `show`'s text, at `out`, room for 32
// bytes)
void heff_show_float(double d, char *out);
void heff_show_float32(float f, char *out);
// (the float, of 64 bits or of 32, nearest the decimal of `n` bytes at
// `p`, correctly rounded; of what is no decimal, NaN)
double heff_float_of_decimal(const char *p, int64_t n, int bits);
// (integers beyond a word, their magnitudes compared, added, subtracted,
// multiplied and divided, as "Integers" below says; and bits read and
// written as Erlang's bit syntax has them, as "Bits" says)
int heff_mag_cmp(const uint64_t *a, int an, const uint64_t *b, int bn);
int heff_mag_add(const uint64_t *a, int an, const uint64_t *b, int bn, uint64_t *o);
int heff_mag_sub(const uint64_t *a, int an, const uint64_t *b, int bn, uint64_t *o);
void heff_mag_mul(const uint64_t *a, int an, const uint64_t *b, int bn, uint64_t *o);
uint64_t heff_mag_div1(const uint64_t *u, int m, uint64_t d, uint64_t *q);
void heff_mag_divmod(const uint64_t *u, int m, const uint64_t *v, int n, uint64_t *q, uint64_t *r, uint64_t *vn, uint64_t *un);
uint64_t heff_bits_read(const uint8_t *s, int64_t at, int64_t n);
void heff_bits_write(uint8_t *s, int64_t at, uint64_t w, int64_t n);
uint64_t heff_bits_little(uint64_t u, int64_t n, int out);

// the tags the runtime knows; a program's own are numbered after them
enum {
  TAG_True, TAG_False, TAG_Nil, TAG_Cons, TAG_MkUnit, TAG_Just, TAG_Nothing,
  TAG_MkPair, TAG_InL, TAG_InR, TAG_KNOWN
};

// (`K_TAGF`, a tag with flat fields (#64): one without is given back as
// ever, nothing looked for in it)
// (`K_FGN`, a foreign value: the host's thing, a pointer, and what lets
// it go ("Foreign values", below))
enum { K_TAG, K_REC, K_CLO, K_PAP, K_STR, K_FLT, K_ARR, K_BNC, K_CELL, K_BIG, K_BYT, K_TAGF, K_BIT, K_FGN };

typedef struct Obj {
  uint32_t rc;
  uint16_t kind;
  uint16_t tag;
} Obj;

typedef V (*Fn)(V self, V *args);

// (a tag: its fields, `n` of them; `flat`, which of its first 16 are
// flat (#64), as a record's are, below)
typedef struct { Obj h; int32_t n; uint32_t flat; V f[]; } Tag;

// (a tag's size and its flat fields, said at once: one word)
static inline void heff_tag_head(Tag *t, int64_t n, uint32_t flat) {
#if defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  uint64_t w = (uint64_t)(uint32_t)n | ((uint64_t)flat << 32);
  memcpy(&t->n, &w, sizeof w);
#else
  t->n = (int32_t)n; t->flat = flat;
#endif
}
// (a record: its fields, `n` of them, their labels `lbl`; `flat`, which
// of its first 16 fields are flat (#39) -- not a `V` but a number's 64
// bits, a `Float64`'s, an `Int64`'s or a `UInt64`'s: 2 bits each, as
// `HEFF_FLAT_F64` and the others say, 0 a `V`)
typedef struct { Obj h; int32_t n; uint32_t flat; uint32_t *lbl; V f[]; } Rec;
// (a closure: its code, how many arguments it takes, and what it holds;
// `memo`, once a thunk -- a function of one argument -- is forced, its
// value, or 0)
typedef struct { Obj h; Fn fn; int32_t arity; int32_t nenv; V memo; V env[]; } Clo;
typedef struct { Obj h; V fun; int32_t n; V a[]; } Pap;
// (a string, `Bytes` (`K_BYT`) or `Bits` (`K_BIT`): its `len` bytes, at
// `p`, which every read of them goes by.  Its own bytes are after it,
// `s`, room for `cap` of them, and `p` is `s`; unless it is a view, `p`
// in another's bytes -- its root's, never a view itself -- and that root
// held where its own bytes would be, `cap` the room it takes ("Slices").
// A view's bytes are its root's: never written, nor grown in place)
typedef struct { Obj h; int64_t len; int64_t cap; uint8_t *p; uint8_t s[]; } Str;
#define HEFF_STR_VIEW(x) ((x)->p != (x)->s)
#define HEFF_STR_ROOT(x) ((V *)(x)->s)
// (a string written in the program, static: its `n` bytes, as a C string
// literal has them -- the NUL C ends it with, after them, no byte of it)
#define HEFF_STATIC_STR(name, kind, n, bytes) \
  static struct { Obj h; int64_t len; int64_t cap; uint8_t *p; uint8_t s[(n) + 1]; } name = {{0x80000000u, kind, 0}, n, n, name.s, bytes}
#define HEFF_LIT(name, n, bytes) HEFF_STATIC_STR(name, K_STR, n, bytes)
// (`Bytes` written in the program, a binary written whole, `b["hi", 255]`,
// static as a string is)
#define HEFF_BYTES(name, n, bytes) HEFF_STATIC_STR(name, K_BYT, n, bytes)
// (a tag, a record of a definition's value of constants, static as a
// string written in the program is, its `size` fields -- more than none,
// none flat -- after it (the compiler's heff.compile.statics: one with
// flat fields it writes as a struct of its own))
#define HEFF_TAG_LIT(name, id, size, ...) \
  static struct { Obj h; int32_t n; uint32_t flat; V f[size]; } name = {{0x80000000u, K_TAG, id}, size, 0, {__VA_ARGS__}}
#define HEFF_REC_LIT(name, size, shape, ...) \
  static struct { Obj h; int32_t n; uint32_t flat; uint32_t *lbl; V f[size]; } name = {{0x80000000u, K_REC, 0}, size, 0, shape, {__VA_ARGS__}}
typedef struct { Obj h; double d; } Flt;
// (a foreign value: a pointer of the host's, the function that lets it
// go, called when the program drops the last reference; and, of a thing
// that can be ended before it is let go of, the function that ends it
// -- 0, or why it failed -- whether it is ended already, and the
// custodian it is in the custody of, 0 for the root's, and where it is
// among that one's things ("Foreign values", below))
typedef struct Fgn {
  Obj h;
  void *p;
  void (*let_go)(void *);
  const char *(*end)(void *);
  V owner;
  int32_t at;
  int32_t ended;
} Fgn;
// (an array: its elements, `n` of them, `V`s or flat -- a number's C
// type, as its header's `tag` says, `HEFF_ARR_V` or another of these
// ("Arrays", below), in the low byte of the tag.  Its room is told by
// the tag too, not by a field, so that the header stays 16 bytes and the
// elements aligned to 16 as the block is (at 24, a vectorised loop over
// `double`s splits its loads and stores across cache lines; at 32, a
// hash map's nodes take a tenth more): bits 8 to 13, `e`, 0 where the
// room is `n`, as an array is made, else the room is 2 to the `e`, `n`
// or more -- an array grown in place, `push`ed or `append`ed to, its
// room a power of 2, at least 4 (`heff_arr_cap`))
typedef struct { Obj h; int64_t n; V a[]; } Arr;
enum {
  HEFF_ARR_V, HEFF_ARR_F64, HEFF_ARR_I64, HEFF_ARR_U64, HEFF_ARR_I32, HEFF_ARR_U32,
  HEFF_ARR_I16, HEFF_ARR_U16, HEFF_ARR_I8, HEFF_ARR_U8, HEFF_ARR_F32
};
// (the bytes an element of each takes)
static const uint8_t heff_arr_width[] = { sizeof(V), 8, 8, 8, 4, 4, 2, 2, 1, 1, 4 };
// (how it keeps its elements, `HEFF_ARR_V` or another; its room's bits)
#define HEFF_ARR_KIND(r) ((unsigned)(r)->h.tag & 0xffu)
#define HEFF_ARR_ROOM 8
// (how many elements it has room for)
#define heff_arr_cap(r) \
  ((r)->h.tag >> HEFF_ARR_ROOM ? (int64_t)1 << ((r)->h.tag >> HEFF_ARR_ROOM) : (r)->n)
#define heff_arr_bytes(r) (sizeof(Arr) + (size_t)heff_arr_cap(r) * heff_arr_width[HEFF_ARR_KIND(r)])
// (the elements an object's walk sees: a flat array's none)
#define heff_arr_slots(r) (HEFF_ARR_KIND(r) == HEFF_ARR_V ? (r)->n : 0)
typedef struct { Obj h; V fun; int32_t n; V a[]; } Bnc;
typedef struct { Obj h; int32_t neg; int32_t n; uint64_t d[]; } Big;

#define IS_INT(v) (((v) & 1) == 1)
#define INT_OF(v) ((int64_t)(v) >> 1)
#define MK_INT(n) ((V)((((uint64_t)(int64_t)(n)) << 1) | 1))
#define IS_NTAG(v) (((v) & 3) == 2)
#define NTAG(id) ((V)(((uintptr_t)(id) << 2) | 2))
#define OBJ(v) ((Obj *)(v))
// (a word's integers: from -INT_LIM up to, not with, INT_LIM)
#define INT_LIM ((int64_t)1 << 62)
#define IS_OBJ(v) (((v) & 3) == 0)
// (an object's marks, the high bits of its count: the highest,
// `IMMORTAL`, set where the object is not this thread's alone -- alone,
// it is immortal, counted by none -- so that a count's fast path tests
// one bit, `heff_mine`)
#define IMMORTAL 0x80000000u
#define heff_mine(rc) (!((rc) & IMMORTAL))

// (an object shared between threads (#66, `heff_share`): counted by
// them all, atomically, and freed by the one that lets it go last --
// marked `SHARED`, both high bits, the one below the highest telling it
// from an immortal one.  What a shared object holds is shared or
// immortal; a thread's own object may hold a shared one, not the other
// way.  Without `HEFF_THREADS`, no object is: `SHARED` is 0, and a
// count is read and changed as it always was.  Threads: a count is read
// atomically too, relaxed -- a plain load, to the processor -- since
// another thread may change a shared one meanwhile)
#ifdef HEFF_THREADS
#define HEFF_SHARED_BIT 0x40000000u
#define SHARED (IMMORTAL | HEFF_SHARED_BIT)
#define heff_shared(rc) ((rc) & HEFF_SHARED_BIT)
// (an object of a cown's (boc's, `heff_own_at`): one
// behaviour's at a time, the one holding the cown, so counted as a
// thread's own, but out of line, where what a body does to it is kept
// (`HeffOwnLog`) -- marked `OWNED`, the highest bit and the one two
// below it.  `TOUCHED`, one below that, where the body's log holds it
// once, counted up)
#define HEFF_OWNED_BIT 0x20000000u
#define OWNED (IMMORTAL | HEFF_OWNED_BIT)
#define heff_owned(rc) ((rc) & HEFF_OWNED_BIT)
#define HEFF_TOUCHED_BIT 0x10000000u
#define heff_immortal(rc) (((rc) & (SHARED | OWNED)) == IMMORTAL)
#define heff_rc(o) __atomic_load_n(&(o)->rc, __ATOMIC_RELAXED)
#else
#define SHARED 0u
#define OWNED 0u
#define HEFF_TOUCHED_BIT 0u
#define heff_shared(rc) 0
#define heff_owned(rc) 0
#define heff_immortal(rc) ((rc) & IMMORTAL)
#define heff_rc(o) ((o)->rc)
#endif
// (an object's count but its marks)
#define HEFF_COUNT(rc) ((rc) & ~(IMMORTAL | SHARED | OWNED | HEFF_TOUCHED_BIT))

HEFF_FN void heff_free(V v);
HEFF_FN void heff_fail(const char *why);

#ifdef HEFF_THREADS
// (the fast paths below test the highest mark, as one thread does, and
// leave an immortal object as it is where they are; a shared one is
// counted where it is tested, up -- an instruction, where the processor
// has one, as arm64's and x86's have, where a call, even one never
// made, costs the function it is in a frame and a way out through it --
// and down, out of line, the test of its last reference a constant the
// compiler would keep in a register of its own all through the
// function.  As those of one thread, they are copied into each place
// they are used)
//
// (a shared object counted down: whether that was its last reference,
// which this thread then frees -- acquiring what every other thread did
// with it before it let it go.  One made immortal meanwhile
// (`heff_freeze`, of a static thunk's value) is never its last: what
// made it so holds it)
HEFF_FN __attribute__((noinline)) int heff_down_shared(Obj *o) {
  uint32_t was = __atomic_fetch_sub(&o->rc, 1, __ATOMIC_ACQ_REL);
  return heff_shared(was) && HEFF_COUNT(was) == 1;
}

// (what a behaviour's body did to its cowns' objects, kept while it
// runs (boc's provider), to be finished once it is done or has failed:
// the owned objects it counted up, each held here once (`TOUCHED`);
// the cowns it read, each held here, by the value that has it, with
// what it held, held here once too, and what it is to hold after; the
// arrays of what a cown holds that it writes in place, each with the
// cown's and the slot that holds it there (none where the cown does);
// and the elements it wrote of them, with what was there -- held here,
// where an array keeps `V`s, else its bits)
typedef struct { void *cell; V held, v, put; int written; } HeffOwnRoot;
typedef struct { Arr *r; V *at; int64_t root; } HeffOwnArr;
typedef struct { Arr *r; int64_t i; uint64_t old; } HeffOwnSet;
typedef struct {
  V *touched;
  int64_t nt, ct;
  HeffOwnRoot *roots;
  int64_t nr, cr;
  HeffOwnArr *arrs;
  int64_t na, ca;
  HeffOwnSet *sets;
  int64_t ns, cs;
  // (the first cells' entries, most bodies' all: none allocated)
  HeffOwnRoot first[4];
} HeffOwnLog;
HEFF_VAR(HEFF_TLS HeffOwnLog *heff_own_log);

// (room in one of a log's lists for one more)
HEFF_FN void *heff_own_room(void *p, int64_t n, int64_t *cap, size_t size) {
  if (n < *cap) return p;
  *cap = *cap ? *cap * 2 : 8;
  p = realloc(p, (size_t)*cap * size);
  if (!p) heff_fail("out of memory");
  return p;
}

// (the owned object held by the log, where it is not yet: one more
// count, the log's)
static inline uint32_t heff_own_touch(Obj *o, uint32_t rc) {
  HeffOwnLog *g = heff_own_log;
  if (!g || (rc & HEFF_TOUCHED_BIT)) return rc;
  g->touched = heff_own_room(g->touched, g->nt, &g->ct, sizeof(V));
  g->touched[g->nt++] = (V)o;
  return (rc | HEFF_TOUCHED_BIT) + 1;
}

// (an owned object counted up `m` more: as a thread's own -- only the
// behaviour holding its cown has it -- and kept by the body's log)
HEFF_FN __attribute__((noinline)) void heff_own_dup(Obj *o, uint32_t m) {
  o->rc = heff_own_touch(o, o->rc) + m;
}

// (... down: whether that was its last reference)
HEFF_FN __attribute__((noinline)) int heff_own_down(Obj *o) {
  uint32_t rc = o->rc - 1;
  o->rc = rc;
  return HEFF_COUNT(rc) == 0;
}

HEFF_FAST V heff_dup(V v) {
  if (IS_OBJ(v)) {
    uint32_t rc = heff_rc(OBJ(v));
    if (HEFF_LIKELY(heff_mine(rc))) OBJ(v)->rc = rc + 1;
    else if (heff_shared(rc)) __atomic_fetch_add(&OBJ(v)->rc, 1, __ATOMIC_RELAXED);
    else if (heff_owned(rc)) heff_own_dup(OBJ(v), 1);
  }
  return v;
}

// (a count taken down: whether that was its last reference -- never of
// an immortal object)
static inline int heff_down(Obj *o) {
  uint32_t rc = heff_rc(o);
  if (HEFF_LIKELY(heff_mine(rc))) return (o->rc = rc - 1) == 0;
  if (heff_shared(rc)) return heff_down_shared(o);
  return heff_owned(rc) && heff_own_down(o);
}

// (a count taken down where it is not the last unless the object is
// shared -- the caller knows it held more than once, or immortal: the
// last of a shared one frees it)
HEFF_FAST void heff_unref(V v) {
  uint32_t rc = heff_rc(OBJ(v));
  if (HEFF_LIKELY(heff_mine(rc))) OBJ(v)->rc = rc - 1;
  else if (heff_shared(rc)) { if (heff_down_shared(OBJ(v))) heff_free(v); }
  else if (heff_owned(rc) && heff_own_down(OBJ(v))) heff_free(v);
}
#else
static inline V heff_dup(V v) {
  if (IS_OBJ(v) && !(OBJ(v)->rc & IMMORTAL)) OBJ(v)->rc++;
  return v;
}

static inline int heff_down(Obj *o) {
  return !(o->rc & IMMORTAL) && --o->rc == 0;
}

static inline void heff_unref(V v) {
  if (!(OBJ(v)->rc & IMMORTAL)) OBJ(v)->rc--;
}
#endif

static inline void heff_drop(V v) {
  if (IS_OBJ(v) && heff_down(OBJ(v))) heff_free(v);
}

// (an object held by the caller alone, its count 1: its last reference,
// to take apart or build in.  Threads: a shared one too, its count back
// to 1 -- the other threads let it go, and none can take it again but
// through a reference the caller holds.  It is read again, acquiring
// what they did with it before they let it go, and unshared: counted by
// this thread alone from then on, so that what is built in it may be
// the thread's own, as a shared object's may not.  What it holds stays
// as it is, shared or not.  Never an immortal one)
#ifdef HEFF_THREADS
HEFF_FN __attribute__((noinline)) int heff_unshare(Obj *o) {
  if (__atomic_load_n(&o->rc, __ATOMIC_ACQUIRE) != (SHARED | 1)) return 0;
  o->rc = 1;
  return 1;
}

// (an owned one counted once: unmarked, a thread's own from then on.
// No object of a cell a body has read is held by the body alone: the
// cell holds it too, or what holds it there, so the body counted it up)
HEFF_FN __attribute__((noinline)) int heff_own_alone(Obj *o) {
  if (HEFF_COUNT(o->rc) != 1) return 0;
  o->rc = 1;
  return 1;
}

// (a shared one's count compared out of line, as `heff_down_shared`
// compares it)
static inline int heff_alone(Obj *o) {
  uint32_t rc = heff_rc(o);
  if (HEFF_LIKELY(rc == 1)) return 1;
  if (heff_shared(rc)) return heff_unshare(o);
  return heff_owned(rc) && heff_own_alone(o);
}
#else
static inline int heff_alone(Obj *o) { return o->rc == 1; }
#endif

static inline int heff_unique(V v) { return heff_alone(OBJ(v)); }

// The first thread, lent (#142).  The program runs on a thread of its
// own, its stack large and watched; the process's first thread only
// waits for its end.  A toolkit that must have that thread for its own
// (AppKit's run loop, UIKit's) is given it by a provider:
// `heff_first_thread(run, stop, u)` asks for `run(u)` there -- 0 where
// it is queued, 1 where a job is lent already (queued or running: one
// at a time), 2 where the program is ending.  The first thread runs it
// as soon as it is free; where `run` returns, the thread waits again,
// for the program's end or another job; where it never does, the
// thread is the toolkit's from then on.  No heff code runs there: what
// the program asks of the toolkit goes by the toolkit's own way to its
// thread (macOS's main queue), what the toolkit tells the program by
// the provider's (a queue and a condition, or a byte on a pipe the
// reactor waits on).  `heff_is_first_thread()`, from `main` on, says
// whether the caller is on it.
//
// The program's end while a job runs there (`heff_end`: its thread
// returning, or a failure or `exit n` on any thread -- not a stack's
// overflow, which ends it at once): with no `stop`, the ending thread
// ends the process itself, its output flushed -- the first thread need
// not come back; with `stop`, it calls `stop(u)`, which is to make
// `run` return, and waits, and the first thread, `run` returned, ends
// the process by the program's status, as it does where nothing is
// lent.  Nothing times a `stop` out: winding the toolkit up is the
// provider's, and a toolkit cut short mid-run is what `stop` is there
// to spare.  (`run` may return on its own as `stop` is called: `stop`
// only asks, never waits.)  A job queued, not begun, when the program
// ends is not run.
// The program ends once: a thread ending it after another waits, and
// the thread ending it, ending it again (an `atexit` handler's
// failure), ends it at once, as `exit` does.
typedef struct {
  void (*run)(void *);
  void (*stop)(void *);
  void *u;
  int lent;     // a job queued or running
  int running;  // begun on the first thread
  int ended;    // 0; 1, the first thread ends the process; 2, another
  int waits;    // whether the ending thread waits for the first
  int status;
  pthread_t first, ender;
  int known;    // whether `first` is set
} HeffFirst;
#ifdef HEFF_PART
extern HeffFirst heff_first;
extern pthread_mutex_t heff_first_mu;
extern pthread_cond_t heff_first_cv;
#else
HeffFirst heff_first;
pthread_mutex_t heff_first_mu = PTHREAD_MUTEX_INITIALIZER;
pthread_cond_t heff_first_cv = PTHREAD_COND_INITIALIZER;
#endif

HEFF_FN int heff_is_first_thread(void) {
  return heff_first.known && pthread_equal(pthread_self(), heff_first.first);
}

HEFF_FN int heff_first_thread(void (*run)(void *), void (*stop)(void *), void *u) {
  pthread_mutex_lock(&heff_first_mu);
  int r = heff_first.ended ? 2 : heff_first.lent ? 1 : 0;
  if (r == 0) {
    heff_first.run = run;
    heff_first.stop = stop;
    heff_first.u = u;
    heff_first.lent = 1;
    pthread_cond_broadcast(&heff_first_cv);
  }
  pthread_mutex_unlock(&heff_first_mu);
  return r;
}

// (the program's end, by `status`, begun on this thread: `returned`,
// the program's thread returning, which leaves the end to the first
// thread where nothing runs there, and returns; every other end this
// thread's, as before anything was lent)
HEFF_FN void heff_end(int status, int returned) {
  pthread_t self = pthread_self();
  pthread_mutex_lock(&heff_first_mu);
  if (heff_first.ended) {
    if (pthread_equal(heff_first.ender, self)) {
      pthread_mutex_unlock(&heff_first_mu);
      exit(status);
    }
    for (;;) pthread_cond_wait(&heff_first_cv, &heff_first_mu);
  }
  heff_first.ender = self;
  heff_first.status = status;
  if (heff_first.running && heff_first.stop && !heff_is_first_thread()) {
    void (*stop)(void *) = heff_first.stop;
    void *u = heff_first.u;
    heff_first.ended = 1;
    heff_first.waits = 1;
    pthread_mutex_unlock(&heff_first_mu);
    stop(u);
    pthread_mutex_lock(&heff_first_mu);
    for (;;) pthread_cond_wait(&heff_first_cv, &heff_first_mu);
  }
  if (returned && !heff_first.running) {
    heff_first.ended = 1;
    pthread_cond_broadcast(&heff_first_cv);
    pthread_mutex_unlock(&heff_first_mu);
    return;
  }
  heff_first.ended = 2;
  pthread_mutex_unlock(&heff_first_mu);
  fflush(stdout);
  exit(status);
}

// (what a provider runs once the program's computation has returned, on
// the program's thread, before its end: boc's, its behaviours waited
// for.  Nonzero, the program ends by 1 where it would by 0)
HEFF_VAR(int (*heff_returned)(void));

// (the program ended by `status`, from any thread of it)
HEFF_FN __attribute__((noreturn)) void heff_exit(int status) {
  heff_end(status, 0);
  exit(status);
}

// (where a value is asked for that may fail -- `heff compile` without
// `--name`, each definition printed -- a failure is caught there, and
// said; otherwise it ends the program.  Jumped to by `_longjmp`, which
// neither saves nor restores the signal mask: macOS's `setjmp` does, a
// call of the system each time, a third of a fork's cost.  A stack that
// overflowed comes back by a way of its own, which restores the mask)
HEFF_VAR(HEFF_TLS jmp_buf *heff_catch);
HEFF_VAR(HEFF_TLS const char *heff_caught);
#ifdef _WIN32
#define HEFF_SETJMP(b) setjmp(b)
#define HEFF_LONGJMP(b) longjmp(b, 1)
#else
#define HEFF_SETJMP(b) _setjmp(b)
#define HEFF_LONGJMP(b) _longjmp(b, 1)
#endif

HEFF_FN void heff_fail(const char *why) {
  if (heff_catch) { heff_caught = why; HEFF_LONGJMP(*heff_catch); }
  fflush(stdout);
  fprintf(stderr, "heff: %s\n", why);
  heff_exit(1);
}

HEFF_FN V heff_abandon(void) {
  if (heff_catch) { heff_caught = "heff:abandon"; HEFF_LONGJMP(*heff_catch); }
  fflush(stdout);
  fprintf(stderr, "heff:abandon\n");
  heff_exit(1);
}

HEFF_FN V heff_nomatch(V s);

// (`panic why`: a failure, `why` its words -- caught as `heff_fail`'s
// is, by the innermost `heff_try`, else said and the program ended.
// The words are copied, and kept: the failure ends what would give
// them back)
HEFF_FN char *heff_cstr_text(V v);
HEFF_FN V heff_panic(V s) {
  char *why = heff_cstr_text(s);
  heff_drop(s);
  heff_fail(why ? why : "panic");
  return NTAG(TAG_MkUnit);
}

HEFF_FN void *heff_alloc(size_t n) {
  void *p = malloc(n);
  if (!p) heff_fail("out of memory");
  return p;
}

// Objects are small and made and given back all the time (a
// computation's continuations, its operations, a list's cells): those of
// up to `SMALL_MAX` bytes are kept, for the next of their size, each
// multiple of 8 bytes apart.  (`-DSMALL_MAX=0`: none kept, every object
// given back to the system, so that AddressSanitizer sees a use after
// its last reference)
#ifndef SMALL_MAX
#define SMALL_MAX 128
#endif

// (each object made counted, with its bytes, where a benchmark is built
// (`-DHEFF_COUNT_ALLOCS`, as `heff bench` builds one): what its allocs/op
// and B/op are of.  Elsewhere nothing, not a counter kept)
#ifdef HEFF_COUNT_ALLOCS
#ifndef HEFF_THREADS
HEFF_VAR(uint64_t heff_allocs);
HEFF_VAR(uint64_t heff_alloc_bytes);
#endif
#define HEFF_COUNTED(c) (heff_allocs++, heff_alloc_bytes += (uint64_t)(c) * 8)
#else
#define HEFF_COUNTED(c) ((void)0)
#endif

// (a page of objects of one size, and a thread's pages, its heap -- below)
#define HEFF_PAGE ((size_t)1 << 16)
typedef struct HeffPage {
  void *free;               // what was given back here
  char *bump, *end;         // what was never used yet
  struct HeffPage *next;    // the next of its size with room
  uint32_t c, listed;       // its size, in words; on that list
#ifdef HEFF_THREADS
  struct HeffHeap *owner;   // the thread's whose page it is, else none
  void *remote;             // what other threads gave back here
  struct HeffPage *all;     // the owner's next page of its size
#endif
} HeffPage;
#define HEFF_PAGE_OF(p) ((HeffPage *)((uintptr_t)(p) & ~(uintptr_t)(HEFF_PAGE - 1)))
#define HEFF_PAGE_FIRST(pg) ((char *)(pg) + (sizeof(HeffPage) + 15) / 16 * 16)

#ifdef HEFF_THREADS
typedef struct HeffHeap {
  HeffPage *at[SMALL_MAX / 8 + 1];       // the page made in last, each size
  HeffPage *room[SMALL_MAX / 8 + 1];     // pages with room, each size
  HeffPage *all[SMALL_MAX / 8 + 1];      // all its pages, each size
  unsigned long news[SMALL_MAX / 8 + 1]; // `heff_remote_news`, as last looked
} HeffHeap;
#endif

// (where a lambda's call last of more arguments than it took is put, up
// to `HEFF_ROOM` of them -- "Calls of what is not known", below)
#define HEFF_ROOM 4

// (with threads: what each thread keeps of the runtime and uses all the
// time -- its heap, its count of calls last, its room, its stack of what
// is given back, its count of what it made -- in one block of its own,
// `heff_tls()`, found once in a function for all of them.  Where a
// thread's own variable costs a call, macOS on arm64 (`_tlv_get_addr`,
// one for each variable a function uses, and a frame for the call even
// in a leaf), the block is found as the system's own thread-specific
// data is, by the register that points to it (`tpidrro_el0`) and a key
// of heff's (`heff_tls_key`), the block put in its slot on each thread
// heff starts before it runs anything of the program's
// (`heff_tls_enter`) -- the slot read with nothing checked.  Elsewhere
// C's `_Thread_local`, an offset from the thread's register already.
// Without threads, each a variable of its own, as ever)
#ifdef HEFF_THREADS
typedef struct {
#if SMALL_MAX != 0
  HeffHeap heap;
#endif
  long dep;
  V room[HEFF_ROOM];
  V *dead;
  size_t ndead, cdead;
#ifdef HEFF_COUNT_ALLOCS
  uint64_t allocs, alloc_bytes;
#endif
} HeffTls;
HEFF_VAR(_Thread_local HeffTls heff_tls_own);
#if defined(__APPLE__) && defined(__aarch64__)
HEFF_VAR(pthread_key_t heff_tls_key);
// (the block: the key read in the same instructions, out of sight of
// the compiler, which may then find the block once for a whole
// function -- the thread, its key and its slot the same all through
// it.  `tpidrro_el0`'s low bits are not the address's)
static inline HeffTls *heff_tls(void) {
  HeffTls *t;
  __asm__("adrp %0, _heff_tls_key@PAGE\n\t"
          "ldr %0, [%0, _heff_tls_key@PAGEOFF]\n\t"
          "mrs x16, tpidrro_el0\n\t"
          "and x16, x16, #~7\n\t"
          "ldr %0, [x16, %0, lsl #3]"
          : "=r"(t) : : "x16");
  return t;
}
#define HEFF_TLS_SLOT 1
#else
#define heff_tls() (&heff_tls_own)
#endif
#if SMALL_MAX != 0
#define heff_heap (heff_tls()->heap)
#endif
#define heff_dep (heff_tls()->dep)
#define heff_room (heff_tls()->room)
#define heff_dead (heff_tls()->dead)
#define heff_ndead (heff_tls()->ndead)
#define heff_cdead (heff_tls()->cdead)
#define heff_allocs (heff_tls()->allocs)
#define heff_alloc_bytes (heff_tls()->alloc_bytes)

// (the block set as this thread's, before it runs anything of the
// program's: in a function of its own, none that uses the block, so
// that no reading of it is moved before it)
HEFF_FN __attribute__((noinline)) void heff_tls_enter(void) {
#ifdef HEFF_TLS_SLOT
  if (pthread_setspecific(heff_tls_key, &heff_tls_own) != 0) {
    fputs("heff: no room for a thread's own\n", stderr);
    exit(1);
  }
#endif
}

// (the key made, as the program starts, before any thread of it: and
// the block of the thread that made it found by it, as `heff_tls`
// finds it -- else the system keeps its own otherwise than heff knows)
HEFF_FN __attribute__((noinline)) void heff_tls_found(void) {
#ifdef HEFF_TLS_SLOT
  if (heff_tls() != &heff_tls_own) {
    fputs("heff: a thread's own not found where it was put\n", stderr);
    exit(1);
  }
#endif
}

HEFF_FN void heff_tls_begin(void) {
#ifdef HEFF_TLS_SLOT
  if (pthread_key_create(&heff_tls_key, NULL) != 0) {
    fputs("heff: no room for a thread's own\n", stderr);
    exit(1);
  }
#endif
  heff_tls_enter();
  heff_tls_found();
}
#else
HEFF_FN void heff_tls_enter(void) {}
HEFF_FN void heff_tls_begin(void) {}
#endif

#if SMALL_MAX == 0
// (none kept: each object the system's, given back to it)
HEFF_VAR(HEFF_TLS void *heff_free_list[SMALL_MAX / 8 + 1]);

static inline void *heff_obj_alloc(size_t n) {
  size_t c = (n + 7) / 8;
  HEFF_COUNTED(c);
  if (c <= SMALL_MAX / 8 && heff_free_list[c]) {
    void *p = heff_free_list[c];
    heff_free_list[c] = *(void **)p;
    return p;
  }
  return heff_alloc(c * 8);
}

static inline void heff_obj_free(void *p, size_t n) {
  size_t c = (n + 7) / 8;
  if (c <= SMALL_MAX / 8) {
    *(void **)p = heff_free_list[c];
    heff_free_list[c] = p;
  } else free(p);
}
#else
// (in pages, each of one size, its own list of what is given back: an
// object is made in the page made in last, what it was given back first,
// else in what of it was never used yet, else in another page that has
// room -- so what is made one after another is near one another, however
// long the program has run, and a list made a cell at a time from the
// front is read from the front by addresses that go up, a page at a
// time.  One list of what is given back for each size, not each page,
// would hand cells out in the order they came back -- after a list is
// filtered, every third far from the one before it -- and a long list
// read through the cache misses at each cell)
//
// (with threads, #66: a page is the thread's that made it, its owner --
// its pages are its heap, `heff_heap`, each thread's own.  What the owner
// gives back goes on the page's list, as in one thread, nothing atomic.
// What another thread gives back -- a shared object, its last holder
// another thread -- goes on the page's second list, `remote`, by a
// compare-and-swap, nothing else of the page touched; the owner takes
// that list over whole, by one exchange, where it finds no room (the
// slow path, `heff_page_alloc`).  A thread that ends gives back its pages
// that hold nothing, and leaves the others, abandoned, to whichever
// thread next finds no room in a page of their size: it adopts them)
#ifdef HEFF_THREADS
HEFF_FN void heff_page_remote(HeffPage *pg, void *p);
#define HEFF_HEAP HeffHeap *h = &heff_heap
#define HEFF_AT h->at
#define HEFF_WITH_ROOM h->room
#else
HEFF_VAR(HeffPage *heff_page_at[SMALL_MAX / 8 + 1]);
HEFF_VAR(HeffPage *heff_page_room[SMALL_MAX / 8 + 1]);
#define HEFF_HEAP
#define HEFF_AT heff_page_at
#define HEFF_WITH_ROOM heff_page_room
#endif

HEFF_FN void *heff_page_alloc(size_t c);

static inline void *heff_obj_alloc(size_t n) {
  size_t c = (n + 7) / 8;
  HEFF_COUNTED(c);
  if (c > SMALL_MAX / 8) return heff_alloc(c * 8);
  HEFF_HEAP;
  HeffPage *pg = HEFF_AT[c];
  if (pg) {
    void *p = pg->free;
    if (p) { pg->free = *(void **)p; return p; }
    if (pg->bump + c * 8 <= pg->end) { p = pg->bump; pg->bump += c * 8; return p; }
  }
  return heff_page_alloc(c);
}

static inline void heff_obj_free(void *p, size_t n) {
  size_t c = (n + 7) / 8;
  if (c > SMALL_MAX / 8) { free(p); return; }
  HeffPage *pg = HEFF_PAGE_OF(p);
  HEFF_HEAP;
#ifdef HEFF_THREADS
  if (__builtin_expect(__atomic_load_n(&pg->owner, __ATOMIC_RELAXED) != h, 0)) {
    heff_page_remote(pg, p);
    return;
  }
#endif
  *(void **)p = pg->free;
  pg->free = p;
  if (!pg->listed && pg != HEFF_AT[pg->c]) {
    pg->listed = 1;
    pg->next = HEFF_WITH_ROOM[pg->c];
    HEFF_WITH_ROOM[pg->c] = pg;
  }
}

// (a new page, of objects of `c` words)
HEFF_FN HeffPage *heff_page_new(size_t c) {
  void *m = NULL;
#ifdef _WIN32
  m = _aligned_malloc(HEFF_PAGE, HEFF_PAGE);
#else
  if (posix_memalign(&m, HEFF_PAGE, HEFF_PAGE) != 0) m = NULL;
#endif
  if (!m) heff_fail("out of memory");
  HeffPage *pg = m;
  pg->free = NULL;
  pg->bump = HEFF_PAGE_FIRST(pg);
  pg->end = (char *)m + HEFF_PAGE;
  pg->next = NULL;
  pg->c = (uint32_t)c;
  pg->listed = 0;
  return pg;
}

#ifndef HEFF_THREADS
// (the page made in last full: another of the size with room, else a
// new one)
HEFF_FN __attribute__((noinline)) void *heff_page_alloc(size_t c) {
  HeffPage *pg = heff_page_room[c];
  if (pg) {
    heff_page_room[c] = pg->next;
    pg->listed = 0;
  } else {
    pg = heff_page_new(c);
  }
  heff_page_at[c] = pg;
  void *p = pg->free;
  if (p) { pg->free = *(void **)p; return p; }
  p = pg->bump;
  pg->bump += c * 8;
  return p;
}
#else
// (how many times a page's `remote` has had something put on it when it
// had nothing -- an owner that finds no room looks through its pages for
// what other threads gave back only where this has moved since it last
// looked; and the pages each size abandoned by threads that ended)
#ifdef HEFF_PART
extern unsigned long heff_remote_news;
extern HeffPage *heff_abandoned[SMALL_MAX / 8 + 1];
extern pthread_mutex_t heff_abandoned_mu;
#else
unsigned long heff_remote_news;
HeffPage *heff_abandoned[SMALL_MAX / 8 + 1];
pthread_mutex_t heff_abandoned_mu = PTHREAD_MUTEX_INITIALIZER;
#endif

// (`p`, of a page another thread owns or none does, given back: on the
// page's `remote`)
HEFF_FN __attribute__((noinline)) void heff_page_remote(HeffPage *pg, void *p) {
  void *old = __atomic_load_n(&pg->remote, __ATOMIC_RELAXED);
  do *(void **)p = old;
  while (!__atomic_compare_exchange_n(&pg->remote, &old, p, 1, __ATOMIC_RELEASE,
                                      __ATOMIC_RELAXED));
  if (!old) __atomic_fetch_add(&heff_remote_news, 1, __ATOMIC_RELEASE);
}

// (what other threads gave back to `pg` taken over by its owner, onto its
// own list: whether there was any)
HEFF_FN int heff_page_take(HeffPage *pg) {
  if (!__atomic_load_n(&pg->remote, __ATOMIC_RELAXED)) return 0;
  void *r = __atomic_exchange_n(&pg->remote, NULL, __ATOMIC_ACQUIRE);
  if (!r) return 0;
  if (pg->free) {
    void *t = r;
    while (*(void **)t) t = *(void **)t;
    *(void **)t = pg->free;
  }
  pg->free = r;
  return 1;
}

// (`pg`, if it has room and is not the page made in last, on the list of
// those with room)
HEFF_FN void heff_page_list(HeffHeap *h, HeffPage *pg) {
  if (pg->listed || pg == h->at[pg->c]) return;
  if (!pg->free && pg->bump + pg->c * 8 > pg->end) return;
  pg->listed = 1;
  pg->next = h->room[pg->c];
  h->room[pg->c] = pg;
}

// (the page made in last full: what other threads gave back to it; else
// another of the size with room; else, if other threads gave back to any
// page since the thread last looked, what they gave to its own; else the
// pages of the size abandoned, adopted; else a new one)
HEFF_FN __attribute__((noinline)) void *heff_page_alloc(size_t c) {
  HeffHeap *h = &heff_heap;
  HeffPage *pg = h->at[c];
  if (!(pg && heff_page_take(pg))) {
    if (!h->room[c]) {
      unsigned long news = __atomic_load_n(&heff_remote_news, __ATOMIC_ACQUIRE);
      if (news != h->news[c]) {
        h->news[c] = news;
        for (HeffPage *q = h->all[c]; q; q = q->all)
          if (heff_page_take(q)) heff_page_list(h, q);
      }
    }
    if (!h->room[c] && __atomic_load_n(&heff_abandoned[c], __ATOMIC_RELAXED)) {
      pthread_mutex_lock(&heff_abandoned_mu);
      HeffPage *q = heff_abandoned[c];
      __atomic_store_n(&heff_abandoned[c], NULL, __ATOMIC_RELAXED);
      pthread_mutex_unlock(&heff_abandoned_mu);
      while (q) {
        HeffPage *next = q->all;
        __atomic_store_n(&q->owner, h, __ATOMIC_RELAXED);
        q->listed = 0;
        q->all = h->all[c];
        h->all[c] = q;
        heff_page_take(q);
        heff_page_list(h, q);
        q = next;
      }
    }
    pg = h->room[c];
    if (pg) {
      h->room[c] = pg->next;
      pg->listed = 0;
    } else {
      pg = heff_page_new(c);
      pg->remote = NULL;
      __atomic_store_n(&pg->owner, h, __ATOMIC_RELAXED);
      pg->all = h->all[c];
      h->all[c] = pg;
    }
    h->at[c] = pg;
  }
  void *p = pg->free;
  if (p) { pg->free = *(void **)p; return p; }
  p = pg->bump;
  pg->bump += c * 8;
  return p;
}

// (as a thread ends: its pages that hold nothing given back to the
// system, the others abandoned, for another thread to adopt)
HEFF_FN void heff_heap_end(void) {
  HeffHeap *h = &heff_heap;
  for (size_t c = 1; c <= SMALL_MAX / 8; c++) {
    HeffPage *left = NULL, *last = NULL;
    for (HeffPage *pg = h->all[c], *next; pg; pg = next) {
      next = pg->all;
      heff_page_take(pg);
      size_t made = (size_t)(pg->bump - HEFF_PAGE_FIRST(pg)) / (c * 8), back = 0;
      for (void *p = pg->free; p; p = *(void **)p) back++;
      if (back == made) {
#ifdef _WIN32
        _aligned_free(pg);
#else
        free(pg);
#endif
        continue;
      }
      __atomic_store_n(&pg->owner, NULL, __ATOMIC_RELAXED);
      pg->listed = 0;
      pg->all = left;
      if (!left) last = pg;
      left = pg;
    }
    if (left) {
      pthread_mutex_lock(&heff_abandoned_mu);
      last->all = heff_abandoned[c];
      __atomic_store_n(&heff_abandoned[c], left, __ATOMIC_RELAXED);
      pthread_mutex_unlock(&heff_abandoned_mu);
    }
  }
  memset(h, 0, sizeof *h);
}
#endif
#endif

static inline int heff_tag_of(V v) {
  return IS_NTAG(v) ? (int)(v >> 2) : OBJ(v)->tag;
}

// (C's condition as a Bool)
#define heff_bool(b) ((b) ? NTAG(TAG_True) : NTAG(TAG_False))

HEFF_FN V heff_tag(int id, int64_t n, V *f) {
  if (n == 0) return NTAG(id);
  Tag *t = heff_obj_alloc(sizeof(Tag) + n * sizeof(V));
  t->h.rc = 1; t->h.kind = K_TAG; t->h.tag = (uint16_t)id; heff_tag_head(t, n, 0);
  memcpy(t->f, f, n * sizeof(V));
  return (V)t;
}

static inline V heff_field(V v, int i) { return ((Tag *)v)->f[i]; }

// Flat fields (#39): a record's field of a type of 64 bits a `V` would
// allocate for -- `Float64`, `Int64`, `UInt64` -- is kept as its bits
// where the code building the record knows the type
// (the compiler's `flatOf`), and the record says so, 2 bits a
// field (`Rec`'s `flat`), so that what walks it -- a drop, a copy, a
// field looked for by its label, a value shown -- does not take the bits
// for a `V`, and a read where the type is not known boxes them.  Only the
// first `HEFF_FLAT_FIELDS` fields may be flat.  A tag's fields are kept
// so too (#64, `Tag`'s `flat`): a match reads one that may be flat as the
// tag holds it (`heff_tget_S`), and a provider given a tag with a field
// of such a type, or of a type not known, reads it by `heff_tget_v`.
enum { HEFF_FLAT_V, HEFF_FLAT_F64, HEFF_FLAT_I64, HEFF_FLAT_U64 };
#define HEFF_FLAT_FIELDS 16
// (what field `i` is, of the bits `flat`)
#define heff_flat_kind(flat, i) \
  ((i) < HEFF_FLAT_FIELDS ? (unsigned)(((flat) >> (2 * (i))) & 3) : 0u)

// (of the first `n` fields, the low bit of each's 2: `n` a constant where
// it is asked, so is this)
static inline uint32_t heff_flat_lows(int64_t n) {
  return n >= HEFF_FLAT_FIELDS ? 0x55555555u
                               : (uint32_t)(((uint64_t)1 << (2 * n)) - 1) & 0x55555555u;
}
// (whether each of the fields `lows` says is flat)
#define heff_flat_all(flat, lows) ((((flat) | ((flat) >> 1)) & (lows)) == (lows))

// (a flat field's bits, of the kind `k`, as a `V`: (below))
HEFF_FN V heff_flat_box(V w, unsigned k);

// (the labels, in the order the record was written, are the program's:
// one array for each)
HEFF_FN V heff_rec(int64_t n, uint32_t *lbl, V *f) {
  Rec *r = heff_obj_alloc(sizeof(Rec) + n * sizeof(V));
  r->h.rc = 1; r->h.kind = K_REC; r->h.tag = 0; r->n = (int32_t)n; r->flat = 0; r->lbl = lbl;
  memcpy(r->f, f, n * sizeof(V));
  return (V)r;
}

// (field `i` as a `V` counted, a flat one boxed)
static inline V heff_rec_dup_field(Rec *r, int64_t i) {
  unsigned k = heff_flat_kind(r->flat, i);
  return k ? heff_flat_box(r->f[i], k) : heff_dup(r->f[i]);
}

// (a field, the record consumed)
HEFF_FN V heff_get(V v, uint32_t l) {
  Rec *r = (Rec *)v;
  for (int64_t i = 0; i < r->n; i++)
    if (r->lbl[i] == l) {
      V x = heff_rec_dup_field(r, i);
      heff_drop(v);
      return x;
    }
  heff_fail("no such field");
  return 0;
}

// (a match's scrutinee given up on an arm, which takes the fields in
// `keep` (a bit each): its last reference, its shell freed and the
// other fields dropped; otherwise each kept field counted)
static inline void heff_take(V v, uint64_t keep) {
  if (!IS_OBJ(v)) return;
  Tag *t = (Tag *)v;
  if (heff_alone(&t->h)) {
    for (int64_t i = 0; i < t->n; i++)
      if (!((keep >> i) & 1) && !heff_flat_kind(t->flat, i)) heff_drop(t->f[i]);
    heff_obj_free(t, sizeof(Tag) + t->n * sizeof(V));
  } else {
    for (int64_t i = 0; i < t->n; i++)
      if ((keep >> i) & 1) heff_dup(t->f[i]);
    heff_unref((V)t);
  }
}

// (as `heff_take`, the cell kept for a tag of its size to be built in
// (`heff_tag_at`): its last reference, the cell itself, its fields
// taken or dropped and blanked; otherwise none, 0)
static inline V heff_take_reuse(V v, uint64_t keep) {
  Tag *t = (Tag *)v;
  if (heff_alone(&t->h)) {
    for (int64_t i = 0; i < t->n; i++) {
      if (!((keep >> i) & 1) && !heff_flat_kind(t->flat, i)) heff_drop(t->f[i]);
      t->f[i] = MK_INT(0);
    }
    t->flat = 0; t->h.kind = K_TAG;
    return v;
  }
  for (int64_t i = 0; i < t->n; i++)
    if ((keep >> i) & 1) heff_dup(t->f[i]);
  heff_unref((V)t);
  return MK_INT(0);
}

// Drops specialised (#26): where the emitter knows what a value is -- a
// tag of `n` fields, the arm it is in matching it -- it gives it back
// as that, not through `heff_drop`, nor `heff_take`'s loops over what
// the cell says.  `n` and `keep` are constants where these are called,
// so each is compiled to the few steps that tag needs: its loops
// unrolled, its size class known.  (`heff_take` and `heff_take_reuse`
// stay for a compiler from before, building this runtime's compiler.)
// (Not optimised, `-O0`, each is a call: inlined there, its every step a
// slot of its caller's frame, a recursion a million deep -- a list built
// by a call that is not last -- would overflow the stack.)
#ifdef __OPTIMIZE__
#define HEFF_KNOWN static inline __attribute__((always_inline))
#else
#define HEFF_KNOWN static inline
#endif

// (the fields of a tag not in `keep` dropped, its flat ones (#64) none)
HEFF_FN __attribute__((noinline)) void heff_tag_unset(Tag *t, uint64_t keep, int64_t n) {
  for (int64_t i = 0; i < n; i++)
    if (!((keep >> i) & 1) && !heff_flat_kind(t->flat, i)) heff_drop(t->f[i]);
}

// (`heff_take`, of a tag of `n` fields)
HEFF_KNOWN void heff_take_n(V v, uint64_t keep, int64_t n) {
  Tag *t = (Tag *)v;
  if (heff_alone(&t->h)) {
    for (int64_t i = 0; i < n; i++)
      if (!((keep >> i) & 1)) heff_drop(t->f[i]);
    heff_obj_free(t, sizeof(Tag) + n * sizeof(V));
  } else {
    for (int64_t i = 0; i < n; i++)
      if ((keep >> i) & 1) heff_dup(t->f[i]);
    heff_unref((V)t);
  }
}

// (... of a tag that may have flat fields (#64): one of them is never in
// `keep` -- it is read as the tag holds it -- and dropped here only if it
// is a `V`)
HEFF_KNOWN void heff_take_nf(V v, uint64_t keep, int64_t n) {
  Tag *t = (Tag *)v;
  if (heff_alone(&t->h) && t->flat) {
    heff_tag_unset(t, keep, n);
    heff_obj_free(t, sizeof(Tag) + n * sizeof(V));
  } else heff_take_n(v, keep, n);
}

// (`heff_take_reuse`, of a tag of `n` fields: its fields not blanked, the
// cell kept being either built in (`heff_tag_at`, each field written) or
// freed as the cell it is (`heff_drop_cell`), never looked into)
HEFF_KNOWN V heff_take_reuse_n(V v, uint64_t keep, int64_t n) {
  Tag *t = (Tag *)v;
  if (heff_alone(&t->h)) {
    for (int64_t i = 0; i < n; i++)
      if (!((keep >> i) & 1)) heff_drop(t->f[i]);
    return v;
  }
  for (int64_t i = 0; i < n; i++)
    if ((keep >> i) & 1) heff_dup(t->f[i]);
  heff_unref((V)t);
  return MK_INT(0);
}

// (... of a tag that may have flat fields (#64), as `heff_take_nf`: the
// cell kept made plain, as `heff_tag_at_n` wants it -- `heff_tag_at_nf`
// says its flat fields anew)
HEFF_KNOWN V heff_take_reuse_nf(V v, uint64_t keep, int64_t n) {
  Tag *t = (Tag *)v;
  if (heff_alone(&t->h) && t->flat) {
    heff_tag_unset(t, keep, n);
    t->flat = 0; t->h.kind = K_TAG;
    return v;
  }
  return heff_take_reuse_n(v, keep, n);
}

// (... of a tag whose fields not in `keep` are all flat, in every tag of
// it the program builds (the compiler's `sure`): none
// dropped, nothing looked for)
HEFF_KNOWN void heff_take_na(V v, uint64_t keep, int64_t n) {
  Tag *t = (Tag *)v;
  if (heff_alone(&t->h)) heff_obj_free(t, sizeof(Tag) + n * sizeof(V));
  else {
    for (int64_t i = 0; i < n; i++)
      if ((keep >> i) & 1) heff_dup(t->f[i]);
    heff_unref((V)t);
  }
}

HEFF_KNOWN V heff_take_reuse_na(V v, uint64_t keep, int64_t n) {
  Tag *t = (Tag *)v;
  if (heff_alone(&t->h)) {
    t->flat = 0; t->h.kind = K_TAG;
    return v;
  }
  return heff_take_reuse_n(v, keep, n);
}

// (a tag of `n` fields dropped: its last reference, its fields dropped
// and its cell freed at once; otherwise counted down)
HEFF_KNOWN void heff_drop_tag(V v, int64_t n) {
  Tag *t = (Tag *)v;
  if (heff_alone(&t->h)) {
    if (t->flat) heff_tag_unset(t, 0, n);
    else
      for (int64_t i = 0; i < n; i++) heff_drop(t->f[i]);
    heff_obj_free(t, sizeof(Tag) + n * sizeof(V));
  } else heff_unref((V)t);
}

// (a cell kept for a tag of `n` fields (`heff_take_reuse_n`) and not
// built in: freed, what was in it given back already; none kept,
// nothing)
HEFF_KNOWN void heff_drop_cell(V r, int64_t n) {
  if (IS_OBJ(r)) heff_obj_free((void *)r, sizeof(Tag) + n * sizeof(V));
}

// (a tag built in the cell `r` kept for it, or a new one)
static inline V heff_tag_at(V r, int id, int64_t n, V *f) {
  if (!IS_OBJ(r)) return heff_tag(id, n, f);
  Tag *t = (Tag *)r;
  t->h.kind = K_TAG; t->h.tag = (uint16_t)id; t->flat = 0;
  memcpy(t->f, f, n * sizeof(V));
  return r;
}

HEFF_FN V heff_clo(Fn fn, int arity, int nenv, V *env) {
  Clo *c = heff_obj_alloc(sizeof(Clo) + nenv * sizeof(V));
  c->h.rc = 1; c->h.kind = K_CLO; c->h.tag = 0;
  c->fn = fn; c->arity = arity; c->nenv = nenv; c->memo = 0;
  if (nenv) memcpy(c->env, env, nenv * sizeof(V));
  return (V)c;
}

static inline V *heff_env(V self) { return ((Clo *)self)->env; }

// Constructions at their known size (#34): where the emitter builds a
// tag, a record or a closure, it knows how many fields it has, a
// constant where these are called -- so each is compiled to its size
// class's free list taken from and its fields stored, not given to a
// function that copies them with `memcpy`.  (`heff_tag`, `heff_rec`,
// `heff_clo` stay for what does not know, and for a compiler from
// before.)

// (the fields at `f`, `n` of them, stored at `to`: `n` a constant, the
// loop unrolled, `f` a compound literal's, each stored where it is
// computed)
HEFF_KNOWN void heff_fields_n(V *to, V *f, int64_t n) {
  for (int64_t i = 0; i < n; i++) to[i] = f[i];
}

// (a tag of `n` fields, `n` more than none)
HEFF_KNOWN V heff_tag_n(int id, int64_t n, V *f) {
  Tag *t = heff_obj_alloc(sizeof(Tag) + n * sizeof(V));
  t->h.rc = 1; t->h.kind = K_TAG; t->h.tag = (uint16_t)id; heff_tag_head(t, n, 0);
  heff_fields_n(t->f, f, n);
  return (V)t;
}

// (... some of its fields flat (#64), as `flat` says: each given as its
// bits, `heff_word_f64` and the others)
HEFF_KNOWN V heff_tag_nf(int id, int64_t n, uint32_t flat, V *f) {
  Tag *t = heff_obj_alloc(sizeof(Tag) + n * sizeof(V));
  t->h.rc = 1; t->h.kind = K_TAGF; t->h.tag = (uint16_t)id; heff_tag_head(t, n, flat);
  heff_fields_n(t->f, f, n);
  return (V)t;
}

// (a tag of `n` fields built in the cell `r` kept for it, or a new one:
// a cell kept by `heff_take_reuse_n`, which says it has no flat fields)
HEFF_KNOWN V heff_tag_at_n(V r, int id, int64_t n, V *f) {
  if (!IS_OBJ(r)) return heff_tag_n(id, n, f);
  Tag *t = (Tag *)r;
  t->h.tag = (uint16_t)id;
  heff_fields_n(t->f, f, n);
  return r;
}

// (... the fields of `same` there already, each read from the cell at
// its place and given back there: stored only in a new one)
HEFF_KNOWN V heff_tag_re_n(V r, int id, int64_t n, uint64_t same, V *f) {
  if (!IS_OBJ(r)) return heff_tag_n(id, n, f);
  Tag *t = (Tag *)r;
  t->h.tag = (uint16_t)id;
  for (int64_t i = 0; i < n; i++)
    if (!((same >> i) & 1)) t->f[i] = f[i];
  return r;
}

HEFF_KNOWN V heff_tag_at_nf(V r, int id, int64_t n, uint32_t flat, V *f) {
  if (!IS_OBJ(r)) return heff_tag_nf(id, n, flat, f);
  Tag *t = (Tag *)r;
  t->h.kind = K_TAGF; t->h.tag = (uint16_t)id; t->flat = flat;
  heff_fields_n(t->f, f, n);
  return r;
}

// (what a tag's field waits as, a hole: no object, nothing to drop; and
// field `i` of the cell `d`, made with a hole there that nothing has
// seen yet, set to `v`: what a call of itself gives put where a tag waits
// for it -- a destination; `d` consumed, `v` given back, counted)
static inline V heff_hole(void) { return MK_INT(0); }

static inline V heff_setField(V d, V i, V v) {
  ((Tag *)d)->f[INT_OF(i)] = v;
  heff_drop(d);
  return heff_dup(v);
}

// (... of a cell lent, a destination's: not given up, and the value set
// given back lent, held by the cell -- no reference taken nor dropped)
static inline V heff_setFieldPeek(V d, V i, V v) {
  ((Tag *)d)->f[INT_OF(i)] = v;
  return v;
}

// (a record of `n` fields, its labels `lbl`)
HEFF_KNOWN V heff_rec_n(int64_t n, uint32_t *lbl, V *f) {
  Rec *r = heff_obj_alloc(sizeof(Rec) + n * sizeof(V));
  r->h.rc = 1; r->h.kind = K_REC; r->h.tag = 0; r->n = (int32_t)n; r->flat = 0; r->lbl = lbl;
  heff_fields_n(r->f, f, n);
  return (V)r;
}

// (... some of its fields flat, as `flat` says: each given as its bits,
// `heff_word_f64` and the others)
HEFF_KNOWN V heff_rec_nf(int64_t n, uint32_t *lbl, uint32_t flat, V *f) {
  Rec *r = heff_obj_alloc(sizeof(Rec) + n * sizeof(V));
  r->h.rc = 1; r->h.kind = K_REC; r->h.tag = 0; r->n = (int32_t)n; r->flat = flat; r->lbl = lbl;
  heff_fields_n(r->f, f, n);
  return (V)r;
}

// (a closure holding `n`, more than none)
HEFF_KNOWN V heff_clo_n(Fn fn, int arity, int64_t n, V *env) {
  Clo *c = heff_obj_alloc(sizeof(Clo) + n * sizeof(V));
  c->h.rc = 1; c->h.kind = K_CLO; c->h.tag = 0;
  c->fn = fn; c->arity = arity; c->nenv = (int32_t)n; c->memo = 0;
  heff_fields_n(c->env, env, n);
  return (V)c;
}

// Fields at their known place (#34): a record's fields are those of its
// type that are not types, in the order the type has them (its shape),
// so where the emitter knows the type -- erasure gives each
// projection its record's shape -- it reads a field at its place, not
// looking for its label (`heff_get`).

// (field `i`, the record not consumed)
#define heff_rfield(v, i) (((Rec *)(v))->f[i])

// (a record's fields but the `i`th dropped and its cell freed: for a
// record of many fields, a call, not as many drops where it is read)
#ifndef HEFF_FEW_FIELDS
#define HEFF_FEW_FIELDS 2
#endif
HEFF_FN __attribute__((noinline)) void heff_rec_give(V v, int64_t i) {
  Rec *r = (Rec *)v;
  for (int64_t j = 0; j < r->n; j++)
    if (j != i) heff_drop(r->f[j]);
  heff_obj_free(r, sizeof(Rec) + r->n * sizeof(V));
}

// (`heff_get_n` of a record with flat fields: the field as a `V`, the
// record dropped)
HEFF_FN __attribute__((noinline)) V heff_get_flat(V v, int64_t i) {
  V x = heff_rec_dup_field((Rec *)v, i);
  heff_drop(v);
  return x;
}

// (field `i` of a record of `n` fields, the record consumed: its last
// reference, the field taken over, the others dropped and its cell freed;
// otherwise the field counted)
HEFF_KNOWN V heff_get_n(V v, int64_t i, int64_t n) {
  Rec *r = (Rec *)v;
  if (r->flat) return heff_get_flat(v, i);
  V x = r->f[i];
  if (heff_alone(&r->h)) {
    if (n > HEFF_FEW_FIELDS) heff_rec_give(v, i);
    else {
      for (int64_t j = 0; j < n; j++)
        if (j != i) heff_drop(r->f[j]);
      heff_obj_free(r, sizeof(Rec) + n * sizeof(V));
    }
  } else {
    heff_dup(x);
    heff_unref((V)r);
  }
  return x;
}

// (field `i` of a record wanted after, which after it is only read other
// fields of, then updated or dropped (the compiler's `takesFor`):
// its last reference, the field taken out of it -- moved, not counted, a
// hole left that drops as nothing; otherwise the field counted.  Never a
// field that may be flat: one that is is read where it is)
HEFF_KNOWN V heff_take_field(V v, int64_t i) {
  Rec *r = (Rec *)v;
  V x = r->f[i];
  if (heff_alone(&r->h)) r->f[i] = MK_INT(0);
  else heff_dup(x);
  return x;
}

// A record updated (#34): one built of the same shape as the record `v`
// it is built from, some of its fields read from `v`'s at their own
// places (`keep`, a bit each) and `v` given up there, is built in `v`'s
// cell where that was `v`'s last reference -- the fields kept left where
// they are, counted neither up nor down, the others dropped -- as a tag
// is in a cell kept for it (Perceus's reuse).  Shared, `v` is copied:
// the fields kept counted, `v` counted down.  Either way the fields not
// kept are stored by the caller, at once.
//
// Its flat fields (#39) are as `v`'s are where they are kept -- `kept`,
// the bits of those of them that may be flat, 3 each -- and as `flat`
// says where they are stored (`heff_rec_reuse_nf`).
HEFF_FN __attribute__((noinline)) V heff_rec_copy(V v, uint64_t keep, uint32_t *lbl, uint32_t kept, uint32_t flat) {
  Rec *r = (Rec *)v;
  int64_t n = r->n;
  uint32_t was = r->flat;
  Rec *c = heff_obj_alloc(sizeof(Rec) + n * sizeof(V));
  c->h.rc = 1; c->h.kind = K_REC; c->h.tag = 0; c->n = (int32_t)n; c->lbl = lbl;
  c->flat = (was & kept) | flat;
  for (int64_t i = 0; i < n; i++)
    c->f[i] = !((keep >> i) & 1) ? MK_INT(0)
            : heff_flat_kind(was, i) ? r->f[i] : heff_dup(r->f[i]);
  heff_unref((V)r);
  return (V)c;
}

// (a record with flat fields, built in its cell: the fields not kept
// dropped, as they were)
HEFF_FN __attribute__((noinline)) void heff_rec_unset(Rec *r, uint64_t keep) {
  for (int64_t i = 0; i < r->n; i++)
    if (!((keep >> i) & 1) && !heff_flat_kind(r->flat, i)) heff_drop(r->f[i]);
}

HEFF_KNOWN V heff_rec_reuse_nf(V v, uint64_t keep, int64_t n, uint32_t *lbl, uint32_t kept, uint32_t flat) {
  Rec *r = (Rec *)v;
  if (!heff_alone(&r->h)) {
    if (n > HEFF_FEW_FIELDS || r->flat) return heff_rec_copy(v, keep, lbl, kept, flat);
    Rec *c = heff_obj_alloc(sizeof(Rec) + n * sizeof(V));
    c->h.rc = 1; c->h.kind = K_REC; c->h.tag = 0; c->n = (int32_t)n; c->flat = flat; c->lbl = lbl;
    for (int64_t i = 0; i < n; i++)
      if ((keep >> i) & 1) c->f[i] = heff_dup(r->f[i]);
    heff_unref((V)r);
    return (V)c;
  }
  uint32_t was = r->flat;
  if (was) {
    // (none to drop where each field stored anew was flat: a number's
    // record updated with numbers)
    uint32_t anew = heff_flat_lows(n) & ~kept;
    if (n > HEFF_FLAT_FIELDS || !heff_flat_all(was, anew)) heff_rec_unset(r, keep);
    r->flat = (was & kept) | flat;
  } else {
    for (int64_t i = 0; i < n; i++)
      if (!((keep >> i) & 1)) heff_drop(r->f[i]);
    if (flat) r->flat = flat;
  }
  r->lbl = lbl;
  return v;
}

// (... where the fields stored anew are flat in every record of its
// shape the program builds (the compiler's `sureRecs`): the
// record's last reference, none dropped, nothing looked for)
HEFF_KNOWN V heff_rec_reuse_na(V v, uint64_t keep, int64_t n, uint32_t *lbl, uint32_t kept, uint32_t flat) {
  Rec *r = (Rec *)v;
  if (heff_alone(&r->h)) {
    r->flat = (r->flat & kept) | flat;
    r->lbl = lbl;
    return v;
  }
  return heff_rec_reuse_nf(v, keep, n, lbl, kept, flat);
}

// (... of a compiler from before #39, which keeps no field flat)
static inline uint32_t heff_kept_bits(uint64_t keep) {
  uint32_t kept = 0;
  for (int i = 0; i < HEFF_FLAT_FIELDS; i++)
    if ((keep >> i) & 1) kept |= 3u << (2 * i);
  return kept;
}

HEFF_KNOWN V heff_rec_reuse_n(V v, uint64_t keep, int64_t n, uint32_t *lbl) {
  return heff_rec_reuse_nf(v, keep, n, lbl, heff_kept_bits(keep), 0);
}

// (a lambda's closure, holding `n`, given up where its body starts,
// which takes what it holds (#26): its last reference, its shell freed;
// otherwise each counted.  `n` is a constant where it is called)
static inline __attribute__((always_inline)) void heff_clo_take(V self, int64_t n) {
  Clo *c = (Clo *)self;
  if (heff_alone(&c->h)) {
    if (c->memo) heff_drop(c->memo);
    heff_obj_free(c, sizeof(Clo) + n * sizeof(V));
  } else {
    for (int64_t i = 0; i < n; i++) heff_dup(c->env[i]);
    heff_unref((V)c);
  }
}

// (an object's size, from what it is)
HEFF_FN size_t heff_size(V v) {
  Obj *o = OBJ(v);
  switch (o->kind) {
  case K_TAG: case K_TAGF: return sizeof(Tag) + ((Tag *)v)->n * sizeof(V);
  case K_REC: return sizeof(Rec) + ((Rec *)v)->n * sizeof(V);
  case K_CLO: return sizeof(Clo) + ((Clo *)v)->nenv * sizeof(V);
  case K_PAP: return sizeof(Pap) + ((Pap *)v)->n * sizeof(V);
  case K_STR: case K_BYT: case K_BIT: return sizeof(Str) + ((Str *)v)->cap;
  case K_FLT: return sizeof(Flt);
  case K_ARR: return heff_arr_bytes((Arr *)v);
  case K_BNC: return sizeof(Bnc) + ((Bnc *)v)->n * sizeof(V);
  case K_BIG: return sizeof(Big) + ((Big *)v)->n * sizeof(uint64_t);
  case K_FGN: return sizeof(Fgn);
  default: return SMALL_MAX + 1;
  }
}

// (a record or a tag whose last reference is gone, its flat fields (#39,
// #64) made words that drop as nothing, as its other fields are given
// back)
HEFF_FN __attribute__((noinline)) void heff_flat_clear(V *f, int64_t n, uint32_t flat) {
  for (int64_t i = 0; i < n && i < HEFF_FLAT_FIELDS; i++)
    if (heff_flat_kind(flat, i)) f[i] = MK_INT(0);
}

// (what is given back, a stack of it, not a recursion: a long list's
// cells given back one after another, the stack as deep as the list
// never -- with threads, each thread's, in its block)
#ifndef HEFF_THREADS
HEFF_VAR(V *heff_dead);
HEFF_VAR(size_t heff_ndead);
HEFF_VAR(size_t heff_cdead);
#endif

// (a value whose last reference this was, put on the stack)
static inline void heff_dead_put(V v) {
  if (heff_ndead == heff_cdead) {
    heff_cdead = heff_cdead ? heff_cdead * 2 : 1024;
    heff_dead = realloc(heff_dead, heff_cdead * sizeof(V));
    if (!heff_dead) heff_fail("out of memory");
  }
  heff_dead[heff_ndead++] = v;
}

// (a value counted down: put on the stack if that was its last reference)
static inline void heff_dead_push(V v) {
  if (!IS_OBJ(v) || !heff_down(OBJ(v))) return;
  heff_dead_put(v);
}

static void heff_foreign_gone(struct Fgn *g);

// (an object whose last reference is gone: what it holds counted down,
// its size reckoned as it is looked at, and it freed; of what it holds,
// each whose last reference that was is given back after it -- the last
// of them next, at once, the others from the stack: a list's cells one
// after another, its spine never on the stack)
__attribute__((noinline)) HEFF_FN void heff_free(V v) {
  size_t base = heff_ndead;
  for (;;) {
    Obj *o = OBJ(v);
    V *f = NULL, next = 0;
    int64_t n = 0;
    size_t size;
    switch (o->kind) {
    case K_TAG: { Tag *t = (Tag *)v; n = t->n; f = t->f; size = sizeof(Tag) + n * sizeof(V); break; }
    case K_TAGF: {
      Tag *t = (Tag *)v; n = t->n; f = t->f; size = sizeof(Tag) + n * sizeof(V);
      heff_flat_clear(t->f, t->n, t->flat);
      break;
    }
    case K_REC: {
      Rec *r = (Rec *)v; n = r->n; f = r->f; size = sizeof(Rec) + n * sizeof(V);
      if (r->flat) heff_flat_clear(r->f, r->n, r->flat);
      break;
    }
    case K_CLO: {
      Clo *c = (Clo *)v; n = c->nenv; f = c->env; size = sizeof(Clo) + n * sizeof(V);
      if (c->memo) heff_dead_push(c->memo);
      break;
    }
    case K_PAP: { Pap *p = (Pap *)v; heff_dead_push(p->fun); n = p->n; f = p->a; size = sizeof(Pap) + n * sizeof(V); break; }
    case K_ARR: { Arr *r = (Arr *)v; n = heff_arr_slots(r); f = r->a; size = heff_arr_bytes(r); break; }
    case K_BNC: { Bnc *b = (Bnc *)v; heff_dead_push(b->fun); n = b->n; f = b->a; size = sizeof(Bnc) + n * sizeof(V); break; }
    // (a foreign value's last reference gone: the host's thing let go of)
    // (and its custodian counted down after, where it has one)
    case K_FGN: {
      Fgn *g = (Fgn *)v;
      heff_foreign_gone(g);
      if (g->owner) { n = 1; f = &g->owner; }
      size = sizeof(Fgn);
      break;
    }
    // (a view: its root counted down)
    case K_STR: case K_BYT: case K_BIT: {
      Str *x = (Str *)v; size = sizeof(Str) + x->cap;
      if (HEFF_STR_VIEW(x)) { n = 1; f = HEFF_STR_ROOT(x); }
      break;
    }
    default: size = heff_size(v); break;
    }
    for (int64_t i = 0; i < n; i++) {
      V x = f[i];
      if (!IS_OBJ(x) || !heff_down(OBJ(x))) continue;
      if (next) heff_dead_put(next);
      next = x;
    }
    heff_obj_free(o, size);
    if (next) v = next;
    else if (heff_ndead > base) v = heff_dead[--heff_ndead];
    else return;
  }
}

// (a record of `n` fields dropped, its shape known (#34): its last
// reference, its fields dropped and its cell freed at once -- of many
// fields, by the walk; otherwise counted down)
HEFF_KNOWN void heff_drop_rec(V v, int64_t n) {
  Rec *r = (Rec *)v;
  if (heff_alone(&r->h)) {
    // (a record of numbers, all flat: its cell, nothing in it)
    if (r->flat && n <= HEFF_FLAT_FIELDS && heff_flat_all(r->flat, heff_flat_lows(n)))
      heff_obj_free(r, sizeof(Rec) + n * sizeof(V));
    else if (n > HEFF_FEW_FIELDS || r->flat) heff_free(v);
    else {
      for (int64_t i = 0; i < n; i++) heff_drop(r->f[i]);
      heff_obj_free(r, sizeof(Rec) + n * sizeof(V));
    }
  } else heff_unref((V)r);
}

// (a closure holding `n` dropped, as `heff_drop_rec` a record)
HEFF_KNOWN void heff_drop_clo(V v, int64_t n) {
  Clo *c = (Clo *)v;
  if (heff_alone(&c->h)) {
    if (n > HEFF_FEW_FIELDS) heff_free(v);
    else {
      if (c->memo) heff_drop(c->memo);
      for (int64_t i = 0; i < n; i++) heff_drop(c->env[i]);
      heff_obj_free(c, sizeof(Clo) + n * sizeof(V));
    }
  } else heff_unref((V)c);
}

// Values between threads (#36)
// ---------------------------------------------------------------------

// (a tag's or a record's fields, an array's elements, a string view's
// root: `*n` of them -- a closure's, a partial application's and a
// bounce's are said by `HEFF_EACH_SLOT`; another string, a float and a
// big integer hold none)
HEFF_FN V *heff_slots(V v, int64_t *n) {
  Obj *o = OBJ(v);
  switch (o->kind) {
  case K_TAG: case K_TAGF: *n = ((Tag *)v)->n; return ((Tag *)v)->f;
  case K_REC: *n = ((Rec *)v)->n; return ((Rec *)v)->f;
  case K_ARR: *n = heff_arr_slots((Arr *)v); return ((Arr *)v)->a;
  case K_STR: case K_BYT: case K_BIT:
    *n = HEFF_STR_VIEW((Str *)v); return HEFF_STR_ROOT((Str *)v);
  default: *n = 0; return NULL;
  }
}

// (a stack of objects, for a walk that is not a recursion: a long
// list's spine never on the C stack)
typedef struct { V *v; size_t n, cap; } HeffStack;

HEFF_FN void heff_stack_push(HeffStack *s, V v) {
  if (s->n == s->cap) {
    s->cap = s->cap ? s->cap * 2 : 256;
    s->v = realloc(s->v, s->cap * sizeof(V));
    if (!s->v) heff_fail("out of memory");
  }
  s->v[s->n++] = v;
}

// (each place of the object `v` holds a value in, given to `f`)
// (a record's flat fields (#39) none, nor a tag's (#64))
#define HEFF_EACH_SLOT(v, f, u)                                         \
  do {                                                                  \
    Obj *o_ = OBJ(v);                                                   \
    int64_t n_;                                                         \
    V *s_ = heff_slots(v, &n_);                                         \
    uint32_t fl_ = o_->kind == K_REC ? ((Rec *)(v))->flat               \
                 : o_->kind == K_TAGF ? ((Tag *)(v))->flat : 0;         \
    for (int64_t i_ = 0; i_ < n_; i_++)                                 \
      if (!heff_flat_kind(fl_, i_)) f(u, &s_[i_]);                      \
    if (o_->kind == K_CLO) {                                            \
      Clo *c_ = (Clo *)(v);                                             \
      for (int32_t i_ = 0; i_ < c_->nenv; i_++) f(u, &c_->env[i_]);     \
      if (c_->memo) f(u, &c_->memo);                                    \
    } else if (o_->kind == K_PAP) {                                     \
      Pap *p_ = (Pap *)(v);                                             \
      for (int32_t i_ = 0; i_ < p_->n; i_++) f(u, &p_->a[i_]);          \
      f(u, &p_->fun);                                                   \
    } else if (o_->kind == K_BNC) {                                     \
      Bnc *b_ = (Bnc *)(v);                                             \
      for (int32_t i_ = 0; i_ < b_->n; i_++) f(u, &b_->a[i_]);          \
      f(u, &b_->fun);                                                   \
    }                                                                   \
  } while (0)

HEFF_FN void heff_freeze_one(HeffStack *s, V *at) {
#ifdef HEFF_THREADS
  // (a shared thunk's `memo` another thread may put a value in meanwhile)
  V v = __atomic_load_n(at, __ATOMIC_ACQUIRE);
#else
  V v = *at;
#endif
  if (!IS_OBJ(v) || !v) return;
  uint32_t rc = heff_rc(OBJ(v));
  if (heff_immortal(rc)) return;
#ifdef HEFF_THREADS
  // (a shared object, other threads counting it meanwhile: its mark
  // that tells it from an immortal one taken off, over its count, which
  // they leave as it is from then on)
  if (heff_shared(rc)) __atomic_fetch_and(&OBJ(v)->rc, ~HEFF_SHARED_BIT, __ATOMIC_RELAXED);
  else
#endif
    OBJ(v)->rc = IMMORTAL;
  heff_stack_push(s, v);
}

// (`v` made immortal, and all it holds: shared between threads from now
// on, each counting it never, and never freed -- what holds it now
// leaks it.  What of `v` is mortal is this thread's, no other's yet;
// what is shared another thread may hold too, and counts no more)
HEFF_FN void heff_freeze(V v) {
  HeffStack s = {0};
  heff_freeze_one(&s, &v);
  while (s.n) {
    V o = s.v[--s.n];
    HEFF_EACH_SLOT(o, heff_freeze_one, &s);
  }
  free(s.v);
}

#ifdef HEFF_THREADS
HEFF_FN void heff_share_one(HeffStack *s, V *at) {
  V v = *at;
  if (!IS_OBJ(v) || !v) return;
  uint32_t rc = heff_rc(OBJ(v));
  if (!heff_mine(rc) && !heff_owned(rc)) return;
  OBJ(v)->rc = HEFF_COUNT(rc) | SHARED;
  heff_stack_push(s, v);
}

// (`v` shared (#66), to hand to other threads: each mortal object of it
// marked `SHARED`, counted atomically from then on, by every thread that
// holds it, and freed by the one that lets it go last.  The walk stops
// at what is shared already or immortal -- what a shared object holds
// is shared or immortal -- so a value shared again is walked only where
// it is new.  `v` not consumed, nothing copied: another thread holds it
// by one more count (`heff_dup`).  What of `v` is mortal is this
// thread's: no other changes it meanwhile)
HEFF_FN V heff_share(V v) {
  if (!IS_OBJ(v) || !v) return v;
  uint32_t rc = heff_rc(OBJ(v));
  if (!heff_mine(rc) && !heff_owned(rc)) return v;
  HeffStack s = {0};
  heff_share_one(&s, &v);
  while (s.n) {
    V o = s.v[--s.n];
    HEFF_EACH_SLOT(o, heff_share_one, &s);
  }
  free(s.v);
  return v;
}

// (one slot of what is moved: an object counted once is held through
// this slot alone, and goes on being walked, as it is; one counted more
// is held by something else too, and is shared, with all it holds)
HEFF_FN void heff_move_one(HeffStack *s, V *at) {
  V v = *at;
  if (!IS_OBJ(v) || !v) return;
  uint32_t rc = heff_rc(OBJ(v));
  if (heff_owned(rc)) {
    if (HEFF_COUNT(rc) != 1) { heff_share(v); return; }
    OBJ(v)->rc = rc = 1;
  }
  if (!heff_mine(rc)) return;
  if (rc == 1) heff_stack_push(s, v);
  else heff_share(v);
}

// (`v` handed to one other thread, which holds it instead of this one
// (#125): where this thread holds `v` alone -- counted once, and not
// shared -- it is moved, its count as it is, no mark: the taker counts
// it alone from then on, as its own, and may take it apart or build in
// it in place.  Below it, each object counted once under one so held is
// the same, moved; one counted more than once something else holds too,
// so it is shared (`heff_share`), with all it holds, and the walk goes
// no further there.  A thread's own object may hold shared ones, so
// what is moved keeps the invariant.  Where `v` is not held alone, it
// is shared, as `heff_share` does.  `v` not consumed: the reference
// handed over is the caller's, which must not count it after.  The walk
// is the same as `heff_share`'s, and finds the objects held more than
// once; what it saves is every mark, and the atomic counting after)
HEFF_FN V heff_move(V v) {
  if (!IS_OBJ(v) || !v) return v;
  uint32_t rc = heff_rc(OBJ(v));
  if (heff_owned(rc) && HEFF_COUNT(rc) == 1) OBJ(v)->rc = rc = 1;
  if (heff_owned(rc)) return heff_share(v);
  if (!heff_mine(rc)) return v;
  if (rc != 1) return heff_share(v);
  HeffStack s = {0};
  heff_stack_push(&s, v);
  while (s.n) {
    V o = s.v[--s.n];
    HEFF_EACH_SLOT(o, heff_move_one, &s);
  }
  free(s.v);
  return v;
}

// (one slot of what a cown is given: an object of this thread's counted
// once is held through this slot alone, and is the cown's, marked
// `OWNED`, the walk going on below it; one counted more is held by
// something else too, and is shared, with all it holds.  The walk stops
// at what is owned already: what the body counted up of that its log
// holds (`TOUCHED`), and the provider shares it after where more than
// the cown holds it; what it did not, nothing else holds)
HEFF_FN void heff_own_one(HeffStack *s, V *at) {
  V v = *at;
  if (!IS_OBJ(v) || !v) return;
  uint32_t rc = heff_rc(OBJ(v));
  if (!heff_mine(rc)) return;
  if (rc == 1) {
    OBJ(v)->rc = OWNED | 1;
    heff_stack_push(s, v);
  } else heff_share(v);
}

// (what the slot holds made the cown's, as `heff_own_one` says: a
// cown's objects are held by the one behaviour that holds the cown,
// each counted as a thread's own, and handed on with the cown, by its
// turnstile, never walked again where nothing changed them)
HEFF_FN void heff_own_at(V *at) {
  HeffStack s = {0};
  heff_own_one(&s, at);
  while (s.n) {
    V o = s.v[--s.n];
    HEFF_EACH_SLOT(o, heff_own_one, &s);
  }
  free(s.v);
}
#else
// (one thread: nothing is shared, nothing to do)
static inline V heff_share(V v) { return v; }
static inline V heff_move(V v) { return v; }
static inline void heff_own_at(V *at) { (void)at; }
#endif

// Calls of what is not known
// ---------------------------------------------------------------------

// (the calls last counted, `heff_dep`; and where a lambda's call last of
// more arguments than it took is put, up to `HEFF_ROOM` of them, to be
// made a jump, `heff_room`: its own are where its caller put them, room
// for only as many as it takes -- and what is called reads them at
// once, before it calls anything -- see the C emitter's `roomed`.  With
// threads, each thread's, in its block)
#ifndef HEFF_THREADS
HEFF_VAR(long heff_dep);
HEFF_VAR(V heff_room[HEFF_ROOM]);
#endif

HEFF_FN V heff_apply(V f, int n, V *a);

// (a call's `n` arguments copied, `n` known only where it is run and
// most often a few: stored one by one, not given to `memcpy`, a call that
// costs more than such a copy)
static inline void heff_copy(V *to, const V *from, int64_t n) {
  switch (n) {
  case 4: to[3] = from[3]; /* fall through */
  case 3: to[2] = from[2]; /* fall through */
  case 2: to[1] = from[1]; /* fall through */
  case 1: to[0] = from[0]; /* fall through */
  case 0: return;
  default: memcpy(to, from, n * sizeof(V));
  }
}

// (the bounces run until a value comes: each a chain of calls last
// counted from naught -- and, done, the count of the chain it was called
// in put back, so that a chain calling one in each of its steps still
// comes to its bounce, not ever deeper on the C stack.  A bounce's
// arguments are in an array of the loop's step, not `alloca`'s, which
// would keep each step's until the end.)
HEFF_FN V heff_trs(V r) {
  long outer = heff_dep;
  do {
    Bnc *b = (Bnc *)r;
    heff_dep = 0;
    V fun = b->fun;
    int n = b->n;
    V a[n > 0 ? n : 1];
    heff_copy(a, b->a, n);
    heff_obj_free(b, sizeof(Bnc) + n * sizeof(V));
    r = heff_apply(fun, n, a);
  } while (!IS_INT(r) && !IS_NTAG(r) && OBJ(r)->kind == K_BNC);
  heff_dep = outer;
  return r;
}

static inline V heff_tr(V r) {
  return (!IS_INT(r) && !IS_NTAG(r) && OBJ(r)->kind == K_BNC) ? heff_trs(r) : r;
}

HEFF_FN V heff_bounce(V f, int n, V *a) {
  Bnc *b = heff_obj_alloc(sizeof(Bnc) + n * sizeof(V));
  b->h.rc = 1; b->h.kind = K_BNC; b->h.tag = 0; b->fun = f; b->n = n;
  heff_copy(b->a, a, n);
  return (V)b;
}

// (a closure taking exactly the `n` arguments at `a`, not a thunk forced:
// what `heff_apply` calls at once, as it is)
static inline int heff_called_as(V f, int n, V *a) {
  Clo *c = (Clo *)f;
  return c->h.kind == K_CLO && c->arity == n && !(n == 1 && a[0] == NTAG(TAG_MkUnit));
}

// (a call last: counted, and every so often a bounce; a closure taking
// exactly its arguments called where the call is, as `heff_apply` would
// call it, without the call of it)
static inline V heff_tail(V f, int n, V *a) {
  if (++heff_dep > 500) return heff_bounce(f, n, a);
  if (HEFF_LIKELY(heff_called_as(f, n, a))) return ((Clo *)f)->fn(f, a);
  return heff_apply(f, n, a);
}

#ifdef HEFF_THREADS
// (a thunk forced, threads at once: a shared or immortal one, whose
// memo other threads may read and write meanwhile.  Its value is shared
// (`heff_share`) and then put in the memo, by the first to have it;
// another computing it meanwhile, the language pure, has the same
// value, takes the memo's and lets its own go, freed.  A static thunk is
// immortal, its memo kept for good: the first freezes the value once it
// is there (`heff_freeze`), so that no thread counts it, atomically or
// at all -- a thread that counted it up before then counts it down
// after as nothing, the memo holding it.  A shared thunk's value is
// counted as any shared object is, freed when the thunk and all that
// hold it let it go)
HEFF_FN __attribute__((noinline)) V heff_force_shared(V f, V *a) {
  Clo *c = (Clo *)f;
  V m = __atomic_load_n(&c->memo, __ATOMIC_ACQUIRE);
  if (!m) {
    heff_dup(f);
    V r = heff_share(heff_tr(c->fn(f, a)));
    heff_dup(r);
    if (__atomic_compare_exchange_n(&c->memo, &m, r, 0, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) {
      if (heff_immortal(heff_rc(&c->h))) heff_freeze(r);
      heff_drop(f);
      return r;
    }
    heff_drop(r);
    heff_drop(r);
  }
  heff_dup(m);
  heff_drop(f);
  return m;
}
#endif

HEFF_FN V heff_apply(V f, int n, V *a) {
  for (;;) {
    Obj *o = OBJ(f);
    if (o->kind == K_PAP) {
      // (its arguments before the ones given: taken over where it is
      // held only here, else shared)
      Pap *p = (Pap *)f;
      int pn = p->n, m = pn + n;
      V *all = alloca(m * sizeof(V));
      V fun;
      if (heff_unique(f)) {
        heff_copy(all, p->a, pn);
        fun = p->fun;
        heff_obj_free(p, sizeof(Pap) + pn * sizeof(V));
      } else {
        for (int i = 0; i < pn; i++) all[i] = heff_dup(p->a[i]);
        fun = heff_dup(p->fun);
        heff_drop(f);
      }
      heff_copy(all + pn, a, n);
      f = fun; a = all; n = m;
      continue;
    }
    if (o->kind != K_CLO) heff_fail("applying what is not a function");
    Clo *c = (Clo *)f;
    // (a thunk forced: its value kept on it, so that forcing it again does
    // not compute it again -- the language is pure, `f MkUnit` is the same
    // value every time -- as the JavaScript backend's `$force` keeps it)
    if (n == 1 && c->arity == 1 && a[0] == NTAG(TAG_MkUnit)) {
#ifdef HEFF_THREADS
      if (!heff_mine(heff_rc(&c->h))) return heff_force_shared(f, a);
#endif
      if (c->memo) {
        V r = heff_dup(c->memo);
        heff_drop(f);
        return r;
      }
      if (heff_unique(f)) return c->fn(f, a);
      heff_dup(f);
      V r = heff_tr(c->fn(f, a));
      c->memo = heff_dup(r);
      heff_drop(f);
      return r;
    }
    if (n == c->arity) return c->fn(f, a);
    if (n < c->arity) {
      Pap *p = heff_obj_alloc(sizeof(Pap) + n * sizeof(V));
      p->h.rc = 1; p->h.kind = K_PAP; p->h.tag = 0; p->fun = f; p->n = n;
      heff_copy(p->a, a, n);
      return (V)p;
    }
    // (more arguments than it takes: the rest given to what it gives --
    // its arity read first, the closure consumed by the call; the rest
    // kept apart first, as they may be in `heff_room`, which the call
    // may put others in)
    int ar = c->arity, rest = n - ar;
    V *more = alloca(rest * sizeof(V));
    heff_copy(more, a + ar, rest);
    V r = heff_tr(c->fn(f, a));
    f = r; a = more; n = rest;
  }
}

static inline V heff_app1(V f, V x) {
  if (HEFF_LIKELY(heff_called_as(f, 1, &x))) return ((Clo *)f)->fn(f, &x);
  return heff_apply(f, 1, &x);
}

// (a call not last of an unknown function: a closure taking exactly the
// arguments given, and not a thunk forced, called at once, where the
// call is -- what `heff_apply` would call, without the call of it;
// anything else through it)
HEFF_FAST V heff_call(V f, int n, V *a) {
  Clo *c = (Clo *)f;
  if (c->h.kind == K_CLO && c->arity == n && !(n == 1 && a[0] == NTAG(TAG_MkUnit)))
    return c->fn(f, a);
  return heff_apply(f, n, a);
}

// (whether `f`, given the `n` arguments at `a`, is a closure taking
// exactly them and not a thunk forced -- what `heff_apply` would call at
// once, as it is -- and a call last of it a jump: a lambda's call last
// of it is then not counted (the emitter's `inPlace`))
static inline int heff_exact(V f, int n, V *a) {
  return HEFF_JUMPS && IS_OBJ(f) && OBJ(f)->kind == K_CLO
      && ((Clo *)f)->arity == n && !(n == 1 && a[0] == NTAG(TAG_MkUnit));
}

// Definitions' values
// ---------------------------------------------------------------------
// A definition that is no function is computed when it is first asked
// for, and kept (the emitter's `valDef`): its value
// `g_X_val`, its state `g_X_st` (`HEFF_ONCE`), asked for by `g_X_get`,
// which has it at once where it is computed (`HEFF_DONE`), and otherwise
// asks `heff_global` to compute it by `g_X_init`.  One thread: the state
// 0, then 1 while it is computed -- asked for again then, it is defined
// by itself -- then 2.  Threads (`HEFF_THREADS`): computed once, by the
// first thread to ask, the others asking meanwhile waiting for it, and
// made immortal (`heff_freeze`), so that every thread has the same value
// and none counts it; while it is computed, its state is the thread
// computing it (`heff_me`'s address), so that a thread asking for what
// it is computing itself is told it is defined by itself, not left to
// wait.  (Definitions are in order, none using one after it: a thread
// computing one waits only for one before it, never for one waiting for
// it.)  A failure caught (`heff_try`) where values were being computed
// leaves them to be computed again.
#ifdef HEFF_THREADS
#define HEFF_ONCE uintptr_t
#define HEFF_DONE(st) HEFF_LIKELY(__atomic_load_n(&(st), __ATOMIC_ACQUIRE) == 2)
#ifdef HEFF_PART
extern pthread_mutex_t heff_once_mu;
extern pthread_cond_t heff_once_cv;
#else
pthread_mutex_t heff_once_mu = PTHREAD_MUTEX_INITIALIZER;
pthread_cond_t heff_once_cv = PTHREAD_COND_INITIALIZER;
#endif
HEFF_VAR(HEFF_TLS char heff_me);
// (the states of what this thread is computing, the last innermost)
HEFF_VAR(HEFF_TLS HEFF_ONCE **heff_open);
HEFF_VAR(HEFF_TLS size_t heff_nopen);
HEFF_VAR(HEFF_TLS size_t heff_capopen);

HEFF_FN __attribute__((noinline)) V heff_global(V *val, HEFF_ONCE *st, V (*init)(void)) {
  uintptr_t me = (uintptr_t)&heff_me;
  // (room for its state among the open first: from its being marked
  // until it is done, it is among them, a failure anywhere between --
  // even a stack's overflow -- leaving it to be computed again)
  if (heff_nopen == heff_capopen) {
    heff_capopen = heff_capopen ? heff_capopen * 2 : 16;
    heff_open = realloc(heff_open, heff_capopen * sizeof(HEFF_ONCE *));
    if (!heff_open) heff_fail("out of memory");
  }
  pthread_mutex_lock(&heff_once_mu);
  for (;;) {
    uintptr_t s = __atomic_load_n(st, __ATOMIC_ACQUIRE);
    if (s == 2) { pthread_mutex_unlock(&heff_once_mu); return *val; }
    if (s == me) { pthread_mutex_unlock(&heff_once_mu); heff_fail("defined by itself"); }
    if (s == 0) break;
    pthread_cond_wait(&heff_once_cv, &heff_once_mu);
  }
  __atomic_store_n(st, me, __ATOMIC_RELAXED);
  heff_open[heff_nopen++] = st;
  pthread_mutex_unlock(&heff_once_mu);
  V v = heff_tr(init());
  heff_freeze(v);
  pthread_mutex_lock(&heff_once_mu);
  *val = v;
  __atomic_store_n(st, 2, __ATOMIC_RELEASE);
  heff_nopen--;
  pthread_cond_broadcast(&heff_once_cv);
  pthread_mutex_unlock(&heff_once_mu);
  return v;
}

// (what this thread was computing when a failure was caught, from the
// `base`th on, to be computed again: the threads waiting for it woken)
HEFF_FN void heff_reopen(size_t base) {
  if (heff_nopen <= base) return;
  pthread_mutex_lock(&heff_once_mu);
  while (heff_nopen > base) __atomic_store_n(heff_open[--heff_nopen], 0, __ATOMIC_RELAXED);
  pthread_cond_broadcast(&heff_once_cv);
  pthread_mutex_unlock(&heff_once_mu);
}
#else
#define HEFF_ONCE int
#define HEFF_DONE(st) HEFF_LIKELY((st) == 2)

// (the states of what is being computed, the last innermost)
HEFF_VAR(HEFF_ONCE **heff_open);
HEFF_VAR(size_t heff_nopen);
HEFF_VAR(size_t heff_capopen);

HEFF_FN __attribute__((noinline)) V heff_global(V *val, HEFF_ONCE *st, V (*init)(void)) {
  if (*st == 1) heff_fail("defined by itself");
  if (heff_nopen == heff_capopen) {
    heff_capopen = heff_capopen ? heff_capopen * 2 : 16;
    heff_open = realloc(heff_open, heff_capopen * sizeof(HEFF_ONCE *));
    if (!heff_open) heff_fail("out of memory");
  }
  *st = 1;
  heff_open[heff_nopen++] = st;
  *val = heff_tr(init());
  heff_nopen--;
  *st = 2;
  return *val;
}

// (what was being computed when a failure was caught, from the `base`th
// on, to be computed again)
HEFF_FN void heff_reopen(size_t base) {
  while (heff_nopen > base) *heff_open[--heff_nopen] = 0;
}
#endif

// Integers
// ---------------------------------------------------------------------
// An integer is a word while it fits in 62 bits and a sign (`MK_INT`,
// from -2^62 up to 2^62); beyond, a big one (`K_BIG`): its sign and its
// magnitude's 64-bit digits, the least first.  Each result fitting in a
// word is one, so that two equal integers are both words or both big.

// (an integer's sign and digits, to compute with: a word's in `buf`)
typedef struct { int neg; int n; const uint64_t *d; uint64_t buf[1]; } Num;

HEFF_FN void num_of(V v, Num *x) {
  if (IS_INT(v)) {
    int64_t i = INT_OF(v);
    x->neg = i < 0;
    x->buf[0] = i < 0 ? (uint64_t)0 - (uint64_t)i : (uint64_t)i;
    x->n = x->buf[0] != 0;
    x->d = x->buf;
  } else {
    Big *b = (Big *)v;
    x->neg = b->neg; x->n = b->n; x->d = b->d;
  }
}

// (a big one's bytes, of `n` digits)
#define BIG_BYTES(n) (sizeof(Big) + (size_t)(n) * sizeof(uint64_t))

// (room for `n` digits, a result written into it where it is computed,
// then made an integer by `big_fin`: nothing copied)
static inline Big *big_new(int64_t n) {
  if (n > INT32_MAX) heff_fail("out of memory");
  Big *b = heff_obj_alloc(BIG_BYTES(n));
  b->h.rc = 1; b->h.kind = K_BIG; b->h.tag = 0; b->neg = 0; b->n = (int32_t)n;
  return b;
}

// (the first `n` digits of `b`'s room as an integer: a word if they
// fit, `b` given back; else `b`, its top zeros dropped -- moved to an
// object of its size where that is another of the sizes kept apart, so
// that it is given back as the size it was made)
HEFF_FN V big_fin(Big *b, int neg, int n) {
  int cap = b->n;
  while (n > 0 && b->d[n - 1] == 0) n--;
  if (n <= 1) {
    uint64_t m = n == 0 ? 0 : b->d[0];
    if (m < (uint64_t)INT_LIM || (neg && m == (uint64_t)INT_LIM)) {
      heff_obj_free(b, BIG_BYTES(cap));
      return MK_INT(neg ? (int64_t)((uint64_t)0 - m) : (int64_t)m);
    }
  }
  size_t was = (BIG_BYTES(cap) + 7) / 8, now = (BIG_BYTES(n) + 7) / 8;
  if (now != was && (now <= SMALL_MAX / 8 || was <= SMALL_MAX / 8)) {
    Big *c = big_new(n);
    memcpy(c->d, b->d, (size_t)n * sizeof(uint64_t));
    heff_obj_free(b, BIG_BYTES(cap));
    b = c;
  }
  b->neg = neg; b->n = n;
  return (V)b;
}

HEFF_SLOW V heff_int_big(int64_t i) {
  Big *b = big_new(1);
  b->d[0] = i < 0 ? (uint64_t)0 - (uint64_t)i : (uint64_t)i;
  return big_fin(b, i < 0, 1);
}

HEFF_FAST V heff_int(int64_t i) {
  if (HEFF_LIKELY(i >= -INT_LIM && i < INT_LIM)) return MK_INT(i);
  return heff_int_big(i);
}

// (magnitudes compared, added, subtracted, multiplied and divided by
// the runtime's Zig, `heff_mag_*`: each result's room, and the integer
// made of it, here)
// (a + b, signed)
HEFF_FN V num_add(const Num *a, int bneg, const Num *b) {
  if (a->neg == bneg) {
    Big *o = big_new((a->n > b->n ? a->n : b->n) + 1);
    return big_fin(o, a->neg, heff_mag_add(a->d, a->n, b->d, b->n, o->d));
  }
  if (heff_mag_cmp(a->d, a->n, b->d, b->n) >= 0) {
    Big *o = big_new(a->n);
    return big_fin(o, a->neg, heff_mag_sub(a->d, a->n, b->d, b->n, o->d));
  }
  Big *o = big_new(b->n);
  return big_fin(o, bneg, heff_mag_sub(b->d, b->n, a->d, a->n, o->d));
}

// (a divided by b, rounded down, as the other backends round: the
// quotient, or the remainder (b's sign) -- the one wanted written into
// the integer made, the other on the stack)
HEFF_FN V num_divmod(const Num *a, const Num *b, int want_mod) {
  int qn = a->n - b->n + 1 > 0 ? a->n - b->n + 1 : 1;
  uint64_t *vn = alloca(b->n * sizeof(uint64_t)), *un = alloca((a->n + 1) * sizeof(uint64_t));
  if (want_mod) {
    uint64_t *q = alloca(qn * sizeof(uint64_t));
    Big *r = big_new(b->n);
    heff_mag_divmod(a->d, a->n, b->d, b->n, q, r->d, vn, un);
    int rn = b->n;
    while (rn > 0 && r->d[rn - 1] == 0) rn--;
    if (!(rn > 0 && a->neg != b->neg)) return big_fin(r, a->neg, rn);
    return big_fin(r, b->neg, heff_mag_sub(b->d, b->n, r->d, rn, r->d));
  }
  uint64_t *r = alloca(b->n * sizeof(uint64_t));
  Big *q = big_new(qn + 1);
  heff_mag_divmod(a->d, a->n, b->d, b->n, q->d, r, vn, un);
  int rn = b->n;
  while (rn > 0 && r[rn - 1] == 0) rn--;
  if (!(rn > 0 && a->neg != b->neg)) return big_fin(q, a->neg != b->neg, qn);
  uint64_t one = 1;
  return big_fin(q, 1, heff_mag_add(q->d, qn, &one, 1, q->d));
}

HEFF_FN V num_mul(const Num *a, const Num *b) {
  int n = a->n + b->n;
  Big *o = big_new(n);
  heff_mag_mul(a->d, a->n, b->d, b->n, o->d);
  return big_fin(o, a->neg != b->neg, n);
}

HEFF_FN int num_cmp(const Num *a, const Num *b) {
  if (a->neg != b->neg) return a->neg ? -1 : 1;
  int c = heff_mag_cmp(a->d, a->n, b->d, b->n);
  return a->neg ? -c : c;
}

// (bench's `keep`: the value as it is, but what it is hidden from the C
// compiler -- an empty instruction it must keep, and that it must take
// to read the value and the memory it points to, and may have changed
// the value -- so that neither the work it is the result of is dropped
// nor that made of it computed once, out of a loop: no instruction at
// all, as Rust's `black_box`)
static inline V heff_keep(V x) {
  __asm__ volatile("" : "+r"(x) : : "memory");
  return x;
}

// An integer's operation (`heff_intAdd` and the others) is inlined
// where it is used, as far as both are words and so is what it makes:
// there it is done on the words as they are, `2x + 1` each -- their
// sum less one is `2(x + y) + 1`, and the machine's overflow of it is
// exactly a sum beyond a word's -- with no call, no frame, nothing to
// drop.  Anything else, a big one or a result beyond a word, is
// `NAME_big`'s, a call: the operation on the integers' digits (`Num`),
// both consumed.
#define INT_BIG(T, name, big)                                           \
  HEFF_SLOW T name##_big(V a, V b) {                                    \
    Num x, y;                                                           \
    num_of(a, &x);                                                      \
    num_of(b, &y);                                                      \
    T r = big;                                                          \
    heff_drop(a);                                                       \
    heff_drop(b);                                                       \
    return r;                                                           \
  }

// (both words: tested at once, their low bits)
#define BOTH_INT(a, b) HEFF_LIKELY(IS_INT((a) & (b)))

// (a word made of two: its low bit set, as the C compiler is told, so
// that an operation on it next tests it no more -- `(x + y) % m` tests
// `x` and `y` once)
static inline __attribute__((always_inline)) V heff_word_made(int64_t r) {
#if defined(__has_builtin)
#if __has_builtin(__builtin_assume)
  __builtin_assume((r & 1) == 1);
#endif
#endif
  return (V)r;
}

INT_BIG(V, heff_intAdd, num_add(&x, y.neg, &y))
HEFF_FAST V heff_intAdd(V a, V b) {
  int64_t r;
  if (BOTH_INT(a, b) && !__builtin_add_overflow((int64_t)a, (int64_t)b - 1, &r)) return heff_word_made(r);
  return heff_intAdd_big(a, b);
}

// (`2x + 1 - 2y`)
INT_BIG(V, heff_intSub, num_add(&x, !y.neg && y.n > 0, &y))
HEFF_FAST V heff_intSub(V a, V b) {
  int64_t r;
  if (BOTH_INT(a, b) && !__builtin_sub_overflow((int64_t)a, (int64_t)b - 1, &r)) return heff_word_made(r);
  return heff_intSub_big(a, b);
}

// (`2x * y`, then its low bit set)
INT_BIG(V, heff_intMul, num_mul(&x, &y))
HEFF_FAST V heff_intMul(V a, V b) {
  int64_t r;
  if (BOTH_INT(a, b) && !__builtin_mul_overflow((int64_t)a - 1, INT_OF(b), &r)) return (V)r | 1;
  return heff_intMul_big(a, b);
}

// (rounded down, as the other backends round; by 0, 0 -- a division is
// total -- which the call gives.  Of two words only -2^62 / -1 is beyond
// a word)
INT_BIG(V, heff_intDiv, y.n == 0 ? MK_INT(0) : num_divmod(&x, &y, 0))
HEFF_FAST V heff_intDiv(V a, V b) {
  if (BOTH_INT(a, b) && b != MK_INT(0)) {
    int64_t x = INT_OF(a), y = INT_OF(b), q = x / y, r = x % y;
    if (r != 0 && ((r < 0) != (y < 0))) q -= 1;
    if (HEFF_LIKELY(q < INT_LIM)) return MK_INT(q);
  }
  return heff_intDiv_big(a, b);
}

// (of the divisor's sign, and nearer 0 than it: a word; by 0, the
// dividend, which the call gives -- `(a / b) * b + a % b` is `a` still)
INT_BIG(V, heff_intMod, y.n == 0 ? heff_dup(a) : num_divmod(&x, &y, 1))
HEFF_FAST V heff_intMod(V a, V b) {
  if (BOTH_INT(a, b) && b != MK_INT(0)) {
    int64_t y = INT_OF(b), r = INT_OF(a) % y;
    if (r != 0 && ((r < 0) != (y < 0))) r += y;
    return MK_INT(r);
  }
  return heff_intMod_big(a, b);
}

// (each given also a mask of the operands given it, the others lent, as
// a comparison is: two words' operation takes nothing, and only where
// one is big is what is lent counted, for `NAME_big` to consume)
#define INT_LENT(name)                                                  \
  HEFF_FAST V name##_lent(V a, V b, int give) {                         \
    if (BOTH_INT(a, b)) return name(a, b);                              \
    return name##_big(give & 1 ? a : heff_dup(a),                       \
                      give & 2 ? b : heff_dup(b));                      \
  }
INT_LENT(heff_intAdd)
INT_LENT(heff_intSub)
INT_LENT(heff_intMul)
INT_LENT(heff_intDiv)
INT_LENT(heff_intMod)

// A comparison, as C's condition (`heff_intLt_c`, what the emitter
// tests where its Bool is only looked at) and as its Bool, each also
// given a mask of the operands given it, the others lent (`_lent`, as a
// string's comparison is).  Words are
// in the order of their integers, and equal as they are; a word and a
// big one are never equal.
#define INT_CMP(name, op, cmp)                                          \
  INT_BIG(int, name##_c, num_cmp(&x, &y) cmp)                           \
  HEFF_FAST int name##_c(V a, V b) {                                    \
    if (BOTH_INT(a, b)) return (int64_t)a op (int64_t)b;                \
    return name##_c_big(a, b);                                          \
  }                                                                     \
  HEFF_FAST V name(V a, V b) { return heff_bool(name##_c(a, b)); }     \
  HEFF_FAST int name##_c_lent(V a, V b, int give) {                     \
    if (BOTH_INT(a, b)) return (int64_t)a op (int64_t)b;                \
    return name##_c_big(give & 1 ? a : heff_dup(a),                     \
                        give & 2 ? b : heff_dup(b));                    \
  }                                                                     \
  HEFF_FAST V name##_lent(V a, V b, int give) {                         \
    return heff_bool(name##_c_lent(a, b, give));                        \
  }
INT_CMP(heff_intEq, ==, == 0)
INT_CMP(heff_intLt, <, < 0)
INT_CMP(heff_intLe, <=, <= 0)

// An integer's bits are as two's complement has them, its sign extended
// for ever (Python's): two words' operation is the words', a big one's
// done on as many 64-bit words as the longer has, and one more for the
// sign.

// (`x` as `n` words of two's complement, the least first)
HEFF_FN void num_twos(const Num *x, uint64_t *t, int n) {
  int carry = 1;
  for (int i = 0; i < n; i++) {
    uint64_t w = i < x->n ? x->d[i] : 0;
    if (x->neg) {
      t[i] = ~w + (uint64_t)carry;
      carry = carry && t[i] == 0;
    } else t[i] = w;
  }
}

// (`n` words of two's complement, written in `b`'s room, as an integer)
HEFF_FN V twos_fin(Big *b, int n) {
  uint64_t *t = b->d;
  int neg = (int)(t[n - 1] >> 63);
  if (neg) {
    int carry = 1;
    for (int i = 0; i < n; i++) {
      t[i] = ~t[i] + (uint64_t)carry;
      carry = carry && t[i] == 0;
    }
  }
  return big_fin(b, neg, n);
}

// (as the sum is: both words, inlined -- the words' operation on `2x + 1`
// and `2y + 1` is `2(x op y) + 1`'s, the low bit set again after `^` --
// else a call, on as many 64-bit words as the longer has, and one more
// for the sign)
#define INT_BITS(name, op)                                                  \
  HEFF_SLOW V name##_big(V a, V b) {                                        \
    Num x, y;                                                               \
    num_of(a, &x);                                                          \
    num_of(b, &y);                                                          \
    int n = (x.n > y.n ? x.n : y.n) + 1;                                    \
    Big *s = big_new(n);                                                    \
    uint64_t *t = alloca(n * sizeof(uint64_t));                             \
    num_twos(&x, s->d, n);                                                  \
    num_twos(&y, t, n);                                                     \
    for (int i = 0; i < n; i++) s->d[i] = s->d[i] op t[i];                  \
    V r = twos_fin(s, n);                                                   \
    heff_drop(a);                                                           \
    heff_drop(b);                                                           \
    return r;                                                               \
  }                                                                         \
  HEFF_FAST V name(V a, V b) {                                              \
    if (BOTH_INT(a, b)) return (a op b) | 1;                                \
    return name##_big(a, b);                                                \
  }
INT_BITS(heff_intAnd, &)
INT_BITS(heff_intOr, |)
INT_BITS(heff_intXor, ^)

HEFF_FN int heff_int_neg(V v) { return IS_INT(v) ? INT_OF(v) < 0 : ((Big *)v)->neg; }

HEFF_SLOW V heff_intShr_big(V a, V b);

// (`a` times 2^`b`; by a negative count, a shift right by its size; one
// beyond memory fails)
HEFF_SLOW V heff_intShl_big(V a, V b) {
  if (heff_int_neg(b)) return heff_intShr_big(a, heff_intSub(MK_INT(0), b));
  int bbig = !IS_INT(b);
  heff_drop(b);
  if (IS_INT(a) && INT_OF(a) == 0) return a;
  if (bbig) heff_fail("a shift beyond memory");
  int64_t k = INT_OF(b);
  if (IS_INT(a) && k < 62) {
    __int128 r = (__int128)INT_OF(a) * ((__int128)1 << k);
    if (r < INT_LIM && r >= -INT_LIM) return MK_INT((int64_t)r);
  }
  Num x;
  num_of(a, &x);
  int64_t w = k / 64, s = k % 64, n = x.n + w + 1;
  Big *ob = big_new(n);
  uint64_t *o = ob->d;
  memset(o, 0, w * sizeof(uint64_t));
  o[x.n + w] = 0;
  for (int i = 0; i < x.n; i++) o[i + w] = s ? x.d[i] << s | (i ? x.d[i - 1] >> (64 - s) : 0) : x.d[i];
  if (s) o[x.n + w] = x.d[x.n - 1] >> (64 - s);
  V r = big_fin(ob, x.neg, (int)n);
  heff_drop(a);
  return r;
}

// (a word by a count from 0 below 62 to a word, inlined: `x << k` is one
// where shifting it back gives `x`, and `2x + 1`'s bits shifted so, the
// low bit set again, are its; else the call)
HEFF_FAST V heff_intShl(V a, V b) {
  if (BOTH_INT(a, b) && b < MK_INT(62)) {
    int64_t k = INT_OF(b), x = (int64_t)a - 1, r = (int64_t)((uint64_t)x << k);
    if ((r >> k) == x) return (V)r | 1;
  }
  return heff_intShl_big(a, b);
}

// (`a` divided by 2^`b`, rounding down: its bits shifted out, the sign
// shifted in; by a negative count, a shift left by its size)
HEFF_SLOW V heff_intShr_big(V a, V b) {
  if (heff_int_neg(b)) return heff_intShl_big(a, heff_intSub(MK_INT(0), b));
  int bbig = !IS_INT(b);
  heff_drop(b);
  int aneg = heff_int_neg(a);
  if (bbig) { heff_drop(a); return MK_INT(aneg ? -1 : 0); }
  int64_t k = INT_OF(b);
  if (IS_INT(a)) return MK_INT(k >= 63 ? (aneg ? -1 : 0) : INT_OF(a) >> k);
  Num x;
  num_of(a, &x);
  int64_t w = k / 64, s = k % 64;
  if (w >= x.n) { heff_drop(a); return MK_INT(aneg ? -1 : 0); }
  int n = x.n - (int)w;
  Big *ob = big_new(n + 1);
  uint64_t *o = ob->d;
  for (int i = 0; i < n; i++) {
    uint64_t hi = i + w + 1 < x.n ? x.d[i + w + 1] : 0;
    o[i] = s ? x.d[i + w] >> s | hi << (64 - s) : x.d[i + w];
  }
  o[n] = 0;
  // (a negative one rounds down: its magnitude up, where a bit set was
  // shifted out)
  int lost = s && (x.d[w] & (((uint64_t)1 << s) - 1));
  for (int64_t i = 0; i < w && !lost; i++) lost = x.d[i] != 0;
  if (x.neg && lost)
    for (int i = 0; i <= n && ++o[i] == 0; i++) {}
  V r = big_fin(ob, x.neg, n + 1);
  heff_drop(a);
  return r;
}

// (a word by a count from 0 to a word, inlined: its bits shifted out, the
// sign shifted in -- by 63 or more, all of them; `2x + 1`'s, the low bit
// set again; else the call)
HEFF_FAST V heff_intShr(V a, V b) {
  if (BOTH_INT(a, b) && (int64_t)b >= 0) {
    int64_t k = INT_OF(b);
    return (V)((int64_t)a >> (k < 63 ? k : 63)) | 1;
  }
  return heff_intShr_big(a, b);
}

// (a word's decimal digits, a '-' before a negative one, written
// backwards to `end`: where they start, 20 bytes at most before it)
static inline char *heff_word_digits(int64_t k, char *end) {
  uint64_t u = k < 0 ? (uint64_t)0 - (uint64_t)k : (uint64_t)k;
  do { *--end = (char)('0' + u % 10); u /= 10; } while (u);
  if (k < 0) *--end = '-';
  return end;
}

// (an integer's decimal digits, a '-' before a negative one: malloc'd.
// Its magnitude divided by 10^19 again and again, in place, each
// remainder 19 of them -- a 64-bit digit has 20 at most)
HEFF_FN char *heff_int_cstr(V v) {
  Num x;
  num_of(v, &x);
  uint64_t *m = alloca((x.n + 1) * sizeof(uint64_t));
  memcpy(m, x.d, x.n * sizeof(uint64_t));
  int n = x.n;
  size_t cap = (size_t)n * 20 + 3, at = cap;
  char *c = heff_alloc(cap);
  c[--at] = 0;
  do {
    uint64_t k = heff_mag_div1(m, n, 10000000000000000000u, m);
    while (n > 0 && m[n - 1] == 0) n--;
    for (int i = 0; i < 19 && (n > 0 || k > 0 || i == 0); i++) {
      c[--at] = (char)('0' + k % 10);
      k /= 10;
    }
  } while (n > 0);
  if (x.neg) c[--at] = '-';
  memmove(c, c + at, cap - at);
  return c;
}

// (an integer written in the program, beyond a word: made once, kept)
HEFF_FN V heff_big_lit(const char *s) {
  int neg = *s == '-';
  if (neg) s++;
  size_t len = strlen(s);
  int n = 0;
  Big *b = big_new((int64_t)(len / 19) + 2);
  uint64_t *d = b->d;
  for (size_t i = 0; i < len;) {
    uint64_t chunk = 0, scale = 1;
    for (int k = 0; k < 19 && i < len; k++, i++) { chunk = chunk * 10 + (uint64_t)(s[i] - '0'); scale *= 10; }
    uint64_t c = chunk;
    for (int j = 0; j < n; j++) {
      unsigned __int128 t = (unsigned __int128)d[j] * scale + c;
      d[j] = (uint64_t)t;
      c = (uint64_t)(t >> 64);
    }
    if (c) d[n++] = c;
  }
  V v = big_fin(b, neg, n);
  if (IS_OBJ(v)) OBJ(v)->rc = IMMORTAL;
  return v;
}
#ifdef HEFF_THREADS
// (threads at once: made by the first to have it, kept; another making
// it meanwhile lets its own go, freed -- no other has seen it)
#define HEFF_BIG(s) ({                                                      \
  static V heff_lit_;                                                       \
  V l_ = __atomic_load_n(&heff_lit_, __ATOMIC_ACQUIRE);                     \
  if (!l_) {                                                                \
    V none_ = 0;                                                            \
    l_ = heff_big_lit(s);                                                   \
    if (!__atomic_compare_exchange_n(&heff_lit_, &none_, l_, 0,             \
                                     __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) { \
      if (IS_OBJ(l_)) heff_obj_free((void *)l_, heff_size(l_));             \
      l_ = none_;                                                           \
    }                                                                       \
  }                                                                         \
  l_; })
#else
#define HEFF_BIG(s) ({ static V heff_lit_; heff_lit_ ? heff_lit_ : (heff_lit_ = heff_big_lit(s)); })
#endif

// (a float's integer part, beyond a word if it must be: a word's
// inlined, a big one's the call)
HEFF_SLOW V heff_int_of_double_big(double f) {
  int e;
  double fr = frexp(fabs(f), &e);
  uint64_t mant = (uint64_t)ldexp(fr, 53);
  int sh = e - 53, w = sh / 64, b = sh % 64;
  Big *o = big_new(w + 2);
  memset(o->d, 0, w * sizeof(uint64_t));
  unsigned __int128 x = (unsigned __int128)mant << b;
  o->d[w] = (uint64_t)x;
  o->d[w + 1] = (uint64_t)(x >> 64);
  return big_fin(o, f < 0, w + 2);
}

HEFF_FAST V heff_int_of_double(double f) {
  if (HEFF_LIKELY(f < (double)INT_LIM && f >= -(double)INT_LIM)) return MK_INT((int64_t)f);
  return heff_int_of_double_big(f);
}

// (an integer as the nearest float: a word's inlined, a big one's by its
// digits, the call)
HEFF_SLOW double heff_double_of_big(V v) {
  char *c = heff_int_cstr(v);
  double d = strtod(c, NULL);
  free(c);
  return d;
}

HEFF_FAST double heff_double_of_int(V v) {
  if (HEFF_LIKELY(IS_INT(v))) return (double)INT_OF(v);
  return heff_double_of_big(v);
}

// Strings
// ---------------------------------------------------------------------

HEFF_FN Str *heff_str_new(int64_t len) {
  Str *s = heff_obj_alloc(sizeof(Str) + len);
  s->h.rc = 1; s->h.kind = K_STR; s->h.tag = 0; s->len = len; s->cap = (len + 7) & ~(int64_t)7;
  s->p = s->s;
  return s;
}

HEFF_FN V heff_str_ascii(const char *c) {
  int64_t n = (int64_t)strlen(c);
  Str *s = heff_str_new(n);
  if (n) memcpy(s->s, c, (size_t)n);
  return (V)s;
}

// (`n` bytes, as they are.  The runtime's own: a provider builds a
// string by what it crosses as, "What providers share")
HEFF_FN V heff_str_of(const void *c, int64_t n) {
  Str *s = heff_str_new(n);
  if (n) memcpy(s->s, c, (size_t)n);
  return (V)s;
}

// (whether the `w` bytes from `p`, read as `u`, are a rune's: not U+FFFD
// read for what is not UTF-8)
static inline int heff_u8_own(const uint8_t *p, uint32_t u, int w) {
  return u != 0xFFFD || (w == 3 && p[0] == 0xEF && p[1] == 0xBF && p[2] == 0xBD);
}

// (`n` bytes, made text: what is not UTF-8 in them U+FFFD, as
// TextDecoder reads them -- as they are, where they are UTF-8)
HEFF_FN V heff_str_valid(const void *c, int64_t n) {
  const uint8_t *p = c;
  int own;
  int64_t m = heff_u8_valid_len(p, n, &own);
  if (own) return heff_str_of(c, n);
  Str *s = heff_str_new(m);
  int64_t k = 0;
  for (int64_t i = 0; i < n;) {
    uint32_t u;
    int w = heff_u8_decode(p + i, n - i, &u);
    if (heff_u8_own(p + i, u, w)) { memcpy(s->s + k, p + i, (size_t)w); k += w; }
    else k += heff_u8_encode(s->s + k, 0xFFFD);
    i += w;
  }
  return (V)s;
}

// A string's room.  One made has room for its bytes, and no more than
// the allocator's rounding to 8 gives it: what is made once and kept --
// a map's key, a field -- takes what it needs.  Only a string grown in
// place, its last reference appended to, is given more, and only where
// that is cheap: while it is a small object (`SMALL_MAX`), it grows to
// what it needs, rounded so, each time a copy of at most so many bytes;
// beyond, to twice its room (or what it needs, if more), by `realloc`,
// which extends it where it is where it can -- so a string built a piece
// at a time is copied a logarithmic number of times, not once a piece,
// and the room not yet written in a large block is the system's pages
// not yet touched, not memory.

// (the string `x`, its last reference and not a view, room for `n` bytes
// made in it: the string, moved where it must be)
HEFF_FN Str *heff_str_grow(Str *x, int64_t n) {
  size_t was = (sizeof(Str) + x->cap + 7) / 8 * 8;
  size_t room = (sizeof(Str) + n + 7) / 8 * 8;
  Str *g;
  if (room > SMALL_MAX) {
    size_t twice = (sizeof(Str) + 2 * x->cap + 7) / 8 * 8;
    if (twice > room) room = twice;
  }
  if (was > SMALL_MAX) {
    // (from `malloc`, the allocator's own beyond `SMALL_MAX`)
    HEFF_COUNTED(room / 8);
    g = realloc(x, room);
    if (!g) heff_fail("out of memory");
  } else {
    // (from the allocator objects are given back to, rounded as it
    // rounds: a block it frees to a free list must be the whole of
    // that list's size)
    g = heff_obj_alloc(room);
    memcpy(g, x, sizeof(Str) + x->len);
    heff_obj_free(x, was);
  }
  g->cap = (int64_t)(room - sizeof(Str));
  g->p = g->s;
  return g;
}

// (`n` bytes, at most 64, from `q` to `p`, apart, by no call: a string
// grown in place grows by a byte or a few, most often -- a byte of
// `fromByte`, a digit, a rune, a copy back in an inflated stream -- and
// a call to `memcpy` for each was much of what that cost.  Below 8, a
// byte at a time, as cases, which a compiler does not turn back into the
// call as it would a loop; from 8, two copies of a fixed size, the second
// ending where the bytes end, overlapping the first: a fixed size is
// copied by loads and stores where it is)
HEFF_FAST void heff_copy_short(uint8_t *p, const uint8_t *q, int64_t n) {
  if (n < 8) {
    switch (n) {
    case 7: p[6] = q[6]; __attribute__((fallthrough));
    case 6: p[5] = q[5]; __attribute__((fallthrough));
    case 5: p[4] = q[4]; __attribute__((fallthrough));
    case 4: p[3] = q[3]; __attribute__((fallthrough));
    case 3: p[2] = q[2]; __attribute__((fallthrough));
    case 2: p[1] = q[1]; __attribute__((fallthrough));
    case 1: p[0] = q[0]; __attribute__((fallthrough));
    default: break;
    }
  } else if (n < 16) {
    memcpy(p, q, 8);
    memcpy(p + n - 8, q + n - 8, 8);
  } else if (n < 32) {
    memcpy(p, q, 16);
    memcpy(p + n - 16, q + n - 16, 16);
  } else {
    memcpy(p, q, 32);
    memcpy(p + n - 32, q + n - 32, 32);
  }
}

// (the first string, its last reference and not a view, grown in place,
// as above; `Bytes` too, a new one of the kind `kind`)
HEFF_FN V heff_buf_append(V a, V b, uint16_t kind) {
  Str *x = (Str *)a, *y = (Str *)b;
  int64_t n = x->len + y->len;
  // (a view has no room: its `len` is more than its `cap`, so that where
  // there is room it is no view, and that is not looked at)
  if (heff_alone(&x->h) && (n <= x->cap || !HEFF_STR_VIEW(x))) {
    if (n > x->cap) {
      if (x->len == 0 && y->h.kind == kind) { heff_drop(a); return b; }
      x = heff_str_grow(x, n);
    }
    if (y->len <= 64) heff_copy_short(x->s + x->len, y->p, y->len);
    else memcpy(x->s + x->len, y->p, (size_t)y->len);
    x->len = n;
    heff_drop(b);
    return (V)x;
  }
  // (to nothing, or nothing to it, where a string would be made: the one
  // that is something, as it is, where it is of the kind wanted -- a
  // view is a string's)
  if (y->len == 0 && x->h.kind == kind) { heff_drop(b); return a; }
  if (x->len == 0 && y->h.kind == kind) { heff_drop(a); return b; }
  Str *s = heff_str_new(n);
  s->h.kind = kind;
  memcpy(s->s, x->p, (size_t)x->len);
  memcpy(s->s + x->len, y->p, (size_t)y->len);
  heff_drop(a);
  heff_drop(b);
  return (V)s;
}

HEFF_FN V heff_strAppend(V a, V b) { return heff_buf_append(a, b, K_STR); }

// Lent strings: a primitive that only reads its strings has a `_lent`
// form, given besides its operands a mask, `give`, of those given it
// (bit `k` the `k`-th operand's): the others are lent, held by the caller
// through the call, neither counted up for it nor down by it.  The C
// backend calls it where an operand is a variable wanted after the call
// (the emitter's `lendingPrims`), and so saves a count up
// and down of its string each time -- a byte read in a loop, or a key
// compared at each node of a map.  (`give` is a constant there: what is
// not given is not looked at.)
#define HEFF_GIVEN(give, k, v) do { if ((give) >> (k) & 1) heff_drop(v); } while (0)

HEFF_FAST V heff_strLength_lent(V a, int give) {
  V n = MK_INT(((Str *)a)->len);
  HEFF_GIVEN(give, 0, a);
  return n;
}
HEFF_FN V heff_strLength(V a) { return heff_strLength_lent(a, 1); }

// Slices.  A slice of a string is a view of it, taking no copy, where it
// is long -- `HEFF_VIEW_MIN` bytes or more -- and at least a
// `HEFF_VIEW_SHARE`-th of its root: a view of a view is one of the root,
// so that a string whose tail is taken again and again is a view each
// time, until it is a short part of its root, then a copy, a root of its
// own.  A shorter slice is copied: it costs no more than a view, and
// holds no parent; and a view holds its root, so the bytes kept for it
// are at most `HEFF_VIEW_SHARE` times its own.  `Bytes` are sliced so
// too: a view is of any kind
#ifndef HEFF_VIEW_MIN
#define HEFF_VIEW_MIN 64
#endif
#ifndef HEFF_VIEW_SHARE
#define HEFF_VIEW_SHARE 4
#endif
_Static_assert(HEFF_VIEW_MIN > sizeof(V), "a view's length is more than its room");

// (`m` bytes of `x` from `b`, a view if they are enough of its root)
HEFF_FAST Str *heff_str_slice_long(Str *x, int64_t b, int64_t m) {
  Str *r = HEFF_STR_VIEW(x) ? (Str *)*HEFF_STR_ROOT(x) : x;
  if (m * HEFF_VIEW_SHARE >= r->len) {
    Str *w = heff_obj_alloc(sizeof(Str) + sizeof(V));
    w->h.rc = 1; w->h.kind = K_STR; w->h.tag = 0; w->len = m; w->cap = sizeof(V);
    w->p = x->p + b;
    heff_dup((V)r);
    *HEFF_STR_ROOT(w) = (V)r;
    return w;
  }
  Str *s = heff_str_new(m);
  memcpy(s->s, x->p + b, (size_t)m);
  return s;
}

// (as JavaScript's `slice`: out of range is clamped, negative from the
// end; a short one copied here, a long one by `heff_str_slice_long`)
HEFF_FN V heff_strSlice_lent(V a, V i, V j, int give) {
  Str *x = (Str *)a;
  int64_t n = x->len, b = INT_OF(i), e = INT_OF(j);
  if (b < 0) b = b + n < 0 ? 0 : b + n;
  if (e < 0) e = e + n < 0 ? 0 : e + n;
  if (b > n) b = n;
  if (e > n) e = n;
  if (e < b) e = b;
  if (!HEFF_LIKELY(e - b < HEFF_VIEW_MIN)) {
    Str *s = heff_str_slice_long(x, b, e - b);
    HEFF_GIVEN(give, 0, a);
    return (V)s;
  }
  Str *s = heff_str_new(e - b);
  memcpy(s->s, x->p + b, (size_t)(e - b));
  HEFF_GIVEN(give, 0, a);
  return (V)s;
}
HEFF_FN V heff_strSlice(V a, V i, V j) { return heff_strSlice_lent(a, i, j, 1); }

// (the 8 bytes at `p` as a number in their order: the first the highest)
static inline uint64_t heff_str_word(const uint8_t *p) {
  uint64_t w;
  memcpy(&w, p, sizeof w);
#if defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  w = __builtin_bswap64(w);
#endif
  return w;
}

// (the bytes' order: of UTF-8, its runes'.  Words, mostly short, are
// compared 8 bytes at a time, in place: no call to memcmp)
static inline int heff_str_cmp(V a, V b) {
  Str *x = (Str *)a, *y = (Str *)b;
  if (x == y) return 0;
  int64_t n = x->len < y->len ? x->len : y->len, i = 0;
  for (; i + 8 <= n; i += 8) {
    uint64_t u = heff_str_word(x->p + i), v = heff_str_word(y->p + i);
    if (u != v) return u < v ? -1 : 1;
  }
  for (; i < n; i++)
    if (x->p[i] != y->p[i]) return x->p[i] < y->p[i] ? -1 : 1;
  return x->len == y->len ? 0 : x->len < y->len ? -1 : 1;
}

// (the order of two strings at once: -1, 0 or 1)
HEFF_FAST V heff_strCompare_lent(V a, V b, int give) {
  int c = heff_str_cmp(a, b);
  HEFF_GIVEN(give, 0, a);
  HEFF_GIVEN(give, 1, b);
  return MK_INT(c);
}
HEFF_FN V heff_strCompare(V a, V b) { return heff_strCompare_lent(a, b, 3); }

// (where `needle` is first in `s` from `i` on (from 0, `i` below it), or
// -1: its first byte looked for by memchr, the rest compared there)
HEFF_FN V heff_strFind_lent(V needle, V s, V i, int give) {
  Str *p = (Str *)needle, *x = (Str *)s;
  int64_t k = INT_OF(i), m = p->len, r = -1;
  if (k < 0) k = 0;
  if (k + m <= x->len) {
    if (m == 0) r = k;
    else {
      const uint8_t *at = x->p + k, *end = x->p + x->len - m + 1;
      while (at < end && (at = memchr(at, p->p[0], (size_t)(end - at)))) {
        if (memcmp(at + 1, p->p + 1, (size_t)(m - 1)) == 0) { r = at - x->p; break; }
        at++;
      }
    }
  }
  HEFF_GIVEN(give, 0, needle);
  HEFF_GIVEN(give, 1, s);
  return MK_INT(r);
}
HEFF_FN V heff_strFind(V needle, V s, V i) { return heff_strFind_lent(needle, s, i, 3); }

// Hashes: a string's and an integer's, the runtime's Zig's -- the same
// numbers as JavaScript's and the interpreter's, so that a map's order
// is one everywhere -- each shifted right by 2, a word's integer, never
// negative.
HEFF_FAST V heff_strHash_lent(V a, int give) {
  Str *x = (Str *)a;
  V r = MK_INT((int64_t)(heff_hash_bytes(x->p, x->len) >> 2));
  HEFF_GIVEN(give, 0, a);
  return r;
}
HEFF_FN V heff_strHash(V a) { return heff_strHash_lent(a, 1); }

// (the bytes of `x` from `i` up to `j`, clamped as `strSlice` clamps
// them: where they start, and how many, read in place, not copied)
static inline int64_t heff_str_range(Str *x, V i, V j, int64_t *len) {
  int64_t n = x->len, b = INT_OF(i), e = INT_OF(j);
  if (b < 0) b = b + n < 0 ? 0 : b + n;
  if (e < 0) e = e + n < 0 ? 0 : e + n;
  if (b > n) b = n;
  if (e > n) e = n;
  if (e < b) e = b;
  *len = e - b;
  return b;
}

// (the hash of `strSlice a i j`, no slice made)
HEFF_FAST V heff_strHashRange_lent(V a, V i, V j, int give) {
  Str *x = (Str *)a;
  int64_t m, b = heff_str_range(x, i, j, &m);
  V r = MK_INT((int64_t)(heff_hash_bytes(x->p + b, m) >> 2));
  HEFF_GIVEN(give, 0, a);
  return r;
}
HEFF_FN V heff_strHashRange(V a, V i, V j) { return heff_strHashRange_lent(a, i, j, 1); }

// (whether `t` is `strSlice s i j`, no slice made)
HEFF_FAST V heff_strEqRange_lent(V t, V s, V i, V j, int give) {
  Str *x = (Str *)t, *y = (Str *)s;
  int64_t m, b = heff_str_range(y, i, j, &m);
  int c = x->len == m && memcmp(x->p, y->p + b, (size_t)m) == 0;
  HEFF_GIVEN(give, 0, t);
  HEFF_GIVEN(give, 1, s);
  return heff_bool(c);
}
HEFF_FN V heff_strEqRange(V t, V s, V i, V j) { return heff_strEqRange_lent(t, s, i, j, 3); }

HEFF_SLOW V heff_intHash_big(V a) {
  uint64_t h = heff_int_hash(a);
  heff_drop(a);
  return MK_INT((int64_t)(h >> 2));
}

// (a word's, inlined: murmur3's finish of its 64 bits, as the Zig's
// does it; a big one's, the call)
HEFF_FAST V heff_intHash(V a) {
  if (HEFF_LIKELY(IS_INT(a))) {
    uint64_t h = (uint64_t)INT_OF(a);
    h ^= h >> 33;
    h *= 0xff51afd7ed558ccdULL;
    h ^= h >> 33;
    h *= 0xc4ceb9fe1a85ec53ULL;
    h ^= h >> 33;
    return MK_INT((int64_t)(h >> 2));
  }
  return heff_intHash_big(a);
}

// (a trie's step: the 5 bits of the hash `h` from bit `s` on choose one of
// 32 children, and the node's bitmap `bm` says which it has -- where the
// one chosen is among them, the bits set below its counted, or, where it
// is not, -1 less that.  The bits are two's complement's, as `shiftR` and
// `and` have them)
HEFF_SLOW int64_t heff_trie_frag_big(V h, V s) {
  return INT_OF(heff_intAnd(heff_intShr(h, s), MK_INT(31)));
}

HEFF_FAST V heff_trieSlot(V bm, V h, V s) {
  int64_t frag;
  if (HEFF_LIKELY(IS_INT(h) && IS_INT(s) && INT_OF(s) >= 0)) {
    int64_t k = INT_OF(s);
    frag = (INT_OF(h) >> (k < 63 ? k : 63)) & 31;
  } else frag = heff_trie_frag_big(h, s);
  uint64_t b = (uint64_t)INT_OF(bm), bit = (uint64_t)1 << frag;
  int64_t i = __builtin_popcountll(b & (bit - 1));
  return MK_INT(b & bit ? i : -1 - i);
}

// (as C's condition, and as a Bool: see `INT_CMP`)
HEFF_FAST int heff_strEq_c_lent(V a, V b, int give) {
  Str *x = (Str *)a, *y = (Str *)b;
  int c = x == y || (x->len == y->len && memcmp(x->p, y->p, (size_t)x->len) == 0);
  HEFF_GIVEN(give, 0, a);
  HEFF_GIVEN(give, 1, b);
  return c;
}
HEFF_FN int heff_strEq_c(V a, V b) { return heff_strEq_c_lent(a, b, 3); }
static inline V heff_strEq(V a, V b) { return heff_bool(heff_strEq_c(a, b)); }
HEFF_FAST V heff_strEq_lent(V a, V b, int give) { return heff_bool(heff_strEq_c_lent(a, b, give)); }

HEFF_FAST int heff_strLt_c_lent(V a, V b, int give) {
  int c = heff_str_cmp(a, b);
  HEFF_GIVEN(give, 0, a);
  HEFF_GIVEN(give, 1, b);
  return c < 0;
}
HEFF_FN int heff_strLt_c(V a, V b) { return heff_strLt_c_lent(a, b, 3); }
static inline V heff_strLt(V a, V b) { return heff_bool(heff_strLt_c(a, b)); }
HEFF_FAST V heff_strLt_lent(V a, V b, int give) { return heff_bool(heff_strLt_c_lent(a, b, give)); }

// (the byte at `i`; out of the string, -1)
HEFF_FAST V heff_strByteAt_lent(V a, V i, int give) {
  Str *x = (Str *)a;
  int64_t k = INT_OF(i);
  V r = k >= 0 && k < x->len ? MK_INT(x->p[k]) : MK_INT(-1);
  HEFF_GIVEN(give, 0, a);
  return r;
}
HEFF_FN V heff_strByteAt(V a, V i) { return heff_strByteAt_lent(a, i, 1); }

// (the 256 strings of one byte, made by the C compiler, immortal: a
// string's room, as a static one's is, in the program's first file)
typedef struct { Obj h; int64_t len; int64_t cap; uint8_t *p; uint8_t s[8]; } HeffByteStr;
#ifdef HEFF_PART
extern HeffByteStr heff_byte_strs[256];
#else
#define HEFF_BYTE_STR(b) {{IMMORTAL, K_STR, 0}, 1, 1, heff_byte_strs[b].s, {b}}
#define HEFF_BYTE_STR4(b) HEFF_BYTE_STR(b), HEFF_BYTE_STR(b + 1), HEFF_BYTE_STR(b + 2), HEFF_BYTE_STR(b + 3)
#define HEFF_BYTE_STR16(b) HEFF_BYTE_STR4(b), HEFF_BYTE_STR4(b + 4), HEFF_BYTE_STR4(b + 8), HEFF_BYTE_STR4(b + 12)
#define HEFF_BYTE_STR64(b) HEFF_BYTE_STR16(b), HEFF_BYTE_STR16(b + 16), HEFF_BYTE_STR16(b + 32), HEFF_BYTE_STR16(b + 48)
HeffByteStr heff_byte_strs[256] = {
  HEFF_BYTE_STR64(0), HEFF_BYTE_STR64(64), HEFF_BYTE_STR64(128), HEFF_BYTE_STR64(192)
};
#endif

// (the string of one byte, a `UInt8`: a word of its value, 0 to 255 --
// one of the 256, nothing made)
HEFF_FN V heff_strFromByte(V c) { return (V)&heff_byte_strs[(uint8_t)INT_OF(c)]; }

// (a word's digits on the stack, nothing allocated but the string; a
// big one's by its digits')
HEFF_FN V heff_intShow(V a) {
  if (HEFF_LIKELY(IS_INT(a))) {
    char b[24], *p = heff_word_digits(INT_OF(a), b + sizeof b);
    return heff_str_of(p, b + sizeof b - p);
  }
  char *c = heff_int_cstr(a);
  heff_drop(a);
  V s = heff_str_ascii(c);
  free(c);
  return s;
}

// Floats
// ---------------------------------------------------------------------

HEFF_FN V heff_flt(double d) {
  Flt *f = heff_obj_alloc(sizeof(Flt));
  f->h.rc = 1; f->h.kind = K_FLT; f->h.tag = 0; f->d = d;
  return (V)f;
}

#define FLT_OF(v) (((Flt *)(v))->d)

// (two floats' operation, both consumed)
#define FLT2(name, expr) \
  HEFF_FN V name(V a, V b) { double x = FLT_OF(a), y = FLT_OF(b); heff_drop(a); heff_drop(b); return expr; }
FLT2(heff_floatAdd, heff_flt(x + y))
FLT2(heff_floatSub, heff_flt(x - y))
FLT2(heff_floatMul, heff_flt(x * y))
FLT2(heff_floatDiv, heff_flt(x / y))
// (as C's condition, and as a Bool: see `INT_CMP`)
#define FLT_CMP(name, op)                                                   \
  static inline int name##_c(V a, V b) {                                    \
    double x = FLT_OF(a), y = FLT_OF(b); heff_drop(a); heff_drop(b); return x op y; } \
  static inline V name(V a, V b) { return heff_bool(name##_c(a, b)); }
FLT_CMP(heff_floatEq, ==)
FLT_CMP(heff_floatLt, <)
FLT_CMP(heff_floatLe, <=)
HEFF_FN V heff_floatFromInt(V a) { double d = heff_double_of_int(a); heff_drop(a); return heff_flt(d); }
HEFF_FN V heff_floatSqrt(V a) { double x = FLT_OF(a); heff_drop(a); return heff_flt(sqrt(x)); }
// (the target the program is built for)
HEFF_FN V heff_onWindows(V u) {
  heff_drop(u);
#ifdef _WIN32
  return heff_bool(1);
#else
  return heff_bool(0);
#endif
}

// (std.math's: libm's, as JavaScript's `Math` has them -- but sin, cos,
// tan, exp and log, the runtime's own, bundled after it)
#define FLT1(name, f) \
  HEFF_FN V name(V a) { double x = FLT_OF(a); heff_drop(a); return heff_flt(f(x)); }
FLT1(heff_floatAsin, asin)
FLT1(heff_floatAcos, acos)
FLT1(heff_floatAtan, atan)
FLT2(heff_floatAtan2, heff_flt(atan2(x, y)))
FLT2(heff_floatPow, heff_flt(pow(x, y)))

// (of what is not finite, 0)
HEFF_FN V heff_floatFloor(V a) {
  double d = FLT_OF(a);
  heff_drop(a);
  if (!isfinite(d)) return MK_INT(0);
  double f = floor(d);
  return heff_int_of_double(f);
}

HEFF_FN V heff_floatShow(V a) {
  char buf[64];
  heff_show_float(FLT_OF(a), buf);
  heff_drop(a);
  return heff_str_ascii(buf);
}

// A Float32 is kept in a word, its bits as an integer's: nothing is
// allocated for one, as it is for a float.
static inline V heff_f32(float f) {
  uint32_t u;
  memcpy(&u, &f, sizeof u);
  return MK_INT((int64_t)u);
}

static inline float heff_f32_of(V v) {
  uint32_t u = (uint32_t)INT_OF(v);
  float f;
  memcpy(&f, &u, sizeof f);
  return f;
}

// Fixed-width numbers
// ---------------------------------------------------------------------
// (heff.elab.fixed's.)  An integer of up to 32 bits is a word of its value,
// in its type's range; one of 64 bits is kept as an `Int` is (a word, big
// beyond 62 bits), so `toInt` is nothing.  An integer's operation is
// done on its 64 bits, unsigned (where no overflow is undefined), and the
// result wrapped around to its type; a division by -1 is a negation
// (that of the least, itself), as no C division by -1 is safe, and one
// by 0 is 0, its remainder the dividend, as an `Int`'s are.  A
// `Float32` is a word of its bits (`heff_f32`): C's `float` is IEEE's,
// each operation rounded, as JavaScript's `Math.fround` rounds.

// (an integer's lowest 64 bits, as two's complement has them; borrowed:
// a word's inlined, a big one's the call)
HEFF_SLOW uint64_t heff_big_low64(V v) {
  Big *b = (Big *)v;
  uint64_t m = b->d[0];
  return b->neg ? (uint64_t)0 - m : m;
}

HEFF_FAST uint64_t heff_int_low64(V v) {
  if (HEFF_LIKELY(IS_INT(v))) return (uint64_t)INT_OF(v);
  return heff_big_low64(v);
}

// (an integer of 64 bits, unsigned: a word inlined, a big one the call)
HEFF_SLOW V heff_u64_big(uint64_t m) {
  Big *b = big_new(1);
  b->d[0] = m;
  return big_fin(b, 0, 1);
}

HEFF_FAST V heff_int_u64(uint64_t m) {
  if (HEFF_LIKELY(m < (uint64_t)INT_LIM)) return MK_INT((int64_t)m);
  return heff_u64_big(m);
}

// (a value of the type `T`, its 64 bits taken (and consumed), and one
// made of 64 bits, wrapped around to `T`)
#define FX_WORD(T)                                                          \
  static inline uint64_t fx_get_##T(V v) { return (uint64_t)INT_OF(v); }    \
  static inline V fx_mk_##T(uint64_t u) { return MK_INT((int64_t)(T)u); }
FX_WORD(int8_t)
FX_WORD(int16_t)
FX_WORD(int32_t)
FX_WORD(uint8_t)
FX_WORD(uint16_t)
FX_WORD(uint32_t)

static inline uint64_t fx_get_int64_t(V v) {
  uint64_t u = heff_int_low64(v);
  heff_drop(v);
  return u;
}
static inline V fx_mk_int64_t(uint64_t u) { return heff_int((int64_t)u); }
static inline uint64_t fx_get_uint64_t(V v) { return fx_get_int64_t(v); }
static inline V fx_mk_uint64_t(uint64_t u) { return heff_int_u64(u); }

// (an integer type's operations on its C type `T` (`heff_div_i32` and the
// rest, `S` its suffix, `BITS` its bits), which its primitives are made of
// and a program's unboxed numbers (#39) are computed by: a shift is by the
// count modulo the bits, and by a negative count, of a signed type, the
// other way by its size)
#define FX_OPS(name, S, T, BITS)                                                     \
  static inline T heff_div_##S(T x, T y) {                                           \
    if (y == 0) return 0;                                                            \
    if ((T)-1 < (T)0 && y == (T)-1) return (T)((uint64_t)0 - (uint64_t)x);          \
    return (T)(x / y); }                                                             \
  static inline T heff_rem_##S(T x, T y) {                                           \
    if (y == 0) return x;                                                            \
    if ((T)-1 < (T)0 && y == (T)-1) return 0;                                        \
    return (T)(x % y); }                                                             \
  static inline uint64_t heff_##name##Left(uint64_t x, uint64_t n) {                 \
    return x << (n & (BITS - 1)); }                                                  \
  static inline uint64_t heff_##name##Right(uint64_t x, uint64_t n) {                \
    return (uint64_t)((T)x >> (n & (BITS - 1))); }                                   \
  static inline T heff_shl_##S(T a, T b) {                                           \
    uint64_t x = (uint64_t)a, y = (uint64_t)b;                                       \
    if ((T)-1 < (T)0 && (int64_t)y < 0) return (T)heff_##name##Right(x, 0 - y);      \
    return (T)heff_##name##Left(x, y); }                                             \
  static inline T heff_shr_##S(T a, T b) {                                           \
    uint64_t x = (uint64_t)a, y = (uint64_t)b;                                       \
    if ((T)-1 < (T)0 && (int64_t)y < 0) return (T)heff_##name##Left(x, 0 - y);       \
    return (T)heff_##name##Right(x, y); }

// (an integer type's primitives: `heff_int32Add` and the rest, `T` its C
// type, `S` its suffix, `BITS` its bits)
#define FX_INT(name, S, T, BITS)                                                     \
  FX_OPS(name, S, T, BITS)                                                           \
  static V heff_##name##Add(V a, V b) {                                              \
    uint64_t x = fx_get_##T(a), y = fx_get_##T(b); return fx_mk_##T(x + y); }       \
  static V heff_##name##Sub(V a, V b) {                                              \
    uint64_t x = fx_get_##T(a), y = fx_get_##T(b); return fx_mk_##T(x - y); }       \
  static V heff_##name##Mul(V a, V b) {                                              \
    uint64_t x = fx_get_##T(a), y = fx_get_##T(b); return fx_mk_##T(x * y); }       \
  static V heff_##name##Div(V a, V b) {                                              \
    T x = (T)fx_get_##T(a), y = (T)fx_get_##T(b);                                   \
    return fx_mk_##T((uint64_t)heff_div_##S(x, y)); }                                \
  static V heff_##name##Rem(V a, V b) {                                              \
    T x = (T)fx_get_##T(a), y = (T)fx_get_##T(b);                                   \
    return fx_mk_##T((uint64_t)heff_rem_##S(x, y)); }                                \
  static inline int heff_##name##Eq_c(V a, V b) {                                   \
    T x = (T)fx_get_##T(a), y = (T)fx_get_##T(b); return x == y; }                  \
  static inline int heff_##name##Lt_c(V a, V b) {                                   \
    T x = (T)fx_get_##T(a), y = (T)fx_get_##T(b); return x < y; }                   \
  static inline int heff_##name##Le_c(V a, V b) {                                   \
    T x = (T)fx_get_##T(a), y = (T)fx_get_##T(b); return x <= y; }                  \
  static inline V heff_##name##Eq(V a, V b) { return heff_bool(heff_##name##Eq_c(a, b)); } \
  static inline V heff_##name##Lt(V a, V b) { return heff_bool(heff_##name##Lt_c(a, b)); } \
  static inline V heff_##name##Le(V a, V b) { return heff_bool(heff_##name##Le_c(a, b)); } \
  static V heff_##name##And(V a, V b) {                                              \
    uint64_t x = fx_get_##T(a), y = fx_get_##T(b); return fx_mk_##T(x & y); }       \
  static V heff_##name##Or(V a, V b) {                                               \
    uint64_t x = fx_get_##T(a), y = fx_get_##T(b); return fx_mk_##T(x | y); }       \
  static V heff_##name##Xor(V a, V b) {                                              \
    uint64_t x = fx_get_##T(a), y = fx_get_##T(b); return fx_mk_##T(x ^ y); }       \
  static V heff_##name##Shl(V a, V b) {                                              \
    T x = (T)fx_get_##T(a), y = (T)fx_get_##T(b);                                   \
    return fx_mk_##T((uint64_t)heff_shl_##S(x, y)); }                                \
  static V heff_##name##Shr(V a, V b) {                                              \
    T x = (T)fx_get_##T(a), y = (T)fx_get_##T(b);                                   \
    return fx_mk_##T((uint64_t)heff_shr_##S(x, y)); }                                \
  static V heff_##name##Show(V a) { return heff_intShow(a); }                        \
  static V heff_##name##FromInt(V a) {                                               \
    uint64_t u = heff_int_low64(a); heff_drop(a); return fx_mk_##T(u); }             \
  static V heff_##name##ToInt(V a) { return a; }
FX_INT(int8, i8, int8_t, 8)
FX_INT(int16, i16, int16_t, 16)
FX_INT(int32, i32, int32_t, 32)
FX_INT(int64, i64, int64_t, 64)
FX_INT(uint8, u8, uint8_t, 8)
FX_INT(uint16, u16, uint16_t, 16)
FX_INT(uint32, u32, uint32_t, 32)
FX_INT(uint64, u64, uint64_t, 64)

#define F32_2(name, expr) \
  static V heff_float32##name(V a, V b) { float x = heff_f32_of(a), y = heff_f32_of(b); return expr; }
F32_2(Add, heff_f32(x + y))
F32_2(Sub, heff_f32(x - y))
F32_2(Mul, heff_f32(x * y))
F32_2(Div, heff_f32(x / y))
#define F32_CMP(name, op)                                                                  \
  static inline int heff_float32##name##_c(V a, V b) { return heff_f32_of(a) op heff_f32_of(b); } \
  static inline V heff_float32##name(V a, V b) { return heff_bool(heff_float32##name##_c(a, b)); }
F32_CMP(Eq, ==)
F32_CMP(Lt, <)
F32_CMP(Le, <=)
HEFF_FN V heff_float32Sqrt(V a) { return heff_f32(sqrtf(heff_f32_of(a))); }

// (the fewest digits that read back as the same `Float32`, as a literal
// at `Float32` reads them, rounded once, written as a float is: of those,
// the nearest it (of two as near, the one whose last digit is even); nine
// always do)
HEFF_FN V heff_float32Show(V a) {
  char buf[64];
  heff_show_float32(heff_f32_of(a), buf);
  return heff_str_ascii(buf);
}

HEFF_FN V heff_float32FromFloat(V a) { float f = (float)FLT_OF(a); heff_drop(a); return heff_f32(f); }
HEFF_FN V heff_float32ToFloat(V a) { return heff_flt((double)heff_f32_of(a)); }
HEFF_FN V heff_float32FromInt(V a) { double d = heff_double_of_int(a); heff_drop(a); return heff_f32((float)d); }
HEFF_FN V heff_float32Floor(V a) {
  double d = heff_f32_of(a);
  if (!isfinite(d)) return MK_INT(0);
  return heff_int_of_double(floor(d));
}

// Unboxed numbers (#39)
// ---------------------------------------------------------------------
// Where a program computes with a fixed-width number or a `Float64`, it
// keeps it as its C type, and makes it a `V`
// only where one is wanted: `heff_box_S` (`S` the type's suffix, `i64`,
// `f32`, ...), the `V` made of it; `heff_unbox_S`, the number of a `V`,
// consumed; `heff_peek_S`, looked at.  `heff_from_int_S` is the type's
// `fromInt` of an `Int` (consumed), `heff_floor_S` its `floor`.

#define FX_BOXES(S, T)                                                      \
  static inline V heff_box_##S(T x) { return fx_mk_##T((uint64_t)x); }      \
  static inline T heff_unbox_##S(V v) { return (T)fx_get_##T(v); }         \
  static inline T heff_peek_##S(V v) { return (T)heff_int_low64(v); }      \
  static inline T heff_from_int_##S(V v) {                                 \
    uint64_t u = heff_int_low64(v); heff_drop(v); return (T)u; }
FX_BOXES(i8, int8_t)
FX_BOXES(i16, int16_t)
FX_BOXES(i32, int32_t)
FX_BOXES(i64, int64_t)
FX_BOXES(u8, uint8_t)
FX_BOXES(u16, uint16_t)
FX_BOXES(u32, uint32_t)
FX_BOXES(u64, uint64_t)

static inline V heff_box_f32(float x) { return heff_f32(x); }
static inline float heff_unbox_f32(V v) { return heff_f32_of(v); }
static inline float heff_peek_f32(V v) { return heff_f32_of(v); }
static inline float heff_from_int_f32(V v) {
  double d = heff_double_of_int(v); heff_drop(v); return (float)d; }

static inline V heff_box_f64(double x) { return heff_flt(x); }
static inline double heff_unbox_f64(V v) { double d = FLT_OF(v); heff_drop(v); return d; }
static inline double heff_peek_f64(V v) { return FLT_OF(v); }
static inline double heff_from_int_f64(V v) {
  double d = heff_double_of_int(v); heff_drop(v); return d; }

// An `Int` known to fit a word (#79), kept
// as its `int64_t`: its `V` is a word, nothing to count, so unboxed or
// looked at alike.  A division and a remainder of two, by one not 0,
// rounded down as `heff_intDiv` and `heff_intMod` round.
static inline V heff_box_word(int64_t x) { return MK_INT(x); }
static inline int64_t heff_unbox_word(V v) { return INT_OF(v); }
static inline int64_t heff_peek_word(V v) { return INT_OF(v); }
static inline int64_t heff_word_div(int64_t x, int64_t y) {
  int64_t q = x / y, r = x % y;
  return r != 0 && ((r < 0) != (y < 0)) ? q - 1 : q;
}
static inline int64_t heff_word_mod(int64_t x, int64_t y) {
  int64_t r = x % y;
  return r != 0 && ((r < 0) != (y < 0)) ? r + y : r;
}

// A record's flat fields (#39, "Flat fields" above): a number's bits, the
// field so made (`heff_word_S`), and the field read as a number,
// whichever it is, flat or a `V` (`heff_rget_S`); the record consumed
// after (`heff_get_n_S`), or the field as a `V`, boxed if it is flat
// (`heff_rget_v`).

static inline V heff_word_f64(double d) { V w; memcpy(&w, &d, sizeof w); return w; }
static inline V heff_word_i64(int64_t x) { return (V)(uint64_t)x; }
static inline V heff_word_u64(uint64_t x) { return (V)x; }
static inline double heff_f64_of_word(V w) { double d; memcpy(&d, &w, sizeof d); return d; }

HEFF_FN V heff_flat_box(V w, unsigned k) {
  if (k == HEFF_FLAT_F64) return heff_flt(heff_f64_of_word(w));
  if (k == HEFF_FLAT_I64) return heff_int((int64_t)w);
  return heff_int_u64((uint64_t)w);
}

HEFF_FAST double heff_rget_f64(V v, int64_t i) {
  Rec *r = (Rec *)v;
  V w = r->f[i];
  return heff_flat_kind(r->flat, i) ? heff_f64_of_word(w) : FLT_OF(w);
}
HEFF_FAST int64_t heff_rget_i64(V v, int64_t i) {
  Rec *r = (Rec *)v;
  V w = r->f[i];
  return heff_flat_kind(r->flat, i) ? (int64_t)w : (int64_t)heff_int_low64(w);
}
HEFF_FAST uint64_t heff_rget_u64(V v, int64_t i) {
  Rec *r = (Rec *)v;
  V w = r->f[i];
  return heff_flat_kind(r->flat, i) ? (uint64_t)w : heff_int_low64(w);
}
HEFF_FAST V heff_rget_v(V v, int64_t i) { return heff_rec_dup_field((Rec *)v, i); }

#define HEFF_GET_N_FLAT(S, T)                                               \
  HEFF_KNOWN T heff_get_n_##S(V v, int64_t i, int64_t n) {                  \
    T x = heff_rget_##S(v, i); heff_drop_rec(v, n); return x; }
HEFF_GET_N_FLAT(f64, double)
HEFF_GET_N_FLAT(i64, int64_t)
HEFF_GET_N_FLAT(u64, uint64_t)

// (... a field flat in every record of its shape the program builds
// (the compiler's `sureRecs`), read as it is)
HEFF_FAST double heff_rflat_f64(V v, int64_t i) { return heff_f64_of_word(((Rec *)v)->f[i]); }
HEFF_FAST int64_t heff_rflat_i64(V v, int64_t i) { return (int64_t)((Rec *)v)->f[i]; }
HEFF_FAST uint64_t heff_rflat_u64(V v, int64_t i) { return (uint64_t)((Rec *)v)->f[i]; }
#define HEFF_GET_NFLAT(S, T)                                                \
  HEFF_KNOWN T heff_get_nflat_##S(V v, int64_t i, int64_t n) {              \
    T x = heff_rflat_##S(v, i); heff_drop_rec(v, n); return x; }
HEFF_GET_NFLAT(f64, double)
HEFF_GET_NFLAT(i64, int64_t)
HEFF_GET_NFLAT(u64, uint64_t)

// A tag's fields that may be flat (#64), read where a match binds one:
// as a number, whichever the tag holds (`heff_tget_S`, the tag looked at;
// of a type never kept flat, the `V` looked at), or as a `V` of its own
// (`heff_tget_v`: counted, boxed if it is flat).

HEFF_FAST double heff_tget_f64(V v, int64_t i) {
  Tag *t = (Tag *)v;
  V w = t->f[i];
  return heff_flat_kind(t->flat, i) ? heff_f64_of_word(w) : FLT_OF(w);
}
HEFF_FAST int64_t heff_tget_i64(V v, int64_t i) {
  Tag *t = (Tag *)v;
  V w = t->f[i];
  return heff_flat_kind(t->flat, i) ? (int64_t)w : (int64_t)heff_int_low64(w);
}
HEFF_FAST uint64_t heff_tget_u64(V v, int64_t i) {
  Tag *t = (Tag *)v;
  V w = t->f[i];
  return heff_flat_kind(t->flat, i) ? (uint64_t)w : heff_int_low64(w);
}
// (... one flat in every tag of it the program builds, as it is)
HEFF_FAST double heff_tflat_f64(V v, int64_t i) { return heff_f64_of_word(((Tag *)v)->f[i]); }
HEFF_FAST int64_t heff_tflat_i64(V v, int64_t i) { return (int64_t)((Tag *)v)->f[i]; }
HEFF_FAST uint64_t heff_tflat_u64(V v, int64_t i) { return (uint64_t)((Tag *)v)->f[i]; }
#define HEFF_TGET_PEEK(S, T)                                                \
  HEFF_FAST T heff_tget_##S(V v, int64_t i) { return heff_peek_##S(((Tag *)v)->f[i]); }
HEFF_TGET_PEEK(i8, int8_t)
HEFF_TGET_PEEK(i16, int16_t)
HEFF_TGET_PEEK(i32, int32_t)
HEFF_TGET_PEEK(u8, uint8_t)
HEFF_TGET_PEEK(u16, uint16_t)
HEFF_TGET_PEEK(u32, uint32_t)
HEFF_TGET_PEEK(f32, float)
HEFF_FAST V heff_tget_v(V v, int64_t i) {
  Tag *t = (Tag *)v;
  unsigned k = heff_flat_kind(t->flat, i);
  return k ? heff_flat_box(t->f[i], k) : heff_dup(t->f[i]);
}

// (of what is not finite, 0)
HEFF_FN V heff_floor_f64(double d) {
  if (!isfinite(d)) return MK_INT(0);
  return heff_int_of_double(floor(d));
}
HEFF_FN V heff_floor_f32(float f) { return heff_floor_f64((double)f); }

// Runes
// ---------------------------------------------------------------------
// A `Rune` is a word of its code point, a 32-bit value, as Go's `rune` is:
// `fromInt` wraps an integer around to 32 bits, as `int32FromInt` does,
// so `toInt` is nothing.  One that is no Unicode scalar value (a
// surrogate, below 0, beyond U+10FFFF) is U+FFFD in a string made of it;
// what is not UTF-8 in a string is read as U+FFFD (`heff_u8_decode`).

static inline int heff_runeEq_c(V a, V b) { return a == b; }
static inline int heff_runeLt_c(V a, V b) { return INT_OF(a) < INT_OF(b); }
static inline int heff_runeLe_c(V a, V b) { return INT_OF(a) <= INT_OF(b); }
static inline V heff_runeEq(V a, V b) { return heff_bool(heff_runeEq_c(a, b)); }
static inline V heff_runeLt(V a, V b) { return heff_bool(heff_runeLt_c(a, b)); }
static inline V heff_runeLe(V a, V b) { return heff_bool(heff_runeLe_c(a, b)); }
HEFF_FN V heff_runeToInt(V a) { return a; }
HEFF_FN V heff_runeFromInt(V a) { return heff_int32FromInt(a); }

// (a string's runes: read, then put in a list from the last)
HEFF_FN V heff_strRunes(V a) {
  Str *x = (Str *)a;
  uint32_t *rs = heff_alloc((size_t)(x->len + 1) * sizeof(uint32_t));
  int64_t m = 0;
  for (int64_t i = 0; i < x->len; m++) i += heff_u8_read(x->p + i, x->len - i, &rs[m]);
  V l = NTAG(TAG_Nil);
  for (int64_t k = m - 1; k >= 0; k--) {
    V f[2] = { MK_INT((int64_t)rs[k]), l };
    l = heff_tag(TAG_Cons, 2, f);
  }
  free(rs);
  heff_drop(a);
  return l;
}

static inline int heff_rune_scalar(int64_t r) {
  return r >= 0 && r <= 0x10FFFF && !(r >= 0xD800 && r < 0xE000);
}

// (the runes' string: each its UTF-8 bytes, counted first by its value
// alone, then written; an ASCII rune written where it is)
HEFF_FN V heff_strOfRunes(V l) {
  int64_t n = 0;
  for (V c = l; heff_tag_of(c) == TAG_Cons; c = heff_field(c, 1)) {
    int64_t r = INT_OF(heff_field(c, 0));
    n += !heff_rune_scalar(r) ? 3 : r < 0x80 ? 1 : r < 0x800 ? 2 : r < 0x10000 ? 3 : 4;
  }
  Str *s = heff_str_new(n);
  int64_t k = 0;
  for (V c = l; heff_tag_of(c) == TAG_Cons; c = heff_field(c, 1)) {
    int64_t r = INT_OF(heff_field(c, 0));
    if (r >= 0 && r < 0x80) s->s[k++] = (uint8_t)r;
    else k += heff_u8_encode(s->s + k, heff_rune_scalar(r) ? (uint32_t)r : 0xFFFD);
  }
  heff_drop(l);
  return (V)s;
}

// (the rune at `i`, and how many bytes it takes, `*w`; out of the
// string, U+FFFD of none: an ASCII byte read where it is called, any
// other by the decoder)
HEFF_FAST uint32_t heff_str_rune_at(Str *x, int64_t i, int64_t *w) {
  if (i < 0 || i >= x->len) { *w = 0; return 0xFFFD; }
  if (x->p[i] < 0x80) { *w = 1; return x->p[i]; }
  uint32_t u;
  *w = heff_u8_decode(x->p + i, x->len - i, &u);
  return u;
}

HEFF_FAST V heff_strRuneAt_lent(V a, V i, int give) {
  int64_t w;
  uint32_t r = heff_str_rune_at((Str *)a, INT_OF(i), &w);
  HEFF_GIVEN(give, 0, a);
  return MK_INT((int64_t)r);
}
HEFF_FN V heff_strRuneAt(V a, V i) { return heff_strRuneAt_lent(a, i, 1); }

HEFF_FAST V heff_strRuneWidth_lent(V a, V i, int give) {
  int64_t w;
  heff_str_rune_at((Str *)a, INT_OF(i), &w);
  HEFF_GIVEN(give, 0, a);
  return MK_INT(w);
}
HEFF_FN V heff_strRuneWidth(V a, V i) { return heff_strRuneWidth_lent(a, i, 1); }

// (the rune at `i` and its width, read once: the two of `strRuneAt` and
// `strRuneWidth`, a tuple)
HEFF_FAST HeffT2 heff_strRuneDecode_lent(V a, V i, int give) {
  int64_t w;
  uint32_t r = heff_str_rune_at((Str *)a, INT_OF(i), &w);
  HEFF_GIVEN(give, 0, a);
  return (HeffT2){{MK_INT((int64_t)r), MK_INT(w)}};
}
HEFF_FN HeffT2 heff_strRuneDecode(V a, V i) { return heff_strRuneDecode_lent(a, i, 1); }

HEFF_FN V heff_strRuneCount(V a) {
  Str *x = (Str *)a;
  int64_t n = 0;
  uint32_t u;
  for (int64_t i = 0; i < x->len; n++) i += heff_u8_read(x->p + i, x->len - i, &u);
  heff_drop(a);
  return MK_INT(n);
}

// Arrays
// ---------------------------------------------------------------------
// An array's elements are `V`s, or flat: a number's C type, an array of
// `double`s, of `int64_t`s, of `uint8_t`s, as the header's `tag` says
// (`HEFF_ARR_F64` and the others), so that nothing is allocated for an
// element, nor counted, and the elements are as near one another as C's
// are.  An array is built flat where the element it is built of is
// known to be a number (the element's repr),
// `heff_arrayReplicate_u8` and the others; built of `V`s, it is flat
// only where they are `Float64`s, each a box of its own (`K_FLT`) -- so
// an array of `Float64`s, if it has an element, is always flat, and read
// where that is known it is read as one, not looked at
// (`heff_arrayIndex_f64`).  An array of another number's type may hold
// `V`s, built where its type is not known (`generate` of a function):
// read where the type is known, it is looked at (`heff_arrayIndex_u8`);
// read where it is not, a flat element is boxed (`heff_arrayIndex`).
//
// `set` writes in place where the array is held only there (its count
// 1), and copies it otherwise: what the program sees is an array not
// changed, as it would be were each `set` a copy.  The path where it is
// held only there, the index in range and the element as the array keeps
// it, is inlined where it is used (`heff_arraySet_u8`); any other is a
// call (`heff_arr_set_slow`).  A read lends the array (`_lent`, as a
// string's), so that a read of an array set after is not a count up and
// down of it.
//
// An array grows the same way: `push`, `append`, `insertAt`, `reserve`
// write into the room after its elements where it is held only there,
// and where there is none it is grown, its room the next power of 2 (a
// block the system gave, by `realloc`) -- so an array built a push at a
// time is copied a logarithmic number of times, not once a push.  `pop`
// lowers the length, the room kept.  Held elsewhere too, it is copied first,
// with room to grow.

// (the most elements an array has room for: more than memory holds, and
// few enough that their bytes are counted without overflowing -- an
// array asked to be longer fails, as memory running out does, not a
// block too small for it written past)
#define HEFF_ARR_MAX ((int64_t)1 << 56)

// (an array of `n` elements, its room `n`)
HEFF_FN Arr *heff_arr_alloc(int64_t n, unsigned kind) {
  if (n > HEFF_ARR_MAX) heff_fail("out of memory");
  Arr *r = heff_obj_alloc(sizeof(Arr) + (size_t)n * heff_arr_width[kind]);
  r->h.rc = 1; r->h.kind = K_ARR; r->h.tag = (uint16_t)kind; r->n = n;
  return r;
}

HEFF_FN Arr *heff_arr_new(int64_t n) { return heff_arr_alloc(n, HEFF_ARR_V); }

// (an array's elements, as C's array of `T`)
#define HEFF_ARR_AT(r, T) ((T *)(void *)(r)->a)

// (an array's length, of how many it is asked for: none for less, and no
// more than memory holds)
HEFF_FN int64_t heff_arr_count(V n) {
  if (IS_INT(n)) return INT_OF(n) > 0 ? INT_OF(n) : 0;
  if (((Big *)n)->neg) return 0;
  heff_fail("out of memory");
  return 0;
}

// (out of range, abandoned)
HEFF_FN __attribute__((noinline, cold)) void heff_arr_out(void) { heff_abandon(); }

// (whether an index is in range)
#define heff_arr_in(r, i) (IS_INT(i) && (uint64_t)INT_OF(i) < (uint64_t)(r)->n)

// (whether the array is held only here and keeps its elements as `kind`
// says: its header, one word, all of it looked at at once -- in
// threads read atomically, relaxed, as `heff_rc` reads a count, a plain
// load still; one shared, held only here, as `heff_alone` has it)
static inline int heff_arr_mine(Arr *r, unsigned kind) {
#if defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
#ifdef HEFF_THREADS
  uint64_t h = __atomic_load_n((uint64_t *)&r->h, __ATOMIC_RELAXED);
#else
  uint64_t h;
  memcpy(&h, &r->h, sizeof h);
#endif
  if (HEFF_LIKELY((h & ~((uint64_t)0xff00 << 48)) == (1u | (uint64_t)K_ARR << 32 | (uint64_t)kind << 48)))
    return 1;
#ifdef HEFF_THREADS
  if (heff_shared((uint32_t)h)) return HEFF_ARR_KIND(r) == kind && heff_unshare(&r->h);
  return heff_owned((uint32_t)h) && HEFF_ARR_KIND(r) == kind && heff_own_alone(&r->h);
#else
  return 0;
#endif
#else
  return HEFF_ARR_KIND(r) == kind && heff_alone(&r->h);
#endif
}

// (element `k` as a `V` counted: a flat one boxed)
HEFF_FN V heff_arr_get(Arr *r, int64_t k) {
  switch (HEFF_ARR_KIND(r)) {
  case HEFF_ARR_F64: return heff_box_f64(HEFF_ARR_AT(r, double)[k]);
  case HEFF_ARR_I64: return heff_box_i64(HEFF_ARR_AT(r, int64_t)[k]);
  case HEFF_ARR_U64: return heff_box_u64(HEFF_ARR_AT(r, uint64_t)[k]);
  case HEFF_ARR_I32: return heff_box_i32(HEFF_ARR_AT(r, int32_t)[k]);
  case HEFF_ARR_U32: return heff_box_u32(HEFF_ARR_AT(r, uint32_t)[k]);
  case HEFF_ARR_I16: return heff_box_i16(HEFF_ARR_AT(r, int16_t)[k]);
  case HEFF_ARR_U16: return heff_box_u16(HEFF_ARR_AT(r, uint16_t)[k]);
  case HEFF_ARR_I8: return heff_box_i8(HEFF_ARR_AT(r, int8_t)[k]);
  case HEFF_ARR_U8: return heff_box_u8(HEFF_ARR_AT(r, uint8_t)[k]);
  case HEFF_ARR_F32: return heff_box_f32(HEFF_ARR_AT(r, float)[k]);
  default: return heff_dup(r->a[k]);
  }
}

// (`x`, consumed, stored at `k` as the array keeps it: what was there
// not dropped)
HEFF_FN void heff_arr_put(Arr *r, int64_t k, V x) {
  switch (HEFF_ARR_KIND(r)) {
  case HEFF_ARR_F64: HEFF_ARR_AT(r, double)[k] = heff_unbox_f64(x); return;
  case HEFF_ARR_I64: HEFF_ARR_AT(r, int64_t)[k] = heff_unbox_i64(x); return;
  case HEFF_ARR_U64: HEFF_ARR_AT(r, uint64_t)[k] = heff_unbox_u64(x); return;
  case HEFF_ARR_I32: HEFF_ARR_AT(r, int32_t)[k] = heff_unbox_i32(x); return;
  case HEFF_ARR_U32: HEFF_ARR_AT(r, uint32_t)[k] = heff_unbox_u32(x); return;
  case HEFF_ARR_I16: HEFF_ARR_AT(r, int16_t)[k] = heff_unbox_i16(x); return;
  case HEFF_ARR_U16: HEFF_ARR_AT(r, uint16_t)[k] = heff_unbox_u16(x); return;
  case HEFF_ARR_I8: HEFF_ARR_AT(r, int8_t)[k] = heff_unbox_i8(x); return;
  case HEFF_ARR_U8: HEFF_ARR_AT(r, uint8_t)[k] = heff_unbox_u8(x); return;
  case HEFF_ARR_F32: HEFF_ARR_AT(r, float)[k] = heff_unbox_f32(x); return;
  default: r->a[k] = x; return;
  }
}

// (how an array built of `V`s keeps them, by one of them: flat if it is
// a `Float64`'s box)
HEFF_FN unsigned heff_arr_kind_of(V x) {
  return IS_OBJ(x) && OBJ(x)->kind == K_FLT ? HEFF_ARR_F64 : HEFF_ARR_V;
}

// (whether the array keeps its elements as one built of `x` would: a
// `map` of it may write each element where it read it, of the same
// kind (heff.compile.arrayloops))
HEFF_FAST V heff_arrayKeepsAs_lent(V a, V x, int give) {
  V b = heff_bool(HEFF_ARR_KIND((Arr *)a) == heff_arr_kind_of(x));
  HEFF_GIVEN(give, 0, a);
  HEFF_GIVEN(give, 1, x);
  return b;
}
HEFF_FN V heff_arrayKeepsAs(V a, V x) { return heff_arrayKeepsAs_lent(a, x, 3); }

// (`r`'s elements from `from`, `n` of them, put at `at` of `s`, each
// counted: as `s` keeps them, if it keeps them otherwise)
HEFF_FN void heff_arr_move(Arr *s, int64_t at, Arr *r, int64_t from, int64_t n) {
  if (HEFF_ARR_KIND(s) == HEFF_ARR_KIND(r)) {
    if (HEFF_ARR_KIND(r) == HEFF_ARR_V)
      for (int64_t j = 0; j < n; j++) s->a[at + j] = heff_dup(r->a[from + j]);
    else memcpy((char *)s->a + at * heff_arr_width[HEFF_ARR_KIND(r)],
                (char *)r->a + from * heff_arr_width[HEFF_ARR_KIND(r)],
                (size_t)n * heff_arr_width[HEFF_ARR_KIND(r)]);
  } else
    for (int64_t j = 0; j < n; j++) heff_arr_put(s, at + j, heff_arr_get(r, from + j));
}

// (a copy of the array `a`, held elsewhere too: `a` counted down)
HEFF_FN __attribute__((noinline)) Arr *heff_arr_copy(V a) {
  Arr *r = (Arr *)a;
  Arr *s = heff_arr_alloc(r->n, HEFF_ARR_KIND(r));
  heff_arr_move(s, 0, r, 0, r->n);
  heff_drop(a);
  return s;
}

// (the bits of the room grown to, to hold `need` elements: the power of
// 2 at least `need`, at least 4)
HEFF_FN unsigned heff_arr_room(int64_t need) {
  if (need > HEFF_ARR_MAX) heff_fail("out of memory");
  unsigned e = 2;
  while (((int64_t)1 << e) < need) e++;
  return e;
}

// (an array held only here, its room made 2 to the `e`, at least its
// length: in place where the system gave both blocks (`realloc`), else
// moved to a block of the allocator's, its own given back)
HEFF_FN __attribute__((noinline)) Arr *heff_arr_regrow(Arr *r, unsigned e) {
  size_t w = heff_arr_width[HEFF_ARR_KIND(r)];
  size_t was = heff_arr_bytes(r), now = sizeof(Arr) + ((size_t)1 << e) * w;
  Arr *g;
  if ((was + 7) / 8 > SMALL_MAX / 8 && (now + 7) / 8 > SMALL_MAX / 8) {
    HEFF_COUNTED((now + 7) / 8);
    g = realloc(r, now);
    if (!g) heff_fail("out of memory");
  } else {
    g = heff_obj_alloc(now);
    memcpy(g, r, sizeof(Arr) + (size_t)r->n * w);
    heff_obj_free(r, was);
  }
  g->h.tag = (uint16_t)(HEFF_ARR_KIND(g) | e << HEFF_ARR_ROOM);
  return g;
}

// (a copy of the array `a`, held elsewhere too or kept otherwise than
// `kind` says, kept so, its room 2 to the `e`: `a` counted down)
HEFF_FN __attribute__((noinline)) Arr *heff_arr_fresh(V a, unsigned e, unsigned kind) {
  Arr *r = (Arr *)a;
  Arr *s = heff_arr_alloc((int64_t)1 << e, kind);
  s->n = r->n;
  s->h.tag = (uint16_t)(kind | e << HEFF_ARR_ROOM);
  heff_arr_move(s, 0, r, 0, r->n);
  heff_drop(a);
  return s;
}

HEFF_FAST V heff_arrayLength_lent(V a, int give) {
  V n = MK_INT(((Arr *)a)->n);
  HEFF_GIVEN(give, 0, a);
  return n;
}
HEFF_FN V heff_arrayLength(V a) { return heff_arrayLength_lent(a, 1); }

// (the element at `i`, a `V`; out of range, abandoned)
HEFF_FAST V heff_arrayIndex_lent(V a, V i, int give) {
  Arr *r = (Arr *)a;
  if (!heff_arr_in(r, i)) heff_arr_out();
  int64_t k = INT_OF(i);
  V x = HEFF_ARR_KIND(r) == HEFF_ARR_V ? heff_dup(r->a[k]) : heff_arr_get(r, k);
  HEFF_GIVEN(give, 0, a);
  return x;
}
HEFF_FN V heff_arrayIndex(V a, V i) { return heff_arrayIndex_lent(a, i, 3); }

// (... not counted, of an array of `V`s -- an `Int`'s never flat: the
// element lent where the array is, which holds it)
HEFF_FAST V heff_arrayPeek(V a, V i) {
  Arr *r = (Arr *)a;
  if (!heff_arr_in(r, i)) heff_arr_out();
  return r->a[INT_OF(i)];
}

// (... read as a number, where the program knows it is one: the
// element as the array keeps it, flat or a `V` -- an array of `Float64`s
// always flat (above))
HEFF_FAST double heff_arrayIndex_f64_lent(V a, V i, int give) {
  Arr *r = (Arr *)a;
  if (!heff_arr_in(r, i)) heff_arr_out();
  double x = HEFF_ARR_AT(r, double)[INT_OF(i)];
  HEFF_GIVEN(give, 0, a);
  return x;
}
HEFF_FAST double heff_arrayIndex_f64(V a, V i) { return heff_arrayIndex_f64_lent(a, i, 3); }

#define HEFF_ARR_INDEX(S, T, K)                                                \
  HEFF_FAST T heff_arrayIndex_##S##_lent(V a, V i, int give) {                 \
    Arr *r = (Arr *)a;                                                         \
    if (!heff_arr_in(r, i)) heff_arr_out();                                    \
    int64_t k = INT_OF(i);                                                     \
    T x = HEFF_ARR_KIND(r) == K ? HEFF_ARR_AT(r, T)[k] : heff_peek_##S(r->a[k]);       \
    HEFF_GIVEN(give, 0, a);                                                    \
    return x;                                                                  \
  }                                                                            \
  HEFF_FAST T heff_arrayIndex_##S(V a, V i) { return heff_arrayIndex_##S##_lent(a, i, 3); } \
  HEFF_FAST T heff_arrayIndexInAny_##S##_lent(V a, V i, int give) {           \
    Arr *r = (Arr *)a;                                                         \
    int64_t k = INT_OF(i);                                                     \
    T x = HEFF_ARR_KIND(r) == K ? HEFF_ARR_AT(r, T)[k] : heff_peek_##S(r->a[k]);       \
    HEFF_GIVEN(give, 0, a);                                                    \
    return x;                                                                  \
  }                                                                            \
  HEFF_FAST T heff_arrayIndexInAny_##S(V a, V i) { return heff_arrayIndexInAny_##S##_lent(a, i, 3); }
// (... known in range, where a loop checked its index once
// (heff.compile.bounds), or a test found it so (heff.compile.tested): the
// index a word, at least 0, below the length -- a fixed-width number's,
// `arrayIndexInAny_i64` above, how the array keeps it still looked at)
HEFF_FAST V heff_arrayIndexIn_lent(V a, V i, int give) {
  Arr *r = (Arr *)a;
  int64_t k = INT_OF(i);
  V x = HEFF_ARR_KIND(r) == HEFF_ARR_V ? heff_dup(r->a[k]) : heff_arr_get(r, k);
  HEFF_GIVEN(give, 0, a);
  return x;
}
HEFF_FAST V heff_arrayIndexIn(V a, V i) { return heff_arrayIndexIn_lent(a, i, 3); }
HEFF_FAST V heff_arrayPeekIn(V a, V i) { return ((Arr *)a)->a[INT_OF(i)]; }
HEFF_FAST double heff_arrayIndexIn_f64_lent(V a, V i, int give) {
  double x = HEFF_ARR_AT((Arr *)a, double)[INT_OF(i)];
  HEFF_GIVEN(give, 0, a);
  return x;
}
HEFF_FAST double heff_arrayIndexIn_f64(V a, V i) { return heff_arrayIndexIn_f64_lent(a, i, 3); }
// (... of a fixed-width number, the array checked once to keep them
// flat (`heff_arrayKeeps_i64`): read as it keeps them, not looked at)
#define HEFF_ARR_INDEX_IN(S, T, K)                                             \
  HEFF_FAST T heff_arrayIndexIn_##S##_lent(V a, V i, int give) {               \
    T x = HEFF_ARR_AT((Arr *)a, T)[INT_OF(i)];                                 \
    HEFF_GIVEN(give, 0, a);                                                    \
    return x;                                                                  \
  }                                                                            \
  HEFF_FAST T heff_arrayIndexIn_##S(V a, V i) { return heff_arrayIndexIn_##S##_lent(a, i, 3); } \
  HEFF_FAST V heff_arrayKeeps_##S##_lent(V a, int give) {                      \
    V b = heff_bool(HEFF_ARR_KIND(((Arr *)a)) == K);                                   \
    HEFF_GIVEN(give, 0, a);                                                    \
    return b;                                                                  \
  }                                                                            \
  HEFF_FAST V heff_arrayKeeps_##S(V a) { return heff_arrayKeeps_##S##_lent(a, 1); }
#define HEFF_ARR_INDEXES(S, T, K) HEFF_ARR_INDEX(S, T, K) HEFF_ARR_INDEX_IN(S, T, K)
HEFF_ARR_INDEXES(i64, int64_t, HEFF_ARR_I64)
HEFF_ARR_INDEXES(u64, uint64_t, HEFF_ARR_U64)
HEFF_ARR_INDEXES(i32, int32_t, HEFF_ARR_I32)
HEFF_ARR_INDEXES(u32, uint32_t, HEFF_ARR_U32)
HEFF_ARR_INDEXES(i16, int16_t, HEFF_ARR_I16)
HEFF_ARR_INDEXES(u16, uint16_t, HEFF_ARR_U16)
HEFF_ARR_INDEXES(i8, int8_t, HEFF_ARR_I8)
HEFF_ARR_INDEXES(u8, uint8_t, HEFF_ARR_U8)
HEFF_ARR_INDEXES(f32, float, HEFF_ARR_F32)
// (... of `Float64`s: whether it keeps them flat, as one built of them
// does, if it has an element (heff.compile.arrayloops))
HEFF_FAST V heff_arrayKeeps_f64_lent(V a, int give) {
  V b = heff_bool(HEFF_ARR_KIND((Arr *)a) == HEFF_ARR_F64);
  HEFF_GIVEN(give, 0, a);
  return b;
}
HEFF_FAST V heff_arrayKeeps_f64(V a) { return heff_arrayKeeps_f64_lent(a, 1); }

// (`set` but where the array is held only here and keeps `x` as it is:
// out of range, the array as it is; held elsewhere too, a copy, `x` at
// `i` in it)
#ifdef HEFF_THREADS
// (a search, from what a cell holds, for the slot holding `want`: down
// through owned objects held by what holds them there alone, and by the
// log -- those the body counted up (`TOUCHED`), and, where `any` is,
// those it did not, `left` of them at most)
typedef struct {
  HeffStack s;
  V want, from;
  V *at;
  V parent;
  int64_t left;
  int any;
} HeffOwnSeek;

HEFF_FN void heff_own_seek(HeffOwnSeek *k, V *at) {
  V v = *at;
  if (k->at || !IS_OBJ(v) || !v) return;
  if (v == k->want) {
    k->at = at;
    k->parent = k->from;
    return;
  }
  uint32_t rc = heff_rc(OBJ(v));
  if (!heff_owned(rc)) return;
  if (rc & HEFF_TOUCHED_BIT) {
    if (HEFF_COUNT(rc) != 2) return;
  } else if (!k->any || HEFF_COUNT(rc) != 1 || k->left-- <= 0) return;
  heff_stack_push(&k->s, v);
}

// (whether the slot `at` is one of the array's elements)
static inline int heff_own_within(V *at, Arr *r) {
  return HEFF_ARR_KIND(r) == HEFF_ARR_V && at >= r->a && at < r->a + r->n;
}

// (whether `r` is what a cell the body read holds, or is held there by a
// way from it nothing else holds -- but the log, and the cell -- so that
// nothing the body or another has sees it written in place: the way
// counted, each object on it held once there, or twice, once by the log,
// the body holding none; what holds the array then itself none the body
// writes in place, nor the array what holds one: kept by the log, to
// put back)
HEFF_FN int heff_own_found(HeffOwnLog *g, Arr *r) {
  for (int any = 0; any < 2; any++)
    for (int64_t j = 0; j < g->nr; j++) {
      V v = g->roots[j].v;
      if (!IS_OBJ(v) || !v || !heff_owned(heff_rc(OBJ(v)))) continue;
      V *at = NULL;
      V parent = 0;
      if (v == (V)r) {
        if (any) continue;
      } else {
        if (HEFF_COUNT(heff_rc(OBJ(v))) != 2) continue;
        HeffOwnSeek k = {{0}, (V)r, 0, NULL, 0, 256, any};
        heff_stack_push(&k.s, v);
        while (k.s.n && !k.at) {
          V o = k.s.v[--k.s.n];
          k.from = o;
          HEFF_EACH_SLOT(o, heff_own_seek, &k);
        }
        free(k.s.v);
        if (!k.at) continue;
        at = k.at;
        parent = k.parent;
      }
      for (int64_t i = 0; i < g->na; i++)
        if ((V)g->arrs[i].r == parent || (g->arrs[i].at && heff_own_within(g->arrs[i].at, r)))
          return 0;
      g->arrs = heff_own_room(g->arrs, g->na, &g->ca, sizeof(HeffOwnArr));
      g->arrs[g->na++] = (HeffOwnArr){r, at, j};
      return 1;
    }
  return 0;
}

// (whether the array, counted up by the body and held by it once, and
// once by what holds it in what a cell the body read holds, may be
// written in place at `k` (`heff_own_found`): what is there then kept
// by the log -- the reference, where the array keeps `V`s, else its
// bits -- to be put back where the cell is to hold what it held (the
// body failed, or did not write the cell))
HEFF_FN __attribute__((noinline)) int heff_own_set(Arr *r, int64_t k) {
  HeffOwnLog *g = heff_own_log;
  uint32_t rc = r->h.rc;
  if (!g || !(rc & HEFF_TOUCHED_BIT) || HEFF_COUNT(rc) != 3) return 0;
  int64_t j = 0;
  while (j < g->na && g->arrs[j].r != r) j++;
  if (j == g->na && !heff_own_found(g, r)) return 0;
  g->sets = heff_own_room(g->sets, g->ns, &g->cs, sizeof(HeffOwnSet));
  HeffOwnSet *e = &g->sets[g->ns++];
  e->r = r;
  e->i = k;
  e->old = 0;
  unsigned w = heff_arr_width[HEFF_ARR_KIND(r)];
  memcpy(&e->old, (char *)r->a + k * w, w);
  return 1;
}
#endif

HEFF_FN __attribute__((noinline)) V heff_arr_set_slow(V a, V i, V x) {
  Arr *r = (Arr *)a;
  if (!heff_arr_in(r, i)) {
    heff_drop(i);
    heff_drop(x);
    return a;
  }
  int64_t k = INT_OF(i);
#ifdef HEFF_THREADS
  if (heff_owned(heff_rc(&r->h)) && heff_own_set(r, k)) {
    heff_arr_put(r, k, x);
    return a;
  }
#endif
  if (!heff_unique(a)) r = heff_arr_copy(a);
  if (HEFF_ARR_KIND(r) == HEFF_ARR_V) heff_drop(r->a[k]);
  heff_arr_put(r, k, x);
  return (V)r;
}

// (`x` at `i`: in place, the array held only here; out of range, the
// array as it is)
HEFF_FAST V heff_arraySet(V a, V i, V x) {
  Arr *r = (Arr *)a;
  if (HEFF_LIKELY(heff_arr_in(r, i) && heff_arr_mine(r, HEFF_ARR_V))) {
    V old = r->a[INT_OF(i)];
    r->a[INT_OF(i)] = x;
    heff_drop(old);
    return a;
  }
  return heff_arr_set_slow(a, i, x);
}

// (... `x` a number, where the program knows it is one)
#define HEFF_ARR_SET(S, T, K)                                                  \
  HEFF_FAST V heff_arraySet_##S(V a, V i, T x) {                              \
    Arr *r = (Arr *)a;                                                         \
    if (HEFF_LIKELY(heff_arr_in(r, i) && heff_arr_mine(r, K))) {             \
      HEFF_ARR_AT(r, T)[INT_OF(i)] = x;                                        \
      return a;                                                                \
    }                                                                          \
    return heff_arr_set_slow(a, i, heff_box_##S(x));                           \
  }
HEFF_ARR_SET(f64, double, HEFF_ARR_F64)
HEFF_ARR_SET(i64, int64_t, HEFF_ARR_I64)
HEFF_ARR_SET(u64, uint64_t, HEFF_ARR_U64)
HEFF_ARR_SET(i32, int32_t, HEFF_ARR_I32)
HEFF_ARR_SET(u32, uint32_t, HEFF_ARR_U32)
HEFF_ARR_SET(i16, int16_t, HEFF_ARR_I16)
HEFF_ARR_SET(u16, uint16_t, HEFF_ARR_U16)
HEFF_ARR_SET(i8, int8_t, HEFF_ARR_I8)
HEFF_ARR_SET(u8, uint8_t, HEFF_ARR_U8)
HEFF_ARR_SET(f32, float, HEFF_ARR_F32)

// A loop that threads an array through `set`, using it only so, checks
// it held only there once, where it is entered (`heff_arrayOwn_f64`):
// a copy where it is not, its elements kept as the loop's `set`s give
// them; held only there, it stays so through the loop, and each `set`
// writes in place, unchecked (`heff_arraySetOwned_f64`) -- the array the
// same each round, which C can then see.

// (a copy of the array, its elements kept as `kind` says: `a` counted
// down)
HEFF_FN __attribute__((noinline)) V heff_arr_own_slow(V a, unsigned kind) {
  Arr *r = (Arr *)a;
  Arr *s = heff_arr_alloc(r->n, kind);
  heff_arr_move(s, 0, r, 0, r->n);
  heff_drop(a);
  return (V)s;
}

// (the array held only here: it, or a copy of it)
HEFF_FAST V heff_arrayOwn(V a) {
  if (HEFF_LIKELY(heff_unique(a))) return a;
  return (V)heff_arr_copy(a);
}

// (`x` at `i` of an array held only here, known in range
// (heff.compile.bounds): written here where the array keeps `V`s, the
// way of each other kind only where it is another)
HEFF_FAST V heff_arraySetOwnedIn(V a, V i, V x) {
  Arr *r = (Arr *)a;
  int64_t k = INT_OF(i);
  if (HEFF_LIKELY(HEFF_ARR_KIND(r) == HEFF_ARR_V)) {
    V old = r->a[k];
    r->a[k] = x;
    heff_drop(old);
  } else heff_arr_put(r, k, x);
  return a;
}

// (... out of range, the array as it is)
HEFF_FAST V heff_arraySetOwned(V a, V i, V x) {
  Arr *r = (Arr *)a;
  if (!HEFF_LIKELY(heff_arr_in(r, i))) {
    heff_drop(i);
    heff_drop(x);
    return a;
  }
  return heff_arraySetOwnedIn(a, i, x);
}

// (... keeping its elements as `T`s, where the program knows them so)
#define HEFF_ARR_OWN(S, T, K)                                                  \
  HEFF_FAST V heff_arrayOwn_##S(V a) {                                         \
    if (HEFF_LIKELY(heff_arr_mine((Arr *)a, K))) return a;                     \
    return heff_arr_own_slow(a, K);                                            \
  }                                                                            \
  HEFF_FAST V heff_arraySetOwned_##S(V a, V i, T x) {                          \
    Arr *r = (Arr *)a;                                                         \
    if (HEFF_LIKELY(heff_arr_in(r, i))) HEFF_ARR_AT(r, T)[INT_OF(i)] = x;      \
    else heff_drop(i);                                                         \
    return a;                                                                  \
  }                                                                            \
  HEFF_FAST V heff_arraySetOwnedIn_##S(V a, V i, T x) {                        \
    HEFF_ARR_AT((Arr *)a, T)[INT_OF(i)] = x;                                   \
    return a;                                                                  \
  }
HEFF_ARR_OWN(f64, double, HEFF_ARR_F64)
HEFF_ARR_OWN(i64, int64_t, HEFF_ARR_I64)
HEFF_ARR_OWN(u64, uint64_t, HEFF_ARR_U64)
HEFF_ARR_OWN(i32, int32_t, HEFF_ARR_I32)
HEFF_ARR_OWN(u32, uint32_t, HEFF_ARR_U32)
HEFF_ARR_OWN(i16, int16_t, HEFF_ARR_I16)
HEFF_ARR_OWN(u16, uint16_t, HEFF_ARR_U16)
HEFF_ARR_OWN(i8, int8_t, HEFF_ARR_I8)
HEFF_ARR_OWN(u8, uint8_t, HEFF_ARR_U8)
HEFF_ARR_OWN(f32, float, HEFF_ARR_F32)

// (`n` elements, each `x`: of `V`s, counted once for each -- flat if
// `x` is a `Float64`)
HEFF_FN V heff_arrayReplicate(V n, V x) {
  int64_t m = heff_arr_count(n);
  if (m == 0) {
    heff_drop(x);
    return (V)heff_arr_new(0);
  }
  Arr *r = heff_arr_alloc(m, heff_arr_kind_of(x));
  if (HEFF_ARR_KIND(r) == HEFF_ARR_F64) {
    double d = heff_unbox_f64(x);
    for (int64_t k = 0; k < m; k++) HEFF_ARR_AT(r, double)[k] = d;
    return (V)r;
  }
  for (int64_t k = 0; k < m; k++) r->a[k] = x;
  if (IS_OBJ(x)) {
    uint32_t rc = heff_rc(OBJ(x));
    if (heff_mine(rc)) OBJ(x)->rc = rc + (uint32_t)(m - 1);
#ifdef HEFF_THREADS
    else if (heff_shared(rc)) __atomic_fetch_add(&OBJ(x)->rc, (uint32_t)(m - 1), __ATOMIC_RELAXED);
    else if (heff_owned(rc)) heff_own_dup(OBJ(x), (uint32_t)(m - 1));
#endif
  }
  return (V)r;
}

// (... of a number, flat)
#define HEFF_ARR_REPLICATE(S, T, K)                                            \
  static V heff_arrayReplicate_##S(V n, T x) {                                 \
    int64_t m = heff_arr_count(n);                                             \
    Arr *r = heff_arr_alloc(m, K);                                             \
    for (int64_t k = 0; k < m; k++) HEFF_ARR_AT(r, T)[k] = x;                  \
    return (V)r;                                                               \
  }
HEFF_ARR_REPLICATE(f64, double, HEFF_ARR_F64)
HEFF_ARR_REPLICATE(i64, int64_t, HEFF_ARR_I64)
HEFF_ARR_REPLICATE(u64, uint64_t, HEFF_ARR_U64)
HEFF_ARR_REPLICATE(i32, int32_t, HEFF_ARR_I32)
HEFF_ARR_REPLICATE(u32, uint32_t, HEFF_ARR_U32)
HEFF_ARR_REPLICATE(i16, int16_t, HEFF_ARR_I16)
HEFF_ARR_REPLICATE(u16, uint16_t, HEFF_ARR_U16)
HEFF_ARR_REPLICATE(i8, int8_t, HEFF_ARR_I8)
HEFF_ARR_REPLICATE(u8, uint8_t, HEFF_ARR_U8)
HEFF_ARR_REPLICATE(f32, float, HEFF_ARR_F32)

HEFF_FN V heff_arrayGenerate(V n, V f) {
  int64_t m = heff_arr_count(n);
  if (m == 0) {
    heff_drop(f);
    return (V)heff_arr_new(0);
  }
  V x = heff_tr(heff_app1(heff_dup(f), MK_INT(0)));
  Arr *r = heff_arr_alloc(m, heff_arr_kind_of(x));
  heff_arr_put(r, 0, x);
  for (int64_t k = 1; k < m; k++) heff_arr_put(r, k, heff_tr(heff_app1(heff_dup(f), MK_INT(k))));
  heff_drop(f);
  return (V)r;
}

// (... of a function known to give numbers of one type, `T`s
// (heff.compile.generate): flat, each unboxed as it comes)
#define HEFF_ARR_GENERATE(S, T, K)                                             \
  HEFF_FN V heff_arrayGenerate_##S(V n, V f) {                                 \
    int64_t m = heff_arr_count(n);                                             \
    Arr *r = heff_arr_alloc(m, K);                                             \
    for (int64_t k = 0; k < m; k++) {                                          \
      V x = heff_tr(heff_app1(heff_dup(f), MK_INT(k)));                        \
      HEFF_ARR_AT(r, T)[k] = heff_unbox_##S(x);                                \
    }                                                                          \
    heff_drop(f);                                                              \
    return (V)r;                                                               \
  }
HEFF_ARR_GENERATE(f64, double, HEFF_ARR_F64)
HEFF_ARR_GENERATE(i64, int64_t, HEFF_ARR_I64)
HEFF_ARR_GENERATE(u64, uint64_t, HEFF_ARR_U64)
HEFF_ARR_GENERATE(i32, int32_t, HEFF_ARR_I32)
HEFF_ARR_GENERATE(u32, uint32_t, HEFF_ARR_U32)
HEFF_ARR_GENERATE(i16, int16_t, HEFF_ARR_I16)
HEFF_ARR_GENERATE(u16, uint16_t, HEFF_ARR_U16)
HEFF_ARR_GENERATE(i8, int8_t, HEFF_ARR_I8)
HEFF_ARR_GENERATE(u8, uint8_t, HEFF_ARR_U8)
HEFF_ARR_GENERATE(f32, float, HEFF_ARR_F32)

// (a list's cell's element, a `V` counted: a flat one (#64) boxed)
HEFF_FN V heff_arrayFromList(V l) {
  int64_t n = 0;
  for (V c = l; heff_tag_of(c) == TAG_Cons; c = heff_field(c, 1)) n++;
  if (n == 0) {
    heff_drop(l);
    return (V)heff_arr_new(0);
  }
  V x = heff_tget_v(l, 0);
  Arr *r = heff_arr_alloc(n, heff_arr_kind_of(x));
  heff_arr_put(r, 0, x);
  int64_t k = 1;
  for (V c = heff_field(l, 1); heff_tag_of(c) == TAG_Cons; c = heff_field(c, 1))
    heff_arr_put(r, k++, heff_tget_v(c, 0));
  heff_drop(l);
  return (V)r;
}

HEFF_FN V heff_arrayToList(V a) {
  Arr *r = (Arr *)a;
  V l = NTAG(TAG_Nil);
  for (int64_t k = r->n - 1; k >= 0; k--) {
    V f[2] = { heff_arr_get(r, k), l };
    l = heff_tag_n(TAG_Cons, 2, f);
  }
  heff_drop(a);
  return l;
}

// (the elements from `i` up to `j`, as a string's slice (`strSlice`):
// each clamped to them, a negative one counted from the end)
HEFF_FN V heff_arraySlice(V a, V i, V j) {
  Arr *r = (Arr *)a;
  int64_t n = r->n, b = INT_OF(i), e = INT_OF(j);
  if (!IS_INT(i)) b = ((Big *)i)->neg ? 0 : n;
  else if (b < 0) b = b + n < 0 ? 0 : b + n;
  else if (b > n) b = n;
  if (!IS_INT(j)) e = ((Big *)j)->neg ? 0 : n;
  else if (e < 0) e = e + n < 0 ? 0 : e + n;
  else if (e > n) e = n;
  heff_drop(i);
  heff_drop(j);
  if (b == 0 && e == n) return a;
  int64_t m = e > b ? e - b : 0;
  Arr *s = heff_arr_alloc(m, HEFF_ARR_KIND(r));
  heff_arr_move(s, 0, r, b, m);
  heff_drop(a);
  return (V)s;
}

// (one array's elements, then another's: kept as theirs are, or -- one
// flat and the other of `V`s -- flat, the other's put so.  The first held
// only here, the second's are put after its own, in its room, grown if
// there is too little; the second held only here too, its elements are
// moved over, not counted)
HEFF_FN V heff_arrayAppend(V a, V b) {
  Arr *r = (Arr *)a, *t = (Arr *)b;
  if (t->n == 0) { heff_drop(b); return a; }
  if (r->n == 0 && !(heff_alone(&r->h) && heff_arr_cap(r) >= t->n)) { heff_drop(a); return b; }
  unsigned kind = HEFF_ARR_KIND(r) != HEFF_ARR_V ? HEFF_ARR_KIND(r) : HEFF_ARR_KIND(t);
  int64_t k = r->n, n = r->n + t->n;
  Arr *s;
  if (heff_arr_mine(r, kind)) s = n > heff_arr_cap(r) ? heff_arr_regrow(r, heff_arr_room(n)) : r;
  else {
    s = heff_arr_alloc(n, kind);
    heff_arr_move(s, 0, r, 0, k);
    heff_drop(a);
  }
  if (HEFF_ARR_KIND(t) == kind && heff_alone(&t->h)) {
    size_t w = heff_arr_width[kind];
    memcpy((char *)s->a + (size_t)k * w, t->a, (size_t)t->n * w);
    heff_obj_free(t, heff_arr_bytes(t));
  } else {
    heff_arr_move(s, k, t, 0, t->n);
    heff_drop(b);
  }
  s->n = n;
  return (V)s;
}

// (a new array of `m`, kept as `kind` says: `a`'s elements before `k`,
// then, `put` places on, those from `k` and `skip` past it -- moved over
// by a copy of their bytes where nothing else holds `a`, its cell given
// back, and counted otherwise, `a` counted down)
HEFF_FN Arr *heff_arr_spread(V a, int64_t k, int64_t skip, int64_t put, int64_t m, unsigned kind) {
  Arr *r = (Arr *)a;
  int64_t rest = r->n - k - skip;
  Arr *s = heff_arr_alloc(m, kind);
  if (HEFF_ARR_KIND(r) == kind && heff_alone(&r->h)) {
    size_t w = heff_arr_width[kind];
    memcpy(s->a, r->a, (size_t)k * w);
    memcpy((char *)s->a + (size_t)(k + put) * w, (char *)r->a + (size_t)(k + skip) * w,
           (size_t)rest * w);
    heff_obj_free(r, heff_arr_bytes(r));
    return s;
  }
  heff_arr_move(s, 0, r, 0, k);
  heff_arr_move(s, k + put, r, k + skip, rest);
  heff_drop(a);
  return s;
}

// (`x` put in at `i`, clamped to 0 up to the length, the elements from
// there on one further on)
HEFF_FN V heff_arrayInsertAt(V a, V i, V x) {
  Arr *r = (Arr *)a;
  int64_t n = r->n, k = INT_OF(i);
  if (!IS_INT(i)) k = ((Big *)i)->neg ? 0 : n;
  else if (k < 0) k = 0;
  else if (k > n) k = n;
  heff_drop(i);
  unsigned kind = n == 0 ? heff_arr_kind_of(x) : HEFF_ARR_KIND(r);
  Arr *s;
  if (n < heff_arr_cap(r) && heff_arr_mine(r, kind)) {
    size_t w = heff_arr_width[kind];
    memmove((char *)r->a + (size_t)(k + 1) * w, (char *)r->a + (size_t)k * w, (size_t)(n - k) * w);
    r->n = n + 1;
    s = r;
  } else s = heff_arr_spread(a, k, 0, 1, n + 1, kind);
  heff_arr_put(s, k, x);
  return (V)s;
}

// (the element at `i` taken out, those after it one nearer: moved down
// in place where the array is held only here, its room kept, else a
// copy; out of range, the array as it is.  Room is kept as a power of 2,
// not as the length, which this lowers: so an array whose room is its
// length is given a power of 2 first, the one at least its length -- its
// own, if its length is one, else by `heff_arr_regrow`.  It never
// shrinks the room)
HEFF_FN __attribute__((noinline)) V heff_arr_remove_slow(V a, V i) {
  Arr *r = (Arr *)a;
  if (!heff_arr_in(r, i)) {
    heff_drop(i);
    return a;
  }
  int64_t n = r->n, k = INT_OF(i);
  if (!heff_alone(&r->h)) return (V)heff_arr_spread(a, k, 1, 0, n - 1, HEFF_ARR_KIND(r));
  if (HEFF_ARR_KIND(r) == HEFF_ARR_V) heff_drop(r->a[k]);
  if (!(r->h.tag >> HEFF_ARR_ROOM)) {
    unsigned e = heff_arr_room(n);
    if ((int64_t)1 << e == n) r->h.tag = (uint16_t)(HEFF_ARR_KIND(r) | e << HEFF_ARR_ROOM);
    else r = heff_arr_regrow(r, e);
  }
  size_t w = heff_arr_width[HEFF_ARR_KIND(r)];
  memmove((char *)r->a + (size_t)k * w, (char *)r->a + (size_t)(k + 1) * w, (size_t)(n - k - 1) * w);
  r->n = n - 1;
  return (V)r;
}

// (... the path where it is the last element of an array held only here
// whose room is a power of 2 already: the length lowered)
HEFF_FAST V heff_arrayRemoveAt(V a, V i) {
  Arr *r = (Arr *)a;
  if (r->n != 0 && i == MK_INT(r->n - 1) && (r->h.tag >> HEFF_ARR_ROOM) && heff_alone(&r->h)) {
    r->n--;
    if (HEFF_ARR_KIND(r) == HEFF_ARR_V) heff_drop(r->a[r->n]);
    return a;
  }
  return heff_arr_remove_slow(a, i);
}

// (`x` after the last element: in the room after them where the array
// is held only here, grown where there is none; held elsewhere too, a
// copy with room.  An array of no elements, of `V`s, is kept as `x`
// says, flat if it is a `Float64`)
HEFF_FN __attribute__((noinline)) V heff_arr_push_slow(V a, V x) {
  Arr *r = (Arr *)a;
  int64_t n = r->n;
  unsigned kind = n == 0 && HEFF_ARR_KIND(r) == HEFF_ARR_V ? heff_arr_kind_of(x) : HEFF_ARR_KIND(r);
  if (heff_arr_mine(r, kind)) {
    if (n == heff_arr_cap(r)) r = heff_arr_regrow(r, heff_arr_room(n + 1));
  } else r = heff_arr_fresh(a, heff_arr_room(n + 1), kind);
  heff_arr_put(r, n, x);
  r->n = n + 1;
  return (V)r;
}

// (... the path where there is room and the array, of `V`s, has an
// element -- so `x` is no `Float64`, which would make it flat)
HEFF_FAST V heff_arrayPush(V a, V x) {
  Arr *r = (Arr *)a;
  if (HEFF_LIKELY(r->n != 0 && r->n < heff_arr_cap(r) && heff_arr_mine(r, HEFF_ARR_V))) {
    r->a[r->n++] = x;
    return a;
  }
  return heff_arr_push_slow(a, x);
}

// (room for `k` more elements: grown in place where the array is held
// only here, else a copy with that room; fewer than none, none)
HEFF_FN V heff_arrayReserve(V a, V k) {
  Arr *r = (Arr *)a;
  int64_t more = heff_arr_count(k);
  heff_drop(k);
  int alone = heff_alone(&r->h);
  if (more == 0 || (alone && more <= heff_arr_cap(r) - r->n)) return a;
  int64_t need = r->n + more;
  if (alone) return (V)heff_arr_regrow(r, heff_arr_room(need));
  return (V)heff_arr_fresh(a, heff_arr_room(need), HEFF_ARR_KIND(r));
}

// Bytes
// ---------------------------------------------------------------------

// (`Bytes`, never changed once made: a string's `Str`, of
// the kind `K_BYT` -- dropped, shared with a thread and grown by an append
// as a string is, and shown as a binary, `b[...]`.  Their length, slice and
// equality are a string's; a byte is a `UInt8`, a word of its value)
HEFF_FN Str *heff_bytes_new(int64_t len) {
  Str *s = heff_str_new(len);
  s->h.kind = K_BYT;
  return s;
}

// (each that only reads its bytes with a `_lent` form, as a string's
// has: "Lent strings", above)
HEFF_FAST V heff_bytesLength_lent(V a, int give) { return heff_strLength_lent(a, give); }
HEFF_FN V heff_bytesLength(V a) { return heff_strLength(a); }

// (the byte at `i`; out of them, abandoned, as `bytes`'s `index` never
// asks)
HEFF_FAST V heff_bytesAt_lent(V a, V i, int give) {
  Str *x = (Str *)a;
  int64_t k = INT_OF(i);
  if (!IS_INT(i) || k < 0 || k >= x->len) return heff_abandon();
  V r = MK_INT(x->p[k]);
  HEFF_GIVEN(give, 0, a);
  return r;
}
HEFF_FN V heff_bytesAt(V a, V i) { return heff_bytesAt_lent(a, i, 1); }

HEFF_FN V heff_bytesSlice_lent(V a, V i, V j, int give) {
  V s = heff_strSlice_lent(a, i, j, give);
  OBJ(s)->kind = K_BYT;
  return s;
}
HEFF_FN V heff_bytesSlice(V a, V i, V j) { return heff_bytesSlice_lent(a, i, j, 1); }

HEFF_FN V heff_bytesAppend(V a, V b) { return heff_buf_append(a, b, K_BYT); }

// (a list's bytes, one after another: their length added up first, so
// that they are made once, each copied once)
HEFF_FN V heff_bytesConcat(V l) {
  int64_t n = 0;
  for (V c = l; heff_tag_of(c) == TAG_Cons; c = heff_field(c, 1)) n += ((Str *)heff_field(c, 0))->len;
  Str *s = heff_bytes_new(n);
  int64_t k = 0;
  for (V c = l; heff_tag_of(c) == TAG_Cons; c = heff_field(c, 1)) {
    Str *x = (Str *)heff_field(c, 0);
    if (x->len) memcpy(s->s + k, x->p, (size_t)x->len);
    k += x->len;
  }
  heff_drop(l);
  return (V)s;
}

HEFF_FAST V heff_bytesEq_lent(V a, V b, int give) { return heff_strEq_lent(a, b, give); }
HEFF_FN V heff_bytesEq(V a, V b) { return heff_strEq(a, b); }

HEFF_FN V heff_bytesFromList(V l) {
  int64_t n = 0;
  for (V c = l; heff_tag_of(c) == TAG_Cons; c = heff_field(c, 1)) n++;
  Str *s = heff_bytes_new(n);
  int64_t k = 0;
  for (V c = l; heff_tag_of(c) == TAG_Cons; c = heff_field(c, 1)) s->s[k++] = (uint8_t)INT_OF(heff_field(c, 0));
  heff_drop(l);
  return (V)s;
}

HEFF_FN V heff_bytesToList(V a) {
  Str *x = (Str *)a;
  V l = NTAG(TAG_Nil);
  for (int64_t k = x->len - 1; k >= 0; k--) {
    V f[2] = { MK_INT(x->p[k]), l };
    l = heff_tag_n(TAG_Cons, 2, f);
  }
  heff_drop(a);
  return l;
}

// (a string's bytes, as they are)
HEFF_FN V heff_bytesFromString(V a) {
  Str *x = (Str *)a, *s = heff_bytes_new(x->len);
  if (x->len) memcpy(s->s, x->p, (size_t)x->len);
  heff_drop(a);
  return (V)s;
}

// (a string of them, as they are: `bytesFromString` undone)
HEFF_FN V heff_bytesAsString(V a) {
  Str *x = (Str *)a;
  V s = heff_str_of(x->p, x->len);
  heff_drop(a);
  return s;
}

// (their text: what is not UTF-8 in them U+FFFD, as TextDecoder reads it)
HEFF_FN V heff_bytesToString(V a) {
  Str *x = (Str *)a;
  V s = heff_str_valid(x->p, x->len);
  heff_drop(a);
  return s;
}

// (what a binary's segment reads and writes, `b[x::16-little]`, as
// Erlang's do: an integer of `n` bits, 0 to 64, its two's complement,
// the most significant bit first -- or, little-endian (where the flags
// `f` have 1), its bytes the least significant first and then the `n %
// 8` bits left, the most significant -- read as signed where `f` has 2.
// `heff_bits_read` and `heff_bits_write` have them in the order they are
// written, `heff_bits_little` turns the one into the other: the three
// are the runtime's Zig's, declared above.)

// (the integer of `n` bits at bit `at` of `s`, as the flags `f` say)
HEFF_FN V heff_bits_int(const uint8_t *s, int64_t at, int64_t n, int64_t flags) {
  uint64_t u = heff_bits_read(s, at, n);
  if (flags & 1) u = heff_bits_little(u, n, 0);
  if ((flags & 2) && n > 0 && n < 64 && (u >> (n - 1)) & 1) return heff_int((int64_t)(u | (~(uint64_t)0 << n)));
  if ((flags & 2) && n == 64) return heff_int((int64_t)u);
  return heff_int_u64(u);
}

// (the integer `v`'s low `n` bits, as they are written)
HEFF_FN uint64_t heff_bits_of_int(V v, int64_t n, int64_t flags) {
  uint64_t u = heff_int_low64(v);
  if (n < 64) u &= ((uint64_t)1 << n) - 1;
  return (flags & 1) ? heff_bits_little(u, n, 1) : u;
}

// (`heff.elab.clauses` checks that it is there before it is read)
HEFF_FAST V heff_bytesIntAt_lent(V a, V o, V n, V f, int give) {
  Str *x = (Str *)a;
  int64_t at = INT_OF(o), bits = INT_OF(n);
  if (!IS_INT(o) || !IS_INT(n) || at < 0 || bits < 0 || bits > 64 || at + bits > x->len * 8) return heff_abandon();
  V r = heff_bits_int(x->p, at, bits, INT_OF(f));
  HEFF_GIVEN(give, 0, a);
  return r;
}
HEFF_FN V heff_bytesIntAt(V a, V o, V n, V f) { return heff_bytesIntAt_lent(a, o, n, f, 1); }

// (the integer `v`, its low `n` bits (a multiple of 8, up to 64), as
// bytes)
HEFF_FN V heff_bytesOfInt(V n, V f, V v) {
  int64_t bits = INT_OF(n);
  if (!IS_INT(n) || bits < 0 || bits > 64 || (bits & 7)) return heff_abandon();
  uint64_t w = heff_bits_of_int(v, bits, INT_OF(f));
  heff_drop(v);
  Str *s = heff_bytes_new(bits >> 3);
  heff_bits_write(s->s, 0, w, bits);
  return (V)s;
}

// (whether the bytes `b` are those of `a` at `o`)
HEFF_FAST V heff_bytesHasAt_lent(V a, V o, V b, int give) {
  Str *x = (Str *)a, *y = (Str *)b;
  int64_t at = INT_OF(o);
  int r = IS_INT(o) && at >= 0 && at <= x->len - y->len && (y->len == 0 || memcmp(x->p + at, y->p, (size_t)y->len) == 0);
  HEFF_GIVEN(give, 0, a);
  HEFF_GIVEN(give, 2, b);
  return heff_bool(r);
}
HEFF_FN V heff_bytesHasAt(V a, V o, V b) { return heff_bytesHasAt_lent(a, o, b, 5); }

// (where the bytes `n` are first in `a` from `i` on (from 0, `i` below
// it), or -1: a string's search, `heff_strFind`)
HEFF_FN V heff_bytesFind_lent(V n, V a, V i, int give) { return heff_strFind_lent(n, a, i, give); }
HEFF_FN V heff_bytesFind(V n, V a, V i) { return heff_strFind_lent(n, a, i, 3); }

// Bits
// ---------------------------------------------------------------------

// (`Bits`, a bitstring, never changed once made: a
// string's `Str`, of the kind `K_BIT`, its `len` bytes holding its bits
// the first the most significant of the first byte; `h.tag` says how
// many bits of the last byte are none of them, each 0 -- so that two of
// the same bits are the same bytes.  Dropped and shared with a thread as
// a string is, and shown as a binary, `b[...]`)
#define HEFF_BITS_LEN(x) ((x)->len * 8 - (int64_t)(x)->h.tag)

HEFF_FN Str *heff_bits_new(int64_t n) {
  int64_t len = (n + 7) >> 3;
  Str *s = heff_str_new(len);
  s->h.kind = K_BIT;
  s->h.tag = (uint16_t)((8 - (n & 7)) & 7);
  if (len) memset(s->s, 0, (size_t)len);
  return s;
}

// (the `n` bits of `src` from bit `from`, put at bit `at` of `dst`,
// whose bits there are 0)
HEFF_FN void heff_bits_copy(uint8_t *dst, int64_t at, const uint8_t *src, int64_t from, int64_t n) {
  if ((at & 7) == 0 && (from & 7) == 0) {
    int64_t k = n >> 3;
    if (k) memcpy(dst + (at >> 3), src + (from >> 3), (size_t)k);
    if (n & 7) dst[(at >> 3) + k] |= (uint8_t)(src[(from >> 3) + k] & (0xff00 >> (n & 7)));
    return;
  }
  int64_t i = 0;
  for (; i + 8 <= n; i += 8) heff_bits_write(dst, at + i, heff_bits_read(src, from + i, 8), 8);
  if (i < n) heff_bits_write(dst, at + i, heff_bits_read(src, from + i, n - i), n - i);
}

HEFF_FN V heff_bitsLength(V a) {
  int64_t n = HEFF_BITS_LEN((Str *)a);
  heff_drop(a);
  return MK_INT(n);
}

HEFF_FN V heff_bitsIntAt(V a, V o, V n, V f) {
  Str *x = (Str *)a;
  int64_t at = INT_OF(o), bits = INT_OF(n);
  if (!IS_INT(o) || !IS_INT(n) || at < 0 || bits < 0 || bits > 64 || at + bits > HEFF_BITS_LEN(x)) return heff_abandon();
  V r = heff_bits_int(x->p, at, bits, INT_OF(f));
  heff_drop(a);
  return r;
}

// (the integer `v`, its low `n` bits, 0 to 64, as bits)
HEFF_FN V heff_bitsOfInt(V n, V f, V v) {
  int64_t bits = INT_OF(n);
  if (!IS_INT(n) || bits < 0 || bits > 64) return heff_abandon();
  uint64_t w = heff_bits_of_int(v, bits, INT_OF(f));
  heff_drop(v);
  Str *s = heff_bits_new(bits);
  heff_bits_write(s->s, 0, w, bits);
  return (V)s;
}

// (a list's bits, one after another, made at once)
HEFF_FN V heff_bitsConcat(V l) {
  int64_t n = 0;
  for (V c = l; heff_tag_of(c) == TAG_Cons; c = heff_field(c, 1)) n += HEFF_BITS_LEN((Str *)heff_field(c, 0));
  Str *s = heff_bits_new(n);
  int64_t k = 0;
  for (V c = l; heff_tag_of(c) == TAG_Cons; c = heff_field(c, 1)) {
    Str *x = (Str *)heff_field(c, 0);
    heff_bits_copy(s->s, k, x->p, 0, HEFF_BITS_LEN(x));
    k += HEFF_BITS_LEN(x);
  }
  heff_drop(l);
  return (V)s;
}

// (the `n` bits from bit `o`; out of them, abandoned)
HEFF_FN V heff_bitsSlice(V a, V o, V n) {
  Str *x = (Str *)a;
  int64_t at = INT_OF(o), m = INT_OF(n);
  if (!IS_INT(o) || !IS_INT(n) || at < 0 || m < 0 || at + m > HEFF_BITS_LEN(x)) return heff_abandon();
  Str *s = heff_bits_new(m);
  heff_bits_copy(s->s, 0, x->p, at, m);
  heff_drop(a);
  return (V)s;
}

// (bytes as bits, and bits that are whole bytes as bytes (others,
// abandoned): the same buffer where it is the last reference)
HEFF_FN V heff_bitsOfBytes(V a) {
  Str *x = (Str *)a;
  if (heff_alone(&x->h)) { x->h.kind = K_BIT; x->h.tag = 0; return a; }
  Str *s = heff_bits_new(x->len * 8);
  if (x->len) memcpy(s->s, x->p, (size_t)x->len);
  heff_drop(a);
  return (V)s;
}

HEFF_FN V heff_bitsBytes(V a) {
  Str *x = (Str *)a;
  if (x->h.tag) return heff_abandon();
  if (heff_alone(&x->h)) { x->h.kind = K_BYT; return a; }
  Str *s = heff_bytes_new(x->len);
  if (x->len) memcpy(s->s, x->p, (size_t)x->len);
  heff_drop(a);
  return (V)s;
}

HEFF_FN V heff_bitsEq(V a, V b) {
  Str *x = (Str *)a, *y = (Str *)b;
  int r = x->len == y->len && x->h.tag == y->h.tag && (x->len == 0 || memcmp(x->p, y->p, (size_t)x->len) == 0);
  heff_drop(a);
  heff_drop(b);
  return heff_bool(r);
}

// (a `Float64`'s bits, IEEE's: of 64 bits, or of 32, rounded to a
// `float` first; a NaN, the quiet one, its sign 0, as every backend has
// it)
HEFF_FN V heff_floatBits(V n, V x) {
  int64_t bits = INT_OF(n);
  double d = FLT_OF(x);
  heff_drop(x);
  if (bits == 64) {
    uint64_t u;
    if (d != d) u = 0x7ff8000000000000ull; else memcpy(&u, &d, 8);
    return heff_int_u64(u);
  }
  if (bits == 32) {
    float g = (float)d;
    uint32_t u;
    if (g != g) u = 0x7fc00000u; else memcpy(&u, &g, 4);
    return heff_int_u64(u);
  }
  return heff_abandon();
}

// (the `Float64` whose bits, of 64 or of 32, are those of `v`)
HEFF_FN V heff_floatOfBits(V n, V v) {
  int64_t bits = INT_OF(n);
  uint64_t u = heff_int_low64(v);
  heff_drop(v);
  if (bits == 64) { double d; memcpy(&d, &u, 8); return heff_flt(d); }
  if (bits == 32) { uint32_t w = (uint32_t)u; float g; memcpy(&g, &w, 4); return heff_flt((double)g); }
  return heff_abandon();
}

// (the `Float64` nearest the decimal `strSlice s i j`, or the `Float32`
// nearest it, of `w` 64 or 32; of text that is no decimal, NaN)
HEFF_FAST V heff_floatOfDecimal_lent(V w, V s, V i, V j, int give) {
  Str *x = (Str *)s;
  int64_t m, b = heff_str_range(x, i, j, &m), bits = INT_OF(w);
  double d = bits == 64 || bits == 32 ? heff_float_of_decimal((const char *)x->p + b, m, (int)bits) : 0;
  HEFF_GIVEN(give, 1, s);
  if (bits != 64 && bits != 32) return heff_abandon();
  return heff_flt(d);
}
HEFF_FN V heff_floatOfDecimal(V w, V s, V i, V j) { return heff_floatOfDecimal_lent(w, s, i, j, 2); }

// What providers share
// ---------------------------------------------------------------------

HEFF_FN V heff_just(V x) { return heff_tag_n(TAG_Just, 1, &x); }
#define heff_nothing NTAG(TAG_Nothing)

HEFF_FN V heff_cons(V x, V rest) {
  V f[2] = { x, rest };
  return heff_tag_n(TAG_Cons, 2, f);
}

// A string crosses between the program and the system through these
// alone: a provider neither reads a `Str`'s bytes nor makes one of its
// own, and the runtime alone knows how a string is kept.  Which of them
// it crosses by is what it is to the system:
//
// - content -- a file's, a stream's, a pipe's, what a command wrote,
//   what was fetched -- is bytes, as they are: in by `heff_str_bytes`
//   (a file read to its end, `heff_str_read`), out by `heff_put` or
//   `heff_bytes`;
// - a path is bytes too: out as a C string (`heff_cstr`), and a
//   directory's names in (`heff_strs_bytes`);
// - a name -- an argument of the program, the environment's, the
//   working directory, the program's path, a command and its
//   arguments -- and what a host of text has (JSON, a terminal's
//   lines) are text: in by `heff_str_text` (`heff_str_text_n`,
//   `heff_strs_text`), out by `heff_cstr_text`.
//
// A C string out is malloc'd, or NULL where the string cannot be one --
// it has a NUL in it -- and the operation then fails (its `Nothing`, its
// `False`).  Content and paths are the string's bytes, as they are;
// text is made valid, what is not UTF-8 in it U+FFFD, both in and out.

// (content in, `n` bytes, as a string)
HEFF_FN V heff_str_bytes(const void *c, int64_t n) { return heff_str_of(c, n); }

// (text in, `n` bytes of it, as a string)
HEFF_FN V heff_str_text_n(const void *c, int64_t n) { return heff_str_valid(c, n); }

// (a C string of text in, as a string: a name)
HEFF_FN V heff_str_text(const char *c) { return heff_str_text_n(c, (int64_t)strlen(c)); }

// (C strings, a directory's names, as a list of strings)
HEFF_FN V heff_strs_bytes(char **xs, int64_t n) {
  V l = NTAG(TAG_Nil);
  for (int64_t i = n - 1; i >= 0; i--) l = heff_cons(heff_str_bytes(xs[i], (int64_t)strlen(xs[i])), l);
  return l;
}

// (C strings of text, names, as a list of strings)
HEFF_FN V heff_strs_text(char **xs, int64_t n) {
  V l = NTAG(TAG_Nil);
  for (int64_t i = n - 1; i >= 0; i--) l = heff_cons(heff_str_text(xs[i]), l);
  return l;
}

// (a path, as a C string to give the system: malloc'd, or NULL)
HEFF_FN char *heff_cstr(V v) {
  Str *s = (Str *)v;
  if (s->len && memchr(s->p, 0, (size_t)s->len)) return NULL;
  char *c = heff_alloc((size_t)s->len + 1);
  if (s->len) memcpy(c, s->p, (size_t)s->len);
  c[s->len] = 0;
  return c;
}

// (a name or text, as a C string to give the system: malloc'd, or NULL)
HEFF_FN char *heff_cstr_text(V v) {
  Str *s = (Str *)v;
  if (s->len && memchr(s->p, 0, (size_t)s->len)) return NULL;
  int own;
  heff_u8_valid_len(s->p, s->len, &own);
  if (own) return heff_cstr(v);
  Str *t = (Str *)heff_str_valid(s->p, s->len);
  char *c = heff_cstr((V)t);
  heff_drop((V)t);
  return c;
}

// (content out, malloc'd, `*n` bytes, a NUL after them)
HEFF_FN char *heff_bytes(V v, size_t *n) {
  Str *s = (Str *)v;
  char *c = heff_alloc((size_t)s->len + 1);
  if (s->len) memcpy(c, s->p, (size_t)s->len);
  c[s->len] = 0;
  *n = (size_t)s->len;
  return c;
}

// (content written out to `f`)
HEFF_FN void heff_put(FILE *f, V v) {
  Str *s = (Str *)v;
  if (s->len) fwrite(s->p, 1, (size_t)s->len, f);
}

// The working directory: each thread's own (#97)
// ---------------------------------------------------------------------
//
// The system has one working directory a process; the runtime keeps a
// directory for each thread (`heff_dir`): the process's own, asked for
// once, in the program's thread; its starter's, copied, in a thread a
// provider starts (`heff_dir_copy`, given to the started thread by
// `heff_dir_take`); another, by std.process's `setWorkingDir`, for
// that thread alone.  A provider gives the system every relative path
// under it (`heff_path_in_dir`), and never changes the process's --
// but in a command started, between its fork and its exec
// (`heff_exec_in_dir`).
HEFF_VAR(HEFF_TLS char *heff_dir);

extern size_t heff_path_under(const uint8_t *dir, size_t dn, const uint8_t *path, size_t pn, int windows, uint8_t *out);

#ifdef _WIN32
#define HEFF_WINDOWS 1
#else
#define HEFF_WINDOWS 0
#endif

// (`s` copied, malloc'd)
HEFF_FN char *heff_strdup(const char *s) {
  size_t n = strlen(s) + 1;
  char *c = heff_alloc(n);
  memcpy(c, s, n);
  return c;
}

// (this thread's working directory)
HEFF_FN const char *heff_working_dir(void) {
  if (!heff_dir) {
    char buf[4096];
#ifdef _WIN32
    const char *d = _getcwd(buf, sizeof buf);
#else
    const char *d = getcwd(buf, sizeof buf);
#endif
    heff_dir = heff_strdup(d ? d : ".");
  }
  return heff_dir;
}

// (this thread's working directory, copied for a thread it starts)
HEFF_FN char *heff_dir_copy(void) {
  return heff_strdup(heff_working_dir());
}

// (`dir`, malloc'd, made this thread's working directory: its now)
HEFF_FN void heff_dir_take(char *dir) {
  free(heff_dir);
  heff_dir = dir;
}

// (`path`, malloc'd, as the system is to be given it from this thread:
// under the thread's directory where it is relative; `path` freed, the
// path given back malloc'd -- NULL stays NULL)
HEFF_FN char *heff_path_in_dir(char *path) {
  if (!path) return NULL;
  const char *dir = heff_working_dir();
  size_t dn = strlen(dir), pn = strlen(path);
  char *out = heff_alloc(dn + pn + 2);
  size_t n = heff_path_under((const uint8_t *)dir, dn, (const uint8_t *)path, pn, HEFF_WINDOWS, (uint8_t *)out);
  out[n] = 0;
  free(path);
  return out;
}

// (`dir`, malloc'd, from this thread, made the thread's working
// directory, as the system names it (its links resolved): 1; or 0
// where it is no directory there, the thread's as it was.  `dir`
// consumed)
HEFF_FN int heff_working_dir_set(char *dir) {
  char *p = heff_path_in_dir(dir);
  struct stat st;
  int ok = stat(p, &st) == 0 && S_ISDIR(st.st_mode);
  if (!ok) { free(p); return 0; }
#ifdef _WIN32
  char *r = _fullpath(NULL, p, 0);
#else
  char *r = realpath(p, NULL);
#endif
  if (r) { free(p); p = r; }
  heff_dir_take(p);
  return 1;
}

#ifndef _WIN32
// (the command `as` -- its name found on the PATH -- forked and exec'd
// in this thread's directory, its standard streams `in`, `out` and
// `err` where each is not -1, the descriptors `closed` closed in it,
// its environment `env` where not NULL: its pid, or -1 where it could
// not be run -- not found, not a program, the directory gone -- `errno`
// why, as the child says through a pipe its exec closes)
HEFF_FN pid_t heff_exec_in_dir(char **as, char **env, int in, int out, int err, const int *closed, int nclosed) {
  int px[2];
  if (pipe(px) != 0) return -1;
  fcntl(px[0], F_SETFD, FD_CLOEXEC);
  fcntl(px[1], F_SETFD, FD_CLOEXEC);
  const char *dir = heff_working_dir();
  fflush(stdout);
  fflush(stderr);
  pid_t pid = fork();
  if (pid == 0) {
    // (the child: nothing but what is safe after a fork)
    int e;
    if ((in >= 0 && dup2(in, 0) < 0) || (out >= 0 && dup2(out, 1) < 0) || (err >= 0 && dup2(err, 2) < 0)) goto failed;
    for (int i = 0; i < nclosed; i++) close(closed[i]);
    if (chdir(dir) != 0) goto failed;
    if (env) environ = env;
    execvp(as[0], as);
  failed:
    e = errno;
    (void)!write(px[1], &e, sizeof e);
    _exit(127);
  }
  close(px[1]);
  int e = 0;
  if (pid > 0) {
    ssize_t got;
    while ((got = read(px[0], &e, sizeof e)) < 0 && errno == EINTR) {}
    if (got > 0) {
      int st;
      while (waitpid(pid, &st, 0) < 0 && errno == EINTR) {}
      pid = -1;
    }
  } else e = errno;
  close(px[0]);
  if (pid < 0) errno = e;
  return pid;
}
#endif

// `Bytes` cross by these alone, as they are: in, `n` bytes copied, by
// `heff_bytes_in`; out, read where they are kept, `*n` of them, by
// `heff_bytes_data` (the value not consumed, its bytes there as long as
// it is held, and never written to).
HEFF_FN V heff_bytes_in(const void *c, int64_t n) {
  Str *s = heff_bytes_new(n);
  if (n) memcpy(s->s, c, (size_t)n);
  return (V)s;
}

HEFF_FN const uint8_t *heff_bytes_data(V v, int64_t *n) {
  Str *s = (Str *)v;
  *n = s->len;
  return s->p;
}

// (C strings' order, for qsort)
HEFF_FN int heff_cmp_cstr(const void *a, const void *b) {
  return strcmp(*(char *const *)a, *(char *const *)b);
}

// (a path joined to a name in it, malloc'd)
HEFF_FN char *heff_join(const char *dir, const char *name) {
  size_t a = strlen(dir), b = strlen(name);
  char *p = heff_alloc(a + b + 2);
  memcpy(p, dir, a);
#ifdef _WIN32
  p[a] = '\\';
#else
  p[a] = '/';
#endif
  memcpy(p + a + 1, name, b + 1);
  return p;
}

// (an answer, for an operation's function: given it, its value asked for)
HEFF_FN V heff_answer(V f, V x) { return heff_tr(heff_app1(f, x)); }

// Foreign values: a thing of the host's that the program holds as a
// value -- a `FILE *`, a library's handle -- made by a provider of a
// pointer and what lets it go (`heff_foreign`), the pointer read back
// where an operation is given the value (`heff_foreign_ptr`); the
// program drops the last reference, and the thing is let go of then, at
// once (Perceus: never while it is referenced).  Its type in the program
// is whatever the operation says it is -- a `data` of no constructors --
// and the provider vouches for it at the boundary; the compiler's
// generated glue makes and reads them as an effect's module describes
// its operations in C (the `ffi` module).  One effect's provider takes
// what another's handed out, the value given it by the program, as a
// `with` of the one hands its thing to an operation of the other.
HEFF_FN V heff_foreign(void *p, void (*let_go)(void *)) {
  Fgn *g = heff_obj_alloc(sizeof(Fgn));
  g->h.rc = 1; g->h.kind = K_FGN; g->h.tag = 0; g->p = p; g->let_go = let_go;
  g->end = NULL; g->owner = 0; g->at = 0; g->ended = 0;
  return (V)g;
}

// A thing that can be ended before it is let go of -- a socket closed,
// a command killed, while another thread may hold it still -- is made
// with what ends it, `end`, besides what lets it go: `end` ends it, and
// says why it failed, or 0; `let_go` frees what is left.  A custodian
// ends it at its shutdown (the custodians' part of the runtime), the
// struct kept for those that hold it, each of whose operations finds it
// ended; else it is ended as the program drops its last reference, just
// before it is let go of.  `end` is asked once, at most, by the runtime;
// the provider's own operations may end it before, so `end` finds it
// ended, and says 0.  A thing that fails to end there is a failure of
// its custodian's (`heff_foreign_failed`), or, of the root's, the
// program's: said, and the program ended.
HEFF_FN V heff_foreign_ending(void *p, void (*let_go)(void *), const char *(*end)(void *)) {
  V v = heff_foreign(p, let_go);
  ((Fgn *)v)->end = end;
  return v;
}

// (the custodians' part, where a program has it: a thing taken out of
// its custodian's custody, as it is let go of; and a failure of its
// custodian's, `owner`, why said)
HEFF_VAR(void (*heff_foreign_disowned)(struct Fgn *g));
HEFF_VAR(void (*heff_foreign_failed)(V owner, const char *why));

// (a failure of the root's custodian: the program's, said, and the
// program ended)
HEFF_FN void heff_root_failed(const char *why) {
  fflush(stdout);
  fprintf(stderr, "heff: %s\n", why);
  heff_exit(1);
}

// (a foreign value let go of: taken out of its custodian's custody,
// ended where it is not already, then let go of; where it fails to end,
// its custodian's failure)
static void heff_foreign_gone(Fgn *g) {
  if (g->owner && heff_foreign_disowned) heff_foreign_disowned(g);
  const char *why = g->end && !g->ended ? g->end(g->p) : NULL;
  char *said = why ? heff_strdup(why) : NULL;
  if (g->let_go) g->let_go(g->p);
  if (!said) return;
  if (g->owner && heff_foreign_failed) heff_foreign_failed(g->owner, said);
  else heff_root_failed(said);
  free(said);
}

HEFF_FN void *heff_foreign_ptr(V v) {
  if (!IS_OBJ(v) || OBJ(v)->kind != K_FGN) heff_fail("not a foreign value");
  return ((Fgn *)v)->p;
}

// The custodian current.  Where a program's world has the custodian's
// effect, its handler's monad reads the custodian current (heff's
// entry, as Reader does), and tells it here just before each operation
// (`heff_custodyIn`): a `Maybe Custodian`, held until the next, for the
// provider performing it to read.  A computation an operation carries
// to run later -- a custodian's `stop`, a `with`'s release -- is of
// that monad, and the provider takes it given the custodian current
// where it was asked (`heff_carried`, `heff_carried_fn`).  In a world
// without custodians nothing is told, and a computation is taken as it
// is.
HEFF_VAR(HEFF_TLS V heff_custody_env);

static inline V heff_custodyIn(V c) {
  V old = heff_custody_env;
  heff_custody_env = c;
  if (old) heff_drop(old);
  return NTAG(TAG_MkUnit);
}

// (a computation an operation carries, `m a`, consumed: as the provider
// runs it, given the custodian current where the operation was asked)
static inline V heff_carried(V m) {
  return heff_custody_env ? heff_answer(m, heff_dup(heff_custody_env)) : m;
}

static V heff_carried_then(V self, V *a) {
  V *e = heff_env(self);
  V f = heff_dup(e[0]), c = heff_dup(e[1]);
  heff_drop(self);
  return heff_answer(heff_answer(f, a[0]), c);
}

// (... of a function to one, `a -> m b`, consumed: what it comes to
// given the custodian current where the operation was asked)
static inline V heff_carried_fn(V f) {
  if (!heff_custody_env) return f;
  V e[2] = { f, heff_dup(heff_custody_env) };
  return heff_clo(heff_carried_then, 1, 2, e);
}

// (an errno's name, the same on every system where its number is not)
HEFF_FN const char *heff_errno_name(int e) {
  switch (e) {
#define HEFF_E(x) case x: return #x;
  HEFF_E(EACCES) HEFF_E(EAGAIN) HEFF_E(EBADF) HEFF_E(EBUSY) HEFF_E(EEXIST) HEFF_E(EFBIG)
  HEFF_E(EINTR) HEFF_E(EINVAL) HEFF_E(EIO) HEFF_E(EISDIR) HEFF_E(EMFILE)
  HEFF_E(ENAMETOOLONG) HEFF_E(ENFILE) HEFF_E(ENODEV) HEFF_E(ENOENT) HEFF_E(ENOMEM)
  HEFF_E(ENOSPC) HEFF_E(ENOSYS) HEFF_E(ENOTDIR) HEFF_E(ENOTEMPTY) HEFF_E(ENXIO)
  HEFF_E(EPERM) HEFF_E(EPIPE) HEFF_E(EROFS) HEFF_E(ESPIPE) HEFF_E(EXDEV)
#ifdef ELOOP
  HEFF_E(ELOOP)
#endif
#ifdef ETXTBSY
  HEFF_E(ETXTBSY)
#endif
#ifdef EOVERFLOW
  HEFF_E(EOVERFLOW)
#endif
#ifdef EDQUOT
  HEFF_E(EDQUOT)
#endif
#if EWOULDBLOCK != EAGAIN
  HEFF_E(EWOULDBLOCK)
#endif
#undef HEFF_E
  default: return "E?";
  }
}

// (why a call of the system failed, as the program has it: a record of
// the errno `err`, its name and what the system says of it -- its labels
// `code`, `name`, `message`, in `shape`, the caller's, as the emitter
// numbers them)
HEFF_FN V heff_errno(int err, uint32_t *shape) {
  const char *name = heff_errno_name(err);
  char other[24];
  if (name[1] == '?') {
    snprintf(other, sizeof other, "errno %d", err);
    name = other;
  }
  V f[3] = { heff_int(err), heff_str_text(name), heff_str_text(strerror(err)) };
  return heff_rec(3, shape, f);
}

// A stack that overflows
// ---------------------------------------------------------------------
//
// heff's recursion is the C stack's, so a recursion deep enough runs
// out of it: a fault in the guard below the stack, where the system
// would end the process, saying nothing.  Instead each thread heff runs
// in -- the program's own, and each a provider starts by
// `heff_thread_start` -- is watched (`heff_watch_stack`): the bottom of
// its stack known, and a stack of its own for the handler of faults
// (`sigaltstack`).  A fault near the bottom of the stack is an
// overflow; any other is the system's, as without the handler.
//
// The handler does not jump out itself: it has the thread go on at
// `heff_overflowed`, on a stack of the thread's kept for it, once the
// system has put back the signal's mask and taken the thread off the
// handler's stack (macOS's `_longjmp` out of a handler would leave the
// system thinking it still on it, and the next fault unhandled).  There
// it fails as `heff_fail` does: caught by the innermost `heff_try`, why
// "stack overflow"; else the program says `heff: stack overflow` and
// exits with 2.  What the frames jumped over were doing is left undone,
// as a failure leaves it: what they made leaked, a definition they were
// computing computed again.  But a fault in code not the program's --
// the system's `malloc`, a lock's -- may leave what that code holds
// held for good: the program ends there, caught or not.
//
// Not on Windows, nor where a sanitizer handles faults itself; and said,
// never caught, but on x86-64 and arm64.
#define HEFF_OVERFLOW "stack overflow"
#define HEFF_OVERFLOW_STATUS 2

#if defined(__has_feature)
#if __has_feature(address_sanitizer) || __has_feature(thread_sanitizer)
#define HEFF_SANITIZED 1
#endif
#endif
#if defined(__SANITIZE_ADDRESS__) || defined(__SANITIZE_THREAD__)
#define HEFF_SANITIZED 1
#endif
#if !defined(HEFF_SANITIZED) && (defined(__APPLE__) || defined(__linux__))
#define HEFF_WATCHED 1
#endif

#ifdef HEFF_WATCHED
#include <sys/ucontext.h>
#ifdef __APPLE__
#include <mach-o/getsect.h>
#include <mach-o/ldsyms.h>
#else
extern int pthread_getattr_np(pthread_t, pthread_attr_t *);
// (the program's code, from its start to the end of its text, as the
// linker marks them)
extern char __executable_start[] __attribute__((weak));
extern char etext[] __attribute__((weak));
#endif

// (the guard below a stack heff starts, and how far below its bottom a
// fault is taken for an overflow; the handler's stack, and the one the
// thread goes on on)
#define HEFF_GUARD ((size_t)1 << 20)
#define HEFF_SIG_STACK ((size_t)1 << 16)

// (where the fault was, and the thread made to go on at `f`, its stack
// pointer `sp`, as if `f` were called -- by the system's view of the
// thread's registers, `uc`)
#if defined(__APPLE__) && defined(__aarch64__)
#define HEFF_PC(uc) ((char *)__darwin_arm_thread_state64_get_pc((uc)->uc_mcontext->__ss))
#define HEFF_GO_ON(uc, f, sp) do { \
    __darwin_arm_thread_state64_set_pc_fptr((uc)->uc_mcontext->__ss, f); \
    __darwin_arm_thread_state64_set_sp((uc)->uc_mcontext->__ss, sp); } while (0)
#elif defined(__APPLE__) && defined(__x86_64__)
#define HEFF_PC(uc) ((char *)(uc)->uc_mcontext->__ss.__rip)
#define HEFF_GO_ON(uc, f, sp) do { \
    (uc)->uc_mcontext->__ss.__rip = (uintptr_t)(f); \
    (uc)->uc_mcontext->__ss.__rsp = (uintptr_t)(sp) - 8; } while (0)
#elif defined(__linux__) && defined(__aarch64__)
#define HEFF_PC(uc) ((char *)(uc)->uc_mcontext.pc)
#define HEFF_GO_ON(uc, f, sp) do { \
    (uc)->uc_mcontext.pc = (uintptr_t)(f); \
    (uc)->uc_mcontext.sp = (uintptr_t)(sp); } while (0)
#elif defined(__linux__) && defined(__x86_64__)
// (`REG_RIP` and `REG_RSP`, 16 and 15, named only where `_GNU_SOURCE` is)
#define HEFF_PC(uc) ((char *)(uc)->uc_mcontext.gregs[16])
#define HEFF_GO_ON(uc, f, sp) do { \
    (uc)->uc_mcontext.gregs[16] = (greg_t)(uintptr_t)(f); \
    (uc)->uc_mcontext.gregs[15] = (greg_t)((uintptr_t)(sp) - 8); } while (0)
#endif

// (the program's code: where a fault in it may be recovered from)
HEFF_VAR(char *heff_code_lo);
HEFF_VAR(char *heff_code_hi);
// (this thread's: the bottom of its stack, where it may go no lower; the
// handler's stack, and above it the one to go on on; and whether the
// fault was in code not the program's)
HEFF_VAR(HEFF_TLS char *heff_stack_lo);
HEFF_VAR(HEFF_TLS char *heff_sig_stack);
HEFF_VAR(HEFF_TLS int heff_overflow_lost);

// (where the thread goes on after its stack overflowed: failed, as
// `heff_fail` fails, or the program ended)
HEFF_FN __attribute__((noreturn)) void heff_overflowed(void) {
  if (heff_catch && !heff_overflow_lost) {
    heff_caught = HEFF_OVERFLOW;
    HEFF_LONGJMP(*heff_catch);
  }
  static const char said[] = "heff: " HEFF_OVERFLOW "\n";
  if (!heff_overflow_lost) fflush(stdout);
  if (write(2, said, sizeof said - 1) < 0) _exit(HEFF_OVERFLOW_STATUS);
  _exit(HEFF_OVERFLOW_STATUS);
}

HEFF_FN void heff_on_fault(int sig, siginfo_t *si, void *ctx) {
  char *a = (char *)si->si_addr, *lo = heff_stack_lo;
  if (!lo || a < lo - HEFF_GUARD || a >= lo + HEFF_GUARD) {
    signal(sig, SIG_DFL);
    return;
  }
#ifdef HEFF_GO_ON
  ucontext_t *uc = ctx;
  char *pc = HEFF_PC(uc);
  heff_overflow_lost = !(pc >= heff_code_lo && pc < heff_code_hi);
  uintptr_t sp = (uintptr_t)(heff_sig_stack + 2 * HEFF_SIG_STACK) & ~(uintptr_t)15;
  HEFF_GO_ON(uc, heff_overflowed, sp);
#else
  (void)ctx;
  heff_overflow_lost = 1;
  heff_overflowed();
#endif
}

// (the handler installed, for every thread, before any is watched)
HEFF_FN void heff_watch_faults(void) {
#ifdef __APPLE__
  unsigned long n = 0;
  heff_code_lo = (char *)getsegmentdata(&_mh_execute_header, "__TEXT", &n);
  heff_code_hi = heff_code_lo ? heff_code_lo + n : NULL;
#else
  heff_code_lo = __executable_start;
  heff_code_hi = etext;
#endif
  struct sigaction sa;
  memset(&sa, 0, sizeof sa);
  sa.sa_sigaction = heff_on_fault;
  sa.sa_flags = SA_SIGINFO | SA_ONSTACK;
  sigemptyset(&sa.sa_mask);
  sigaction(SIGSEGV, &sa, NULL);
  sigaction(SIGBUS, &sa, NULL);
}

// (this thread watched: its stack's bottom, and the handler's stack --
// each of its own that the handler reads touched here, not first in the
// handler, which may not allocate)
HEFF_FN void heff_watch_stack(void) {
  char *m = malloc(2 * HEFF_SIG_STACK);
  if (!m) return;
  stack_t ss;
  ss.ss_sp = m;
  ss.ss_size = HEFF_SIG_STACK;
  ss.ss_flags = 0;
  if (sigaltstack(&ss, NULL) != 0) { free(m); return; }
  heff_sig_stack = m;
  heff_overflow_lost = 0;
  pthread_t me = pthread_self();
#ifdef __APPLE__
  heff_stack_lo = (char *)pthread_get_stackaddr_np(me) - pthread_get_stacksize_np(me);
#else
  pthread_attr_t attr;
  void *at;
  size_t n;
  if (pthread_getattr_np(me, &attr) == 0) {
    if (pthread_attr_getstack(&attr, &at, &n) == 0) heff_stack_lo = at;
    pthread_attr_destroy(&attr);
  }
#endif
}

// (as the thread ends: no longer watched)
HEFF_FN void heff_unwatch_stack(void) {
  if (!heff_sig_stack) return;
  stack_t ss;
  memset(&ss, 0, sizeof ss);
  ss.ss_flags = SS_DISABLE;
  sigaltstack(&ss, NULL);
  heff_stack_lo = NULL;
  free(heff_sig_stack);
  heff_sig_stack = NULL;
}
#else
HEFF_FN void heff_watch_faults(void) {}
HEFF_FN void heff_watch_stack(void) {}
HEFF_FN void heff_unwatch_stack(void) {}
#endif

// Threads a provider starts (#36): each runs what it
// is given -- shared, `heff_share` -- by `heff_try`, so
// that a failure there is the thread's to hand back, not the end of the
// process; and ends by `heff_thread_end`.
// ---------------------------------------------------------------------

// (`f x`, asked for here, a failure caught: 0, its value at `*out`; or
// why it failed -- "heff:abandon" where it abandoned (`heff_abandon`),
// the thread's own string otherwise, to be copied before the thread
// ends.  What was made before the failure is leaked, not given back)
HEFF_FN const char *heff_try(V f, V x, V *out) {
  jmp_buf here;
  jmp_buf *volatile up = heff_catch;
  volatile long dep = heff_dep;
  volatile size_t open = heff_nopen;
  heff_catch = &here;
  if (HEFF_SETJMP(here) == 0) {
    *out = heff_tr(heff_app1(f, x));
    heff_catch = up;
    return NULL;
  }
  heff_catch = up;
  heff_dep = dep;
  heff_reopen(open);
  return heff_caught;
}

// (a failure handed back, as the thread it was caught in would have
// failed: `why` from `heff_try`, copied)
HEFF_FN void heff_fail_again(const char *why) {
  if (strcmp(why, "heff:abandon") == 0) heff_abandon();
  if (!heff_catch && strcmp(why, HEFF_OVERFLOW) == 0) {
    fflush(stdout);
    fputs("heff: " HEFF_OVERFLOW "\n", stderr);
    heff_exit(HEFF_OVERFLOW_STATUS);
  }
  heff_fail(why);
}

// (this thread's pages and what else the runtime keeps for it given
// back to the system, as it ends -- its pages that still hold something
// abandoned, for another thread to adopt)
// (what a thread does as it ends, where a part of the runtime asks for
// it: the custodians' part, the releases due on the thread run)
HEFF_VAR(void (*heff_thread_ending)(void));

HEFF_FN void heff_thread_end(void) {
  void (*ending)(void) = __atomic_load_n(&heff_thread_ending, __ATOMIC_ACQUIRE);
  if (ending) ending();
#if SMALL_MAX == 0
  for (size_t c = 0; c <= SMALL_MAX / 8; c++) {
    void *p = heff_free_list[c];
    while (p) {
      void *next = *(void **)p;
      free(p);
      p = next;
    }
    heff_free_list[c] = NULL;
  }
#elif defined(HEFF_THREADS)
  heff_heap_end();
#endif
  free(heff_dead);
  heff_dead = NULL;
  heff_ndead = heff_cdead = 0;
  free(heff_dir);
  heff_dir = NULL;
#ifdef HEFF_THREADS
  free(heff_open);
  heff_open = NULL;
  heff_nopen = heff_capopen = 0;
#endif
}

// (a thread started, as the program's own is, with a large stack: heff's
// recursion is the C stack's -- 0, or the system's error)
#ifndef HEFF_THREAD_STACK
#define HEFF_THREAD_STACK ((size_t)1 << 28)
#endif
typedef struct { void *(*run)(void *); void *u; } HeffStart;

// (a thread heff starts, watched while it runs)
HEFF_FN void *heff_started(void *u) {
  HeffStart s = *(HeffStart *)u;
  free(u);
  heff_tls_enter();
  heff_watch_stack();
  void *r = s.run(s.u);
  heff_unwatch_stack();
  return r;
}

HEFF_FN int heff_thread_start(pthread_t *t, void *(*run)(void *), void *u) {
  HeffStart *s = malloc(sizeof(HeffStart));
  if (!s) return ENOMEM;
  s->run = run;
  s->u = u;
  pthread_attr_t attr;
  pthread_attr_init(&attr);
  pthread_attr_setstacksize(&attr, HEFF_THREAD_STACK);
#ifdef HEFF_WATCHED
  pthread_attr_setguardsize(&attr, HEFF_GUARD);
#endif
  int r = pthread_create(t, &attr, heff_started, s);
  pthread_attr_destroy(&attr);
  if (r != 0) free(s);
  return r;
}

// Outside operations done later: the reactor (#43)
// ---------------------------------------------------------------------
//
// An outside operation that cannot be done without waiting -- a socket
// not yet readable or writable, a name being resolved, an HTTP transfer
// -- is a wait (`HeffWait`): what it waits for (a descriptor and its
// events; or, its `fd` -1, a source's word, below), its next step, how
// its answer is made of what it did, and how it is let go of undone.
// Its provider takes its first step itself; where that does not finish
// it, it hands the wait, the operation's function `f` and the world's
// continuation `k` to `heff_outside`, which
//
// - where no group is being started in (`heff_group` 0: a program with
//   no scheduler of std.reactor's), waits for it there, polling its
//   descriptor and stepping it until it is done, the whole program
//   waiting with it, and gives `f` of its answer to `k`, as the
//   provider would have;
// - in a group, keeps it among the pending and gives back
//   `HEFF_PENDING`, not calling `k`: what comes back, by the calls last
//   the world's continuations are, to the start (`heff_reactor_start`),
//   which tells its scheduler that the operation is pending.
//
// std.reactor's provider opens a group for
// a scheduler, starts each of its threads' outside operations in it --
// a computation run to its end, its value given back, or to a wait,
// pending -- asks which are finished, and closes it, what is pending in
// it let go of.  `heff_reactor_finished` polls the descriptors of every
// pending wait and of every source, steps each that is ready, and for
// each done, gives `f` of its answer to `k`, the rest of what was
// started run, up to its end -- its value one of its group's finished
// -- or to another wait, pending again.  A source (libcurl's, in
// std.http's provider) has descriptors of its own to poll and how
// long at most to wait for them, and says which of its waits are done
// (`heff_wait_done`).  A wait may have a deadline instead of, or as
// well as, a descriptor (`until`, by `heff_now_ms`): a sleep of
// std.time's is one with no descriptor, done when its time has passed,
// the reactor waiting no longer than the nearest deadline.  A wait whose
// deadline passes before it is done is done so, its `err` ETIMEDOUT:
// the time limit of an operation of std.net's, its answer that it timed
// out, what it began undone by it (a socket being connected closed).
// Where no group is being started in, the same deadline bounds the poll
// that waits for it there.
//
// Each thread of the system has a reactor of its own (`HEFF_TLS`): its
// waits are its own, waited for by it alone, driven by the scheduler
// running in it, and nothing of one thread's reactor is touched by
// another.

#include <errno.h>
#include <time.h>

// (now, in milliseconds of a clock that only goes forward: for
// deadlines, not for the time of day)
#ifdef _WIN32
HEFF_FN int64_t heff_now_ms(void) { return (int64_t)GetTickCount64(); }
#else
HEFF_FN int64_t heff_now_ms(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (int64_t)t.tv_sec * 1000 + t.tv_nsec / 1000000;
}
#endif

#define HEFF_STEP_DONE 0
#define HEFF_STEP_WAIT 1

// (what a provider gives back where its operation is pending: no value
// of the program's)
#ifdef HEFF_PART
extern Obj heff_pending_obj;
#else
Obj heff_pending_obj = { IMMORTAL, K_STR, 0 };
#endif
#define HEFF_PENDING ((V)&heff_pending_obj)

typedef struct HeffWait HeffWait;
struct HeffWait {
  int fd;                        // (what it waits for; -1, a source's word,
                                 //  or its deadline alone)
  short events;                  // (POLLIN, POLLOUT)
  int64_t until;                 // (when it is done regardless, by
                                 //  `heff_now_ms`; 0, never)
  int err;                       // (why waiting failed -- errno, poll's,
                                 //  EBADF, its socket closed, or ETIMEDOUT,
                                 //  its deadline passed -- its answer's to say)
  int (*step)(HeffWait *);       // (its next step: HEFF_STEP_DONE, or HEFF_STEP_WAIT,
                                 //  its `fd` and `events` again)
  V (*answer)(HeffWait *);       // (its answer, made, the wait let go of)
  void (*cancel)(HeffWait *);    // (the wait let go of, undone)
  // (the reactor's)
  V f, k;
  int64_t group;
  int done;
  int64_t epoch;                 // (how many descriptors had been closed,
                                 //  by any thread, when it began to wait)
  int marked;                    // (the descriptor its reactor is marked
                                 //  as waiting on, for it, or -1)
  int kfd;                       // (where there is a kqueue: the descriptor
  short kway;                    //  it is waiting on there, and which way --
                                 //  1 reading, 2 writing -- or 0, on none;
                                 //  3, polled instead)
  HeffWait *prev, *next;
};

#ifndef _WIN32
typedef struct HeffSource HeffSource;
struct HeffSource {
  // (its descriptors to poll, at `p`, room for `room` of them: how many
  // it has, which are written only where there is room; at `*ms`, how
  // long at most to wait for them, -1 for ever)
  int (*fds)(struct pollfd *p, int room, int *ms);
  // (after the poll: its descriptors, `n` of them at `p`, as polled)
  void (*ready)(struct pollfd *p, int n);
  int on;
  size_t at;                     // (the reactor's: where its descriptors are
  int n;                         //  polled, and how many)
  HeffSource *next;
};
#endif

// (a group: its number, unique among every thread's; how many waits are
// pending in it -- in a root, those of the groups within it too -- the
// root it is within, or 0 where it is one; in a root, what a step of a
// computation started in it that fails is finished as, given why, or 0:
// the failure is the program's; and, in a group within one, what gives
// it up from any thread, where something does, or 0)
typedef struct HeffGiving HeffGiving;
typedef struct { int64_t id, pending, root; V failed; HeffGiving *giving; } HeffGroup;
typedef struct { int64_t group; V v; } HeffFinished;

HEFF_VAR(HEFF_TLS int64_t heff_group);
HEFF_VAR(int64_t heff_last_group);
HEFF_VAR(HEFF_TLS HeffGroup *heff_groups_open);
HEFF_VAR(HEFF_TLS size_t heff_ngroups);
HEFF_VAR(HEFF_TLS size_t heff_capgroups);
HEFF_VAR(HEFF_TLS HeffWait *heff_waits_first);
HEFF_VAR(HEFF_TLS HeffWait *heff_waits_last);
HEFF_VAR(HEFF_TLS HeffFinished *heff_finished);
HEFF_VAR(HEFF_TLS size_t heff_nfinished);
HEFF_VAR(HEFF_TLS size_t heff_capfinished);
#ifndef _WIN32
HEFF_VAR(HEFF_TLS HeffSource *heff_sources);
HEFF_VAR(HEFF_TLS struct pollfd *heff_polled);
HEFF_VAR(HEFF_TLS HeffWait **heff_polled_waits);
HEFF_VAR(HEFF_TLS size_t heff_cappolled);
// (what wakes this thread's reactor from another thread: a pipe, made
// with its first group and closed with its last, written a byte to; and
// whether a turn has read one since `heff_reactor_finished` last came
// back)
HEFF_VAR(HEFF_TLS int heff_wake_made);
HEFF_VAR(HEFF_TLS int heff_wake_fds[2]);
HEFF_VAR(HEFF_TLS int heff_woken);
#endif

// (every thread's open groups, each with the pipe that wakes its
// thread's reactor, under a lock: so that a group is woken from any
// thread, and not once its pipe is closed)
typedef struct { int64_t id; int fd; } HeffWaker;
#ifdef HEFF_PART
extern HeffWaker *heff_wakers;
extern size_t heff_nwakers, heff_capwakers;
extern pthread_mutex_t heff_wakers_mu;
#else
HeffWaker *heff_wakers;
size_t heff_nwakers, heff_capwakers;
pthread_mutex_t heff_wakers_mu = PTHREAD_MUTEX_INITIALIZER;
#endif

// (the descriptors closed last, by any thread, under the wakers' lock:
// each with the count of those closed so far, kept at that count modulo
// how many are kept -- so that a wait pending in another thread's
// reactor on one that is closed is done, EBADF, by that thread, and not
// one begun after on a descriptor of the same number; and how many this
// thread has looked at)
#define HEFF_CLOSED_KEPT 1024
typedef struct { int fd; int64_t epoch; } HeffClosed;
#ifdef HEFF_PART
extern HeffClosed heff_closed[HEFF_CLOSED_KEPT];
extern int64_t heff_closed_epoch;
#else
HeffClosed heff_closed[HEFF_CLOSED_KEPT];
int64_t heff_closed_epoch;
#endif
HEFF_VAR(HEFF_TLS int64_t heff_closed_seen);

#ifndef _WIN32
// (which threads' reactors wait on each descriptor: a word of bits for
// each, a bit for each reactor, set by its thread while one of its waits
// is on it and cleared by it when none is -- so that a descriptor being
// closed wakes those alone, and only where there are any.  The words are
// in chunks made when first needed, never let go of; the reactors' bits
// and their pipes are given out with their pipes, under the wakers'
// lock, the last bit standing for every reactor beyond the others, set
// and never cleared, which wakes every reactor.  A descriptor beyond the
// chunks has no word, and wakes every reactor.  Of a thread's own: its
// bit, 0 where it has no pipe, and how many of its waits are on each
// descriptor)
#define HEFF_MARK_CHUNK 4096
#define HEFF_MARK_CHUNKS 1024
#define HEFF_MARK_ANY ((uint64_t)1 << 63)
HEFF_VAR(uint64_t *heff_marks[HEFF_MARK_CHUNKS]);
HEFF_VAR(uint64_t heff_marks_given);
HEFF_VAR(int heff_marks_pipe[63]);
HEFF_VAR(HEFF_TLS uint64_t heff_mark);
HEFF_VAR(HEFF_TLS int32_t *heff_marks_mine);
HEFF_VAR(HEFF_TLS size_t heff_capmarks_mine);

// (the word of descriptor `fd`, made where `make` and it is not; NULL
// where it is beyond the chunks, or, not `make`, not made)
HEFF_FN uint64_t *heff_marks_of(int fd, int make) {
  size_t c = (size_t)fd / HEFF_MARK_CHUNK;
  if (c >= HEFF_MARK_CHUNKS) return NULL;
  uint64_t *m = __atomic_load_n(&heff_marks[c], __ATOMIC_SEQ_CST);
  if (!m && make) {
    uint64_t *made = calloc(HEFF_MARK_CHUNK, sizeof *made);
    if (!made) heff_fail("out of memory");
    if (__atomic_compare_exchange_n(&heff_marks[c], &m, made, 0, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST)) m = made;
    else free(made);
  }
  return m ? &m[(size_t)fd % HEFF_MARK_CHUNK] : NULL;
}

// (this thread's reactor marked as waiting on `fd` once more: whether it
// is, or once less)
HEFF_FN int heff_mark_on(int fd) {
  if (fd < 0 || !heff_mark || (size_t)fd >= (size_t)HEFF_MARK_CHUNK * HEFF_MARK_CHUNKS) return 0;
  if ((size_t)fd >= heff_capmarks_mine) {
    size_t cap = heff_capmarks_mine ? heff_capmarks_mine : 256;
    while (cap <= (size_t)fd) cap *= 2;
    int32_t *m = heff_alloc(cap * sizeof *m);
    if (heff_capmarks_mine) memcpy(m, heff_marks_mine, heff_capmarks_mine * sizeof *m);
    memset(m + heff_capmarks_mine, 0, (cap - heff_capmarks_mine) * sizeof *m);
    free(heff_marks_mine);
    heff_marks_mine = m;
    heff_capmarks_mine = cap;
  }
  if (heff_marks_mine[fd]++ == 0) __atomic_fetch_or(heff_marks_of(fd, 1), heff_mark, __ATOMIC_SEQ_CST);
  return 1;
}

HEFF_FN void heff_mark_off(int fd) {
  if (fd < 0 || !heff_mark || (size_t)fd >= heff_capmarks_mine) return;
  if (--heff_marks_mine[fd] == 0 && heff_mark != HEFF_MARK_ANY)
    __atomic_fetch_and(heff_marks_of(fd, 1), ~heff_mark, __ATOMIC_SEQ_CST);
}
#endif

#ifdef HEFF_KQUEUE
// (where the system has kqueue: each thread's reactor keeps its waits'
// descriptors in a kqueue of its own, each added as its wait begins and
// deleted as it ends, so that a turn asks the kernel for those ready
// alone -- a poll of every pending wait's descriptor, every turn, costs
// as many as are pending, and a server's many quiet connections made
// each turn as dear as they are many.  A descriptor waited on one way
// by two waits of the thread at once, or one kqueue refuses, is polled
// as before, the later wait's.  The kqueue, made with the thread's
// first group, as its pipe is, is polled with the others, and read, not
// waiting, where it is ready; and each wait of it has its descriptor
// and its way kept, by both, at `heff_kq_owner`)
HEFF_VAR(HEFF_TLS int heff_kq);
HEFF_VAR(HEFF_TLS int heff_kq_made);
HEFF_VAR(HEFF_TLS HeffWait **heff_kq_owner);
HEFF_VAR(HEFF_TLS size_t heff_capkq_owner);

// (the wait's descriptor and way in the kqueue: where it has one, and
// another wait of the thread has not, and kqueue takes it; else polled)
HEFF_FN void heff_kq_add(HeffWait *w) {
  w->kway = 0;
  w->kfd = w->fd;
  if (w->fd < 0 || w->done) return;
  short way = w->events == POLLIN ? 1 : w->events == POLLOUT ? 2 : 0;
  if (!way) {
    w->kway = 3;
    return;
  }
  if (!heff_kq_made) {
    w->kway = 3;
    return;
  }
  size_t at = (size_t)w->fd * 2 + (size_t)(way - 1);
  if (at >= heff_capkq_owner) {
    size_t cap = heff_capkq_owner ? heff_capkq_owner : 512;
    while (cap <= at) cap *= 2;
    HeffWait **m = heff_alloc(cap * sizeof *m);
    if (heff_capkq_owner) memcpy(m, heff_kq_owner, heff_capkq_owner * sizeof *m);
    memset(m + heff_capkq_owner, 0, (cap - heff_capkq_owner) * sizeof *m);
    free(heff_kq_owner);
    heff_kq_owner = m;
    heff_capkq_owner = cap;
  }
  if (heff_kq_owner[at]) {
    w->kway = 3;
    return;
  }
  struct kevent ch, got;
  EV_SET(&ch, (uintptr_t)w->fd, way == 1 ? EVFILT_READ : EVFILT_WRITE, EV_ADD | EV_RECEIPT, 0, 0, w);
  struct timespec zero = { 0, 0 };
  int r = kevent(heff_kq, &ch, 1, &got, 1, &zero);
  if (r < 0 || (r == 1 && (got.flags & EV_ERROR) && got.data != 0)) {
    w->kway = 3;
    return;
  }
  heff_kq_owner[at] = w;
  w->kway = way;
}

// (the wait's descriptor deleted from the kqueue, where it is there --
// closed meanwhile, the kernel deleted it then)
HEFF_FN void heff_kq_delete(HeffWait *w) {
  short way = w->kway;
  w->kway = 0;
  if (way != 1 && way != 2) return;
  size_t at = (size_t)w->kfd * 2 + (size_t)(way - 1);
  if (at < heff_capkq_owner && heff_kq_owner[at] == w) heff_kq_owner[at] = NULL;
  struct kevent ch;
  EV_SET(&ch, (uintptr_t)w->kfd, way == 1 ? EVFILT_READ : EVFILT_WRITE, EV_DELETE, 0, 0, NULL);
  struct timespec zero = { 0, 0 };
  (void)kevent(heff_kq, &ch, 1, NULL, 0, &zero);
}

// (the wait's way, after a step: where it waits on another descriptor,
// or the other way, or is done, so in the kqueue)
HEFF_FN void heff_kq_again(HeffWait *w) {
  short way = w->events == POLLIN ? 1 : w->events == POLLOUT ? 2 : 0;
  if (w->done || w->fd != w->kfd || (w->kway != 3 && way != w->kway)) {
    heff_kq_delete(w);
    heff_kq_add(w);
  }
}

// (the kqueue made, with the thread's first group, as its pipe is:
// where it cannot be, its waits polled)
HEFF_FN void heff_kq_open(void) {
  if (heff_kq_made) return;
  heff_kq = kqueue();
  if (heff_kq < 0) return;
  fcntl(heff_kq, F_SETFD, FD_CLOEXEC);
  heff_kq_made = 1;
}

// (the kqueue let go of, with the thread's last group: none of its
// waits pending)
HEFF_FN void heff_kq_close(void) {
  if (!heff_kq_made) return;
  close(heff_kq);
  heff_kq_made = 0;
  free(heff_kq_owner);
  heff_kq_owner = NULL;
  heff_capkq_owner = 0;
}
#endif

// (the group open of that number, or NULL)
HEFF_FN HeffGroup *heff_group_of(int64_t g) {
  for (size_t i = 0; i < heff_ngroups; i++)
    if (heff_groups_open[i].id == g) return &heff_groups_open[i];
  return NULL;
}

// (the group's pending, and its root's, `by` more)
HEFF_FN void heff_group_pending(int64_t id, int64_t by) {
  HeffGroup *g = heff_group_of(id);
  if (!g) return;
  g->pending += by;
  if (g->root) {
    HeffGroup *r = heff_group_of(g->root);
    if (r) r->pending += by;
  }
}

HEFF_FN void heff_wait_link(HeffWait *w) {
  w->prev = heff_waits_last;
  w->next = NULL;
  if (heff_waits_last) heff_waits_last->next = w;
  else heff_waits_first = w;
  heff_waits_last = w;
#ifndef _WIN32
  // (marked first, then the count read: a thread closing its descriptor
  // sees the mark, or this the close counted)
  w->marked = heff_mark_on(w->fd) ? w->fd : -1;
#endif
#ifdef HEFF_KQUEUE
  heff_kq_add(w);
#endif
  w->epoch = __atomic_load_n(&heff_closed_epoch, __ATOMIC_SEQ_CST);
  heff_group_pending(w->group, 1);
}

HEFF_FN void heff_wait_unlink(HeffWait *w) {
  if (w->prev) w->prev->next = w->next;
  else heff_waits_first = w->next;
  if (w->next) w->next->prev = w->prev;
  else heff_waits_last = w->prev;
  w->prev = w->next = NULL;
#ifndef _WIN32
  heff_mark_off(w->marked);
#endif
#ifdef HEFF_KQUEUE
  heff_kq_delete(w);
#endif
  heff_group_pending(w->group, -1);
}

// (a wait done, as its source says: given its answer at the next turn)
HEFF_FN void heff_wait_done(HeffWait *w) { w->done = 1; }

// (the waits on the descriptor `fd`, which is being closed: done, their
// answers that it was -- EBADF -- not a poll of a descriptor that may be
// another's by then)
HEFF_FN void heff_reactor_closing(int fd) {
  for (HeffWait *w = heff_waits_first; w; w = w->next)
    if (w->fd == fd && !w->done) {
      w->err = EBADF;
      w->done = 1;
    }
#ifndef _WIN32
  // (and every other thread's that waits on it, by that thread: told so,
  // and woken -- where none is marked, none told; a wait begun after the
  // marks are read is as one begun after the count: one on a descriptor
  // closed)
  if (fd < 0) return;
  uint64_t *word = heff_marks_of(fd, 0);
  int beyond = (size_t)fd >= (size_t)HEFF_MARK_CHUNK * HEFF_MARK_CHUNKS;
  uint64_t own = heff_mark == HEFF_MARK_ANY ? 0 : heff_mark;
  uint64_t others = beyond ? HEFF_MARK_ANY : word ? __atomic_load_n(word, __ATOMIC_SEQ_CST) & ~own : 0;
  if (!others) return;
  pthread_mutex_lock(&heff_wakers_mu);
  if (heff_nwakers) {
    int64_t e = __atomic_add_fetch(&heff_closed_epoch, 1, __ATOMIC_SEQ_CST);
    heff_closed[e % HEFF_CLOSED_KEPT].fd = fd;
    heff_closed[e % HEFF_CLOSED_KEPT].epoch = e;
    if (word) others |= __atomic_load_n(word, __ATOMIC_SEQ_CST) & ~own;
    char b = 0;
    if (others & HEFF_MARK_ANY) {
      for (size_t i = 0; i < heff_nwakers; i++)
        if (!heff_wake_made || heff_wakers[i].fd != heff_wake_fds[1]) {
          ssize_t r = write(heff_wakers[i].fd, &b, 1);
          (void)r;
        }
    } else
      for (int i = 0; i < 63; i++)
        if (others & heff_marks_given & ((uint64_t)1 << i)) {
          ssize_t r = write(heff_marks_pipe[i], &b, 1);
          (void)r;
        }
  }
  pthread_mutex_unlock(&heff_wakers_mu);
#endif
}

#ifndef _WIN32
// (the waits of this thread's on descriptors another thread closed since
// it last looked, each begun before it was closed: done, EBADF -- where
// any was, the poll to come not waiting)
HEFF_FN int heff_reactor_closed_elsewhere(void) {
  int64_t e = __atomic_load_n(&heff_closed_epoch, __ATOMIC_ACQUIRE);
  if (e == heff_closed_seen) return 0;
  int some = 0;
  pthread_mutex_lock(&heff_wakers_mu);
  e = heff_closed_epoch;
  int64_t from = heff_closed_seen + 1;
  if (e - from >= HEFF_CLOSED_KEPT) from = e - HEFF_CLOSED_KEPT + 1;
  for (int64_t k = from; k <= e; k++) {
    HeffClosed c = heff_closed[k % HEFF_CLOSED_KEPT];
    for (HeffWait *w = heff_waits_first; w; w = w->next)
      if (w->fd == c.fd && !w->done && w->epoch < c.epoch) {
        w->err = EBADF;
        w->done = 1;
        some = 1;
      }
  }
  pthread_mutex_unlock(&heff_wakers_mu);
  heff_closed_seen = e;
  return some;
}
#endif

#ifndef _WIN32
// (a source of waits, polled with the others from now on, by this thread)
HEFF_FN void heff_reactor_source(HeffSource *s) {
  if (s->on) return;
  s->on = 1;
  s->next = heff_sources;
  heff_sources = s;
}
#endif

// (the operation of the wait `w` -- its first step taken, not done --
// waited for here, or, in a group, pending: see above)
HEFF_FN V heff_outside(HeffWait *w, V f, V k) {
  if (heff_group) {
    w->f = f;
    w->k = k;
    w->group = heff_group;
    w->done = 0;
    heff_wait_link(w);
    return HEFF_PENDING;
  }
#ifndef _WIN32
  for (;;) {
    if (w->fd < 0 && !w->until) heff_fail("an outside operation waits for no descriptor, and no scheduler is there to wait for it");
    int ms = -1;
    if (w->until) {
      int64_t left = w->until - heff_now_ms();
      ms = left <= 0 ? 0 : left > INT_MAX ? INT_MAX : (int)left;
    }
    struct pollfd p = { w->fd, w->events, 0 };
    int r = poll(&p, w->fd >= 0 ? 1 : 0, ms);
    if (r < 0) {
      if (errno == EINTR) continue;
      w->err = errno;
      break;
    }
    if (r == 0) {
      if (w->until && heff_now_ms() >= w->until) {
        w->err = ETIMEDOUT;
        break;
      }
      continue;
    }
    if (w->step(w) == HEFF_STEP_DONE) break;
  }
#else
  if (w->fd < 0 && w->until) {
    int64_t left = w->until - heff_now_ms();
    if (left > 0) Sleep((DWORD)left);
  }
#endif
  V x = heff_answer(f, w->answer(w));
  return heff_tail(k, 1, &x);
}

// (what was started in group `g` come to its value `v`: one of the
// group's finished -- or, the group closed meanwhile, let go of)
HEFF_FN void heff_finished_put(int64_t g, V v) {
  HeffGroup *gr = heff_group_of(g);
  if (gr && gr->root) {
    g = gr->root;
    gr = heff_group_of(g);
  }
  if (!gr) {
    heff_drop(v);
    return;
  }
  if (heff_nfinished == heff_capfinished) {
    size_t cap = heff_capfinished ? heff_capfinished * 2 : 16;
    HeffFinished *m = heff_alloc(cap * sizeof *m);
    if (heff_nfinished) memcpy(m, heff_finished, heff_nfinished * sizeof *m);
    free(heff_finished);
    heff_finished = m;
    heff_capfinished = cap;
  }
  heff_finished[heff_nfinished].group = g;
  heff_finished[heff_nfinished].v = v;
  heff_nfinished++;
}

// (a function given its argument, and nothing else: where what is
// started comes to its end)
HEFF_FN V heff_kept(V self, V *a) {
  heff_drop(self);
  return a[0];
}

// (what a failure of a step of what group `g` started is finished as:
// its root's function, or 0)
HEFF_FN V heff_group_failed(int64_t g) {
  HeffGroup *gr = heff_group_of(g);
  if (gr && gr->root) gr = heff_group_of(gr->root);
  return gr ? gr->failed : 0;
}

// (`k` given `x`, a step of what group `g` started, run with the group
// as `heff_group`: what it comes to, at `*r`.  Where the group has a
// function for failures, under `heff_try`: one that fails is finished
// as that function's value, given why, and 1 is the answer; else 0.
// `k` and `x` consumed)
HEFF_FN int heff_group_step(int64_t g, V k, V x, V *r) {
  int64_t up = heff_group;
  heff_group = g;
  V failed = heff_group_failed(g);
  if (!failed) {
    *r = heff_tr(heff_app1(k, x));
    heff_group = up;
    return 0;
  }
  const char *why = heff_try(k, x, r);
  heff_group = up;
  if (!why) return 0;
  heff_finished_put(g, heff_tr(heff_app1(heff_dup(failed), heff_str_text(why))));
  return 1;
}

// (what group `g` started, the rest of it run in the group, from `k`
// given `x`: to its end, its value finished, or to a wait, pending; or,
// where the group says what a failure is, failed, that finished)
HEFF_FN void heff_reactor_run(int64_t g, V k, V x) {
  V r;
  if (heff_group_step(g, k, x, &r)) return;
  if (r != HEFF_PENDING) heff_finished_put(g, r);
}

// (group `g` among those woken by this thread's pipe)
HEFF_FN void heff_waker_add(int64_t g) {
#ifndef _WIN32
  if (!heff_wake_made) {
    if (pipe(heff_wake_fds) != 0) heff_fail("the reactor's pipe could not be made");
    for (int i = 0; i < 2; i++) {
      fcntl(heff_wake_fds[i], F_SETFL, fcntl(heff_wake_fds[i], F_GETFL) | O_NONBLOCK);
      fcntl(heff_wake_fds[i], F_SETFD, FD_CLOEXEC);
    }
    heff_wake_made = 1;
#ifdef HEFF_KQUEUE
    heff_kq_open();
#endif
  }
  pthread_mutex_lock(&heff_wakers_mu);
  if (heff_nwakers == heff_capwakers) {
    size_t cap = heff_capwakers ? heff_capwakers * 2 : 16;
    HeffWaker *m = heff_alloc(cap * sizeof *m);
    if (heff_nwakers) memcpy(m, heff_wakers, heff_nwakers * sizeof *m);
    free(heff_wakers);
    heff_wakers = m;
    heff_capwakers = cap;
  }
  heff_wakers[heff_nwakers].id = g;
  heff_wakers[heff_nwakers].fd = heff_wake_fds[1];
  heff_nwakers++;
  if (!heff_mark) {
    // (the reactor's bit, and its pipe by it; or, none left, the last)
    heff_mark = HEFF_MARK_ANY;
    for (int i = 0; i < 63; i++)
      if (!(heff_marks_given & ((uint64_t)1 << i))) {
        heff_marks_given |= (uint64_t)1 << i;
        heff_marks_pipe[i] = heff_wake_fds[1];
        heff_mark = (uint64_t)1 << i;
        break;
      }
  }
  pthread_mutex_unlock(&heff_wakers_mu);
#else
  (void)g;
#endif
}

// (group `g` no longer woken; with the thread's last group, its pipe
// closed)
HEFF_FN void heff_waker_remove(int64_t g) {
#ifndef _WIN32
  pthread_mutex_lock(&heff_wakers_mu);
  for (size_t i = 0; i < heff_nwakers; i++)
    if (heff_wakers[i].id == g) {
      heff_wakers[i] = heff_wakers[--heff_nwakers];
      break;
    }
  if (heff_ngroups == 0 && heff_wake_made) {
    close(heff_wake_fds[0]);
    close(heff_wake_fds[1]);
    heff_wake_made = 0;
    heff_woken = 0;
    // (its bit given back: no wait of its is pending, none marked)
    if (heff_mark != HEFF_MARK_ANY) heff_marks_given &= ~heff_mark;
    heff_mark = 0;
#ifdef HEFF_KQUEUE
    heff_kq_close();
#endif
  }
  pthread_mutex_unlock(&heff_wakers_mu);
#else
  (void)g;
#endif
}

// | The thread whose group `g`, a root, is woken, from any thread: its
// | reactor's next turn, or the one it is waiting in, comes back, and so
// | does `heff_reactor_finished`, with none finished where none is.
HEFF_FN void heff_reactor_wake_group(int64_t g) {
#ifndef _WIN32
  pthread_mutex_lock(&heff_wakers_mu);
  for (size_t i = 0; i < heff_nwakers; i++)
    if (heff_wakers[i].id == g) {
      char b = 0;
      ssize_t r = write(heff_wakers[i].fd, &b, 1);
      (void)r;
      break;
    }
  pthread_mutex_unlock(&heff_wakers_mu);
#else
  (void)g;
#endif
}

// (a group of this thread's, of a number no other has, within the root
// `root` or 0)
HEFF_FN int64_t heff_group_made(int64_t root) {
  if (heff_ngroups == heff_capgroups) {
    size_t cap = heff_capgroups ? heff_capgroups * 2 : 8;
    HeffGroup *m = heff_alloc(cap * sizeof *m);
    if (heff_ngroups) memcpy(m, heff_groups_open, heff_ngroups * sizeof *m);
    free(heff_groups_open);
    heff_groups_open = m;
    heff_capgroups = cap;
  }
  int64_t g = __atomic_add_fetch(&heff_last_group, 1, __ATOMIC_RELAXED);
  heff_groups_open[heff_ngroups].id = g;
  heff_groups_open[heff_ngroups].pending = 0;
  heff_groups_open[heff_ngroups].root = root;
  heff_groups_open[heff_ngroups].failed = 0;
  heff_groups_open[heff_ngroups].giving = 0;
  heff_ngroups++;
  // (a root alone is woken: one within it is waited on with it)
  if (!root) heff_waker_add(g);
  return g;
}

// | A group of its own, for a scheduler: its number.  `failed`, where it
// | is not 0, is what a step of a computation started in it that fails
// | is finished as, given why, the others going on (kept by the group,
// | and let go of when it is closed); where it is 0, the failure is the
// | program's.
HEFF_FN int64_t heff_reactor_open(V failed) {
  int64_t g = heff_group_made(0);
  heff_group_of(g)->failed = failed;
  return g;
}

// | A group within group `g`: what is started in it finishes among the
// | finished of `g`'s root, and is pending among its pending.
HEFF_FN int64_t heff_reactor_open_within(int64_t g) {
  HeffGroup *gr = heff_group_of(g);
  if (!gr) heff_fail("a group within one that is not open");
  return heff_group_made(gr->root ? gr->root : g);
}

// | `c`, a computation of the world (its handler's monad: a function of
// | its continuation), started in group `g`: run to its end, its value;
// | or to a wait, `HEFF_PENDING`, its value to be one of the group's
// | finished.  `c` consumed.
HEFF_FN V heff_reactor_start(int64_t g, V c) {
  int64_t up = heff_group;
  heff_group = g;
  V r = heff_tr(heff_app1(c, heff_clo(heff_kept, 1, 0, NULL)));
  heff_group = up;
  return r;
}

// (the waits done -- stepped done, or said so -- taken out of the
// pending, then each given its answer, the rest of what it was started
// in run, in the order they were pending)
HEFF_FN void heff_reactor_wake(void) {
  HeffWait *first = NULL, *last = NULL;
  for (HeffWait *w = heff_waits_first, *next; w; w = next) {
    next = w->next;
    if (!w->done) continue;
    heff_wait_unlink(w);
    if (last) last->next = w;
    else first = w;
    last = w;
  }
  for (HeffWait *w = first, *next; w; w = next) {
    next = w->next;
    V f = w->f, k = w->k;
    int64_t g = w->group;
    V x = heff_answer(f, w->answer(w));
    heff_reactor_run(g, k, x);
  }
}

// (the waits whose deadline has passed: done, timed out -- a sleep's
// answer minds it not)
HEFF_FN void heff_reactor_expire(void) {
  int64_t now = heff_now_ms();
  for (HeffWait *w = heff_waits_first; w; w = w->next)
    if (!w->done && w->until && now >= w->until) {
      if (!w->err) w->err = ETIMEDOUT;
      w->done = 1;
    }
}

#ifndef _WIN32
// (room for `n` descriptors polled)
HEFF_FN void heff_polled_room(size_t n) {
  if (n <= heff_cappolled && heff_polled) return;
  size_t cap = heff_cappolled ? heff_cappolled : 64;
  while (cap < n) cap *= 2;
  free(heff_polled);
  free(heff_polled_waits);
  heff_polled = heff_alloc(cap * sizeof *heff_polled);
  heff_polled_waits = heff_alloc(cap * sizeof *heff_polled_waits);
  heff_cappolled = cap;
}

// (whether the wait's descriptor is polled by the turn: where there is
// no kqueue, every pending one's; else those kqueue was not given)
static inline int heff_wait_polled(HeffWait *w) {
#ifdef HEFF_KQUEUE
  return !w->done && w->fd >= 0 && w->kway == 3;
#else
  return !w->done && w->fd >= 0;
#endif
}

// (the wait stepped, its descriptor ready: done, or waiting again, maybe
// on another)
static inline void heff_wait_ready(HeffWait *w) {
  if (!w->done && w->step(w) == HEFF_STEP_DONE) w->done = 1;
  if (w->fd != w->marked) {
    // (a step on to another descriptor: its reactor marked so)
    heff_mark_off(w->marked);
    w->marked = heff_mark_on(w->fd) ? w->fd : -1;
  }
#ifdef HEFF_KQUEUE
  heff_kq_again(w);
#endif
}

#ifdef HEFF_KQUEUE
// (the kqueue's ready read, not waiting, and each ready wait stepped)
HEFF_FN void heff_kq_ready(void) {
  struct kevent got[256];
  struct timespec zero = { 0, 0 };
  for (;;) {
    int r = kevent(heff_kq, NULL, 0, got, 256, &zero);
    if (r <= 0) break;
    for (int i = 0; i < r; i++) {
      HeffWait *w = got[i].udata;
      // (one whose way was deleted by an earlier step of this read: not
      // its event any more)
      short way = got[i].filter == EVFILT_READ ? 1 : 2;
      if (w && w->kway == way && w->kfd == (int)got[i].ident) heff_wait_ready(w);
    }
    if (r < 256) break;
  }
}
#endif

// (one turn: every pending wait's descriptor and every source's polled
// -- for as long as they say, where `wait`, else not waiting -- each
// ready stepped, and those done woken)
HEFF_FN void heff_reactor_turn(int wait) {
  size_t n = 0;
  int ms = wait ? -1 : 0;
  if (heff_reactor_closed_elsewhere()) ms = 0;
  int64_t now = heff_now_ms();
  for (HeffWait *w = heff_waits_first; w; w = w->next) {
    if (w->done) ms = 0;
    else {
      if (heff_wait_polled(w)) n++;
      if (w->until) {
        int64_t left = w->until > now ? w->until - now : 0;
        if (ms < 0 || left < ms) ms = left > INT_MAX ? INT_MAX : (int)left;
      }
    }
  }
  size_t mine = n;
#ifdef HEFF_KQUEUE
  if (heff_kq_made) n++;
#endif
  if (heff_wake_made) n++;
  for (HeffSource *s = heff_sources; s; s = s->next) {
    int t = -1;
    s->n = s->fds(NULL, 0, &t);
    n += (size_t)s->n;
  }
  heff_polled_room(n);
  n = 0;
  for (HeffWait *w = heff_waits_first; w; w = w->next)
    if (heff_wait_polled(w)) {
      heff_polled[n].fd = w->fd;
      heff_polled[n].events = w->events;
      heff_polled[n].revents = 0;
      heff_polled_waits[n] = w;
      n++;
    }
#ifdef HEFF_KQUEUE
  // (the kqueue as it is now: a step below may make it)
  size_t kq = n;
  int kq_polled = heff_kq_made;
  if (kq_polled) {
    heff_polled[n].fd = heff_kq;
    heff_polled[n].events = POLLIN;
    heff_polled[n].revents = 0;
    n++;
  }
#endif
  size_t wake = n;
  if (heff_wake_made) {
    heff_polled[n].fd = heff_wake_fds[0];
    heff_polled[n].events = POLLIN;
    heff_polled[n].revents = 0;
    n++;
  }
  for (HeffSource *s = heff_sources; s; s = s->next) {
    int t = -1;
    s->at = n;
    s->fds(heff_polled + n, s->n, &t);
    for (int i = 0; i < s->n; i++) heff_polled[n + (size_t)i].revents = 0;
    n += (size_t)s->n;
    if (t >= 0 && (ms < 0 || t < ms)) ms = t;
  }
  if (n == 0 && ms < 0) heff_fail("the reactor waits, with nothing to wait for");
  int r = poll(heff_polled, (nfds_t)n, ms);
  if (r < 0 && errno != EINTR) heff_fail("the reactor's poll failed");
  if (r < 0) for (size_t i = 0; i < n; i++) heff_polled[i].revents = 0;
  for (size_t i = 0; i < mine; i++)
    if (heff_polled[i].revents) heff_wait_ready(heff_polled_waits[i]);
#ifdef HEFF_KQUEUE
  if (kq_polled && heff_polled[kq].revents) heff_kq_ready();
#endif
  if (heff_wake_made && heff_polled[wake].revents) {
    char b[64];
    while (read(heff_wake_fds[0], b, sizeof b) > 0) {}
    heff_woken = 1;
  }
  for (HeffSource *s = heff_sources; s; s = s->next) s->ready(heff_polled + s->at, s->n);
  heff_reactor_expire();
  heff_reactor_wake();
}
#else
// (no descriptor is polled: the deadlines alone are waited for)
HEFF_FN void heff_reactor_turn(int wait) {
  int64_t now = heff_now_ms(), ms = wait ? -1 : 0;
  for (HeffWait *w = heff_waits_first; w; w = w->next) {
    if (w->done) ms = 0;
    else if (w->until) {
      int64_t left = w->until > now ? w->until - now : 0;
      if (ms < 0 || left < ms) ms = left;
    }
  }
  if (ms < 0) heff_fail("the reactor waits, with nothing to wait for");
  if (ms > 0) Sleep((DWORD)ms);
  heff_reactor_expire();
  heff_reactor_wake();
}
#endif

// | Group `g`'s finished, since it was last asked, in the order they
// | were: where `wait`, waiting for one at least while any of it is
// | pending; none where none is.
HEFF_FN void heff_giving_taken(void);

HEFF_FN V heff_reactor_finished(int64_t g, int wait) {
  for (;;) {
    heff_giving_taken();
    int some = 0;
    for (size_t i = 0; i < heff_nfinished && !some; i++) some = heff_finished[i].group == g;
    HeffGroup *gr = heff_group_of(g);
    if (some || !gr || gr->pending == 0) break;
#ifndef _WIN32
    if (heff_woken) break;
#endif
    heff_reactor_turn(wait);
    if (!wait) break;
  }
#ifndef _WIN32
  heff_woken = 0;
#endif
  // (the group's taken, in order; the others' kept, in theirs)
  V l = NTAG(TAG_Nil);
  for (size_t i = heff_nfinished; i-- > 0;)
    if (heff_finished[i].group == g) l = heff_cons(heff_finished[i].v, l);
  size_t kept = 0;
  for (size_t i = 0; i < heff_nfinished; i++)
    if (heff_finished[i].group != g) heff_finished[kept++] = heff_finished[i];
  heff_nfinished = kept;
  return l;
}

// | How many of group `g`'s computations started are pending: in a
// | root, those of the groups within it too; 0 where it is not open.
HEFF_FN int64_t heff_reactor_pending(int64_t g) {
  HeffGroup *gr = heff_group_of(g);
  return gr ? gr->pending : 0;
}

// | Group `g` closed: what is pending in it let go of, undone, and what
// | of it is finished and not asked for.
HEFF_FN int heff_group_in(int64_t id, int64_t g) {
  if (id == g) return 1;
  HeffGroup *gr = heff_group_of(id);
  return gr && gr->root == g;
}

HEFF_FN void heff_giving_closed(int64_t g);

HEFF_FN void heff_reactor_close(int64_t g) {
  heff_giving_closed(g);
  for (HeffWait *w = heff_waits_first, *next; w; w = next) {
    next = w->next;
    if (!heff_group_in(w->group, g)) continue;
    heff_wait_unlink(w);
    V f = w->f, k = w->k;
    w->cancel(w);
    heff_drop(f);
    heff_drop(k);
  }
  size_t kept = 0;
  for (size_t i = 0; i < heff_nfinished; i++) {
    if (heff_finished[i].group == g) heff_drop(heff_finished[i].v);
    else heff_finished[kept++] = heff_finished[i];
  }
  heff_nfinished = kept;
  for (size_t i = 0; i < heff_ngroups;) {
    int64_t id = heff_groups_open[i].id, root = heff_groups_open[i].root;
    if (id == g || root == g) {
      if (heff_groups_open[i].failed) heff_drop(heff_groups_open[i].failed);
      heff_groups_open[i] = heff_groups_open[--heff_ngroups];
      // (a root's waker taken out; and, with the thread's last group,
      // its pipe closed)
      if (!root || heff_ngroups == 0) heff_waker_remove(id);
    } else i++;
  }
}

// Giving a group up from any thread
// ---------------------------------------------------------------------
//
// A group within another is given up from any thread by what gives it
// up (`heff_reactor_giving`): a foreign value -- a thing a custodian can
// have in its custody -- made with a value of the group's, `gave`.
// Ended, by a custodian's shutdown or as its last reference is dropped,
// it asks the thread whose group it is to give the group up, and wakes
// that thread.  The thread does at its next look at its finished
// (`heff_giving_taken`, at a point where no wait of its is being
// stepped): where any of the group is pending, the group is closed, what
// is pending in it let go of, undone, and `gave` is among its root's
// finished instead, so that what counts the computations started knows
// that one is done; where none is -- what was started came to its
// value, or failed, already -- the group is closed alone.  A group
// closed, by any means, is given up no more.  The asking is under a lock
// of its own: the group is its thread's, the thing anyone's.

struct HeffGiving {
  int64_t group, root;
  int state;                     // (0 open; 1 asked to be given up, among
                                 //  those asked once the lock is had; 2
                                 //  taken by its thread; 3 closed: from 0,
                                 //  by a `cas`, else under the lock)
  int refs;                      // (the thing's, and the group's while it
                                 //  is open: counted atomically)
  V gave;
  HeffGiving *next;              // (among those asked)
};

#ifdef HEFF_PART
extern HeffGiving *heff_giving_asked;
extern int64_t heff_giving_n;
extern pthread_mutex_t heff_giving_mu;
#else
HeffGiving *heff_giving_asked;
int64_t heff_giving_n;
pthread_mutex_t heff_giving_mu = PTHREAD_MUTEX_INITIALIZER;
#endif

// (one of its holders let go of it: freed by the last)
HEFF_FN void heff_giving_unref(HeffGiving *gv) {
  if (__atomic_sub_fetch(&gv->refs, 1, __ATOMIC_ACQ_REL) > 0) return;
  V gave = gv->gave;
  free(gv);
  heff_drop(gave);
}

// (it taken out of those asked; the lock held)
HEFF_FN void heff_giving_unasked(HeffGiving *gv) {
  for (HeffGiving **at = &heff_giving_asked; *at; at = &(*at)->next)
    if (*at == gv) {
      *at = gv->next;
      __atomic_sub_fetch(&heff_giving_n, 1, __ATOMIC_RELEASE);
      return;
    }
}

// (its end, from any thread: its group asked to be given up, and its
// thread woken, where it is open)
static const char *heff_giving_end(void *p) {
  HeffGiving *gv = p;
  int open = 0, asked = 0;
  if (!__atomic_compare_exchange_n(&gv->state, &open, 1, 0, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE))
    return NULL;
  pthread_mutex_lock(&heff_giving_mu);
  // (not closed meanwhile, by its thread)
  if (__atomic_load_n(&gv->state, __ATOMIC_ACQUIRE) == 1) {
    gv->next = heff_giving_asked;
    heff_giving_asked = gv;
    __atomic_add_fetch(&heff_giving_n, 1, __ATOMIC_RELEASE);
    asked = 1;
  }
  pthread_mutex_unlock(&heff_giving_mu);
  if (asked) heff_reactor_wake_group(gv->root);
  return NULL;
}

static void heff_giving_let_go(void *p) { heff_giving_unref(p); }

// | What gives up group `g`, a group within another of this thread's,
// | from any thread: `gave`, its value where it is given up while any
// | of it is pending, finished in its root.  `gave` consumed.
HEFF_FN V heff_reactor_giving(int64_t g, V gave) {
  HeffGroup *gr = heff_group_of(g);
  if (!gr || !gr->root) heff_fail("a group given up that is not one within another");
  if (gr->giving) heff_fail("a group given up by two things");
  HeffGiving *gv = heff_alloc(sizeof *gv);
  gv->group = g;
  gv->root = gr->root;
  gv->state = 0;
  gv->refs = 2;
  gv->gave = heff_share(gave);
  gv->next = NULL;
  gr->giving = gv;
  return heff_foreign_ending(gv, heff_giving_let_go, heff_giving_end);
}

// (the groups `g` closes -- it, and those within it -- given up no
// more, let go of by them: before what is pending in them is, as what
// that lets go of may hold what gives one up)
HEFF_FN void heff_giving_closed(int64_t g) {
  for (size_t i = 0; i < heff_ngroups; i++) {
    HeffGroup *gr = &heff_groups_open[i];
    if (!gr->giving || (gr->id != g && gr->root != g)) continue;
    HeffGiving *gv = gr->giving;
    gr->giving = 0;
    int open = 0;
    if (!__atomic_compare_exchange_n(&gv->state, &open, 3, 0, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) {
      pthread_mutex_lock(&heff_giving_mu);
      if (__atomic_load_n(&gv->state, __ATOMIC_ACQUIRE) == 1) heff_giving_unasked(gv);
      __atomic_store_n(&gv->state, 3, __ATOMIC_RELEASE);
      pthread_mutex_unlock(&heff_giving_mu);
    }
    heff_giving_unref(gv);
  }
}

// | The groups of this thread's asked to be given up, given up: each
// | closed, and, where any of it was pending, what it gave finished in
// | its root.
HEFF_FN void heff_giving_taken(void) {
  if (__atomic_load_n(&heff_giving_n, __ATOMIC_ACQUIRE) == 0) return;
  HeffGiving *mine = NULL;
  pthread_mutex_lock(&heff_giving_mu);
  for (HeffGiving **at = &heff_giving_asked; *at;) {
    HeffGiving *gv = *at;
    HeffGroup *gr = heff_group_of(gv->group);
    if (gr && gr->giving == gv) {
      *at = gv->next;
      __atomic_sub_fetch(&heff_giving_n, 1, __ATOMIC_RELEASE);
      __atomic_store_n(&gv->state, 2, __ATOMIC_RELEASE);
      gv->next = mine;
      mine = gv;
    } else at = &gv->next;
  }
  pthread_mutex_unlock(&heff_giving_mu);
  while (mine) {
    HeffGiving *gv = mine;
    mine = gv->next;
    HeffGroup *gr = heff_group_of(gv->group);
    if (!gr) continue;
    int64_t root = gr->root;
    V gave = gr->pending > 0 ? heff_dup(gv->gave) : 0;
    heff_reactor_close(gv->group);
    if (gave) heff_finished_put(root, gave);
  }
}

// Running
// ---------------------------------------------------------------------

HEFF_FN V heff_nomatch(V s) {
  (void)s;
  heff_fail("no case for a tag");
  return 0;
}

// Values, shown (`heff dump-c`: each definition of
// the file printed as the tests print JavaScript's)
// ---------------------------------------------------------------------

// (the names of the tags and labels, each by its number: a tag's and a
// label's number is a hash of its name)
typedef struct { uint32_t id; const char *name; } HeffName;
HEFF_VAR(const HeffName *heff_tag_names);
HEFF_VAR(int heff_ntag_names);
HEFF_VAR(const HeffName *heff_lbl_names);
HEFF_VAR(int heff_nlbl_names);

HEFF_FN const char *heff_name_of(const HeffName *t, int n, uint32_t id) {
  for (int i = 0; i < n; i++) if (t[i].id == id) return t[i].name;
  return "?";
}

typedef struct { char *s; size_t n, cap; } Buf;

HEFF_FN void buf_put(Buf *b, const char *c, size_t n) {
  if (b->n + n + 1 > b->cap) {
    size_t cap = (b->cap ? b->cap * 2 : 256);
    while (cap < b->n + n + 1) cap *= 2;
    char *s = heff_alloc(cap);
    if (b->n) memcpy(s, b->s, b->n);
    free(b->s);
    b->s = s; b->cap = cap;
  }
  memcpy(b->s + b->n, c, n);
  b->n += n;
  b->s[b->n] = 0;
}

// (content in, `f` read to its end, as a string: straight into it where
// `size`, what the file says it holds, is all there is, else through a
// buffer; 0, where a read failed)
HEFF_FN V heff_str_read(FILE *f, int64_t size) {
  Buf b = {0};
  if (size > 0) {
    Str *s = heff_str_new(size);
    size_t got = fread(s->s, 1, (size_t)size, f);
    int c = got == (size_t)size ? fgetc(f) : EOF;
    if (c == EOF) {
      if (ferror(f)) { heff_drop((V)s); return 0; }
      s->len = (int64_t)got;
      return (V)s;
    }
    // (more than it said: what was read, and the rest, through the buffer)
    char more = (char)c;
    buf_put(&b, (const char *)s->s, got);
    buf_put(&b, &more, 1);
    heff_drop((V)s);
  }
  char chunk[65536];
  size_t got;
  while ((got = fread(chunk, 1, sizeof chunk, f)) > 0) buf_put(&b, chunk, got);
  V s = ferror(f) ? 0 : heff_str_bytes(b.s ? b.s : "", (int64_t)b.n);
  free(b.s);
  return s;
}

HEFF_FN void buf_str(Buf *b, const char *c) { buf_put(b, c, strlen(c)); }

// Commands
// ---------------------------------------------------------------------

#ifdef _WIN32
// (a command line of `as`, each quoted as the C runtime's parser reads it
// back: malloc'd)
HEFF_FN char *heff_command_line(char **as) {
  Buf b = {0};
  for (char **a = as; *a; a++) {
    if (a != as) buf_put(&b, " ", 1);
    const char *s = *a;
    if (*s && !strpbrk(s, " \t\n\v\"")) { buf_str(&b, s); continue; }
    buf_put(&b, "\"", 1);
    for (;;) {
      size_t slashes = 0;
      while (*s == '\\') { s++; slashes++; }
      if (!*s) {
        for (size_t i = 0; i < slashes * 2; i++) buf_put(&b, "\\", 1);
        break;
      }
      size_t k = *s == '"' ? slashes * 2 + 1 : slashes;
      for (size_t i = 0; i < k; i++) buf_put(&b, "\\", 1);
      buf_put(&b, s++, 1);
    }
    buf_put(&b, "\"", 1);
  }
  buf_put(&b, "", 1);
  return b.s;
}

typedef struct { HANDLE h; Buf *b; } HeffDrain;

// (all a pipe gives, until it is closed)
HEFF_FN DWORD WINAPI heff_drain(LPVOID u) {
  HeffDrain *d = u;
  char chunk[65536];
  DWORD got;
  while (ReadFile(d->h, chunk, sizeof chunk, &got, NULL) && got > 0) buf_put(d->b, chunk, got);
  return 0;
}

// (a command started, its stdin this program's, its stdout and stderr
// `out` and `err`, or 0 if it cannot be)
HEFF_FN HANDLE heff_spawn(char **as, HANDLE out, HANDLE err) {
  char *line = heff_command_line(as);
  STARTUPINFOA si;
  memset(&si, 0, sizeof si);
  si.cb = sizeof si;
  si.dwFlags = STARTF_USESTDHANDLES;
  si.hStdInput = GetStdHandle(STD_INPUT_HANDLE);
  si.hStdOutput = out;
  si.hStdError = err;
  PROCESS_INFORMATION pi;
  int ok = CreateProcessA(NULL, line, NULL, NULL, TRUE, 0, NULL, heff_working_dir(), &si, &pi);
  free(line);
  if (!ok) return 0;
  CloseHandle(pi.hThread);
  return pi.hProcess;
}

// (a command's exit code once it has ended)
HEFF_FN int64_t heff_wait(HANDLE h) {
  DWORD code = (DWORD)-1;
  WaitForSingleObject(h, INFINITE);
  GetExitCodeProcess(h, &code);
  CloseHandle(h);
  return (int64_t)code;
}
#else
// (what a command writes, both streams read together, so that neither
// fills its pipe while the other is waited for)
HEFF_FN void heff_read_both(int out, int err, Buf *bo, Buf *be) {
  struct pollfd fds[2] = { { out, POLLIN, 0 }, { err, POLLIN, 0 } };
  int open = 2;
  char chunk[65536];
  while (open > 0) {
    if (poll(fds, 2, -1) < 0) break;
    for (int i = 0; i < 2; i++) {
      if (fds[i].fd < 0 || !(fds[i].revents & (POLLIN | POLLHUP))) continue;
      ssize_t got = read(fds[i].fd, chunk, sizeof chunk);
      if (got <= 0) { close(fds[i].fd); fds[i].fd = -1; open--; }
      else buf_put(i == 0 ? bo : be, chunk, (size_t)got);
    }
  }
}

#endif

// (the command `as` (a NULL-ended array, its name first, found on the
// PATH) run, its stdin this program's, what it writes to stdout and
// stderr gathered in `bo` and `be`: its exit status, -1 if it could not
// be run)
HEFF_FN int64_t heff_capture(char **as, Buf *bo, Buf *be) {
  int64_t status = -1;
#ifdef _WIN32
  SECURITY_ATTRIBUTES sa = { sizeof sa, NULL, TRUE };
  HANDLE or_, ow, er, ew;
  if (CreatePipe(&or_, &ow, &sa, 0) && CreatePipe(&er, &ew, &sa, 0)) {
    SetHandleInformation(or_, HANDLE_FLAG_INHERIT, 0);
    SetHandleInformation(er, HANDLE_FLAG_INHERIT, 0);
    HANDLE h = heff_spawn(as, ow, ew);
    CloseHandle(ow);
    CloseHandle(ew);
    HeffDrain de = { er, be }, dout = { or_, bo };
    HANDLE t = CreateThread(NULL, 0, heff_drain, &de, 0, NULL);
    heff_drain(&dout);
    if (t) { WaitForSingleObject(t, INFINITE); CloseHandle(t); }
    else heff_drain(&de);
    CloseHandle(or_);
    CloseHandle(er);
    if (h) status = heff_wait(h);
  }
#else
  int po[2], pe[2];
  if (pipe(po) == 0 && pipe(pe) == 0) {
    int closed[2] = { po[0], pe[0] };
    pid_t pid = heff_exec_in_dir(as, NULL, -1, po[1], pe[1], closed, 2);
    int ok = pid > 0;
    close(po[1]);
    close(pe[1]);
    heff_read_both(po[0], pe[0], bo, be);
    if (ok) {
      int st;
      if (waitpid(pid, &st, 0) >= 0 && WIFEXITED(st)) status = WEXITSTATUS(st);
    }
  }
#endif
  return status;
}

// (a string as JSON writes one: in quotes, `"` `\` and controls escaped;
// what is not UTF-8 in it U+FFFD -- or, `shown`, each of its bytes
// `\xnn`, as a string literal writes it)
HEFF_FN void buf_json_string_as(Buf *b, V v, int shown) {
  Str *s = (Str *)v;
  buf_str(b, "\"");
  for (int64_t i = 0; i < s->len; i++) {
    uint32_t u = s->p[i];
    char tmp[16];
    if (u >= 0x80) {
      int w = heff_u8_decode(s->p + i, s->len - i, &u);
      if (heff_u8_own(s->p + i, u, w)) buf_put(b, (const char *)s->p + i, (size_t)w);
      else if (!shown) buf_str(b, "\xEF\xBF\xBD");
      else for (int k = 0; k < w; k++) { snprintf(tmp, sizeof tmp, "\\x%02x", s->p[i + k]); buf_str(b, tmp); }
      i += w - 1;
    }
    else if (u == '"') buf_str(b, "\\\"");
    else if (u == '\\') buf_str(b, "\\\\");
    else if (u == '\n') buf_str(b, "\\n");
    else if (u == '\t') buf_str(b, "\\t");
    else if (u == '\r') buf_str(b, "\\r");
    else if (u == '\b') buf_str(b, "\\b");
    else if (u == '\f') buf_str(b, "\\f");
    else if (u < 0x20) { snprintf(tmp, sizeof tmp, "\\u%04x", u); buf_str(b, tmp); }
    else { char o = (char)u; buf_put(b, &o, 1); }
  }
  buf_str(b, "\"");
}

HEFF_FN void buf_json_string(Buf *b, V v) { buf_json_string_as(b, v, 0); }

// (a tag of that name and that many arguments, its arguments `*fs`)
HEFF_FN int heff_tag_named(V v, const char *name, int n, V **fs) {
  int tag, m = 0;
  V *f = NULL;
  if (IS_NTAG(v)) tag = (int)(v >> 2);
  else if (IS_OBJ(v) && (OBJ(v)->kind == K_TAG || OBJ(v)->kind == K_TAGF)) { tag = OBJ(v)->tag; m = (int)((Tag *)v)->n; f = ((Tag *)v)->f; }
  else return 0;
  if (m != n || strcmp(heff_name_of(heff_tag_names, heff_ntag_names, (uint32_t)tag), name)) return 0;
  *fs = f;
  return 1;
}

// (a list, `Cons a (Cons b Nil)`: whether it is one, a chain that ends
// in `Nil`)
HEFF_FN int heff_is_list(V v) {
  V *f;
  while (heff_tag_named(v, "Cons", 2, &f)) v = f[1];
  return heff_tag_named(v, "Nil", 0, &f);
}

// (the `len` bytes at `p` as the prelude's `showBytes` writes them in a
// binary, `b[...]`: each run of printable ASCII a string, `"` and `\`
// escaped, any other byte its number; whether any is written)
HEFF_FN int heff_show_byte_pieces(Buf *b, const uint8_t *p, int64_t len) {
  int run = 0, any = 0;
  for (int64_t i = 0; i < len; i++) {
    uint8_t c = p[i];
    if (c >= 0x20 && c < 0x7f) {
      if (!run) { buf_str(b, any ? ", \"" : "\""); run = any = 1; }
      if (c == '"') buf_str(b, "\\\"");
      else if (c == '\\') buf_str(b, "\\\\");
      else { char o = (char)c; buf_put(b, &o, 1); }
    } else {
      char tmp[8];
      if (run) { buf_str(b, "\""); run = 0; }
      snprintf(tmp, sizeof tmp, "%s%u", any ? ", " : "", (unsigned)c);
      buf_str(b, tmp);
      any = 1;
    }
  }
  if (run) buf_str(b, "\"");
  return any;
}

HEFF_FN void heff_show_bytes(Buf *b, V v) {
  Str *s = (Str *)v;
  buf_str(b, "b[");
  heff_show_byte_pieces(b, s->p, s->len);
  buf_str(b, "]");
}

// (bits as the prelude's `showBits` writes them: their whole bytes as
// bytes are, then the bits left, `v::k`, or, none left, `b[]::bits`)
HEFF_FN void heff_show_bits(Buf *b, V v) {
  Str *s = (Str *)v;
  int64_t k = (8 - (int64_t)s->h.tag) & 7, whole = k ? s->len - 1 : s->len;
  char tmp[32];
  buf_str(b, "b[");
  int any = heff_show_byte_pieces(b, s->p, whole);
  if (k) snprintf(tmp, sizeof tmp, "%s%u::%d", any ? ", " : "", (unsigned)(s->p[whole] >> (8 - k)), (int)k);
  else snprintf(tmp, sizeof tmp, "%sb[]::bits", any ? ", " : "");
  buf_str(b, tmp);
  buf_str(b, "]");
}

HEFF_FN void heff_show(Buf *b, V v, int arg);

// (field `i` of the tag `v` shown, as a `V`: boxed, if it is flat, #64)
HEFF_FN void heff_show_field(Buf *b, V v, int i, int arg) {
  V x = heff_tget_v(v, i);
  heff_show(b, x, arg);
  heff_drop(x);
}

HEFF_FN void heff_show(Buf *b, V v, int arg) {
  char tmp[64];
  if (heff_is_list(v)) {
    V *f;
    buf_str(b, "[");
    for (int i = 0; heff_tag_named(v, "Cons", 2, &f); i++, v = f[1]) {
      if (i) buf_str(b, ", ");
      heff_show_field(b, v, 0, 0);
    }
    buf_str(b, "]");
    return;
  }
  if (IS_INT(v) || (IS_OBJ(v) && OBJ(v)->kind == K_BIG)) {
    char w[24], *c = IS_INT(v) ? heff_word_digits(INT_OF(v), w + sizeof w - 1) : heff_int_cstr(v);
    w[sizeof w - 1] = 0;
    if (arg && c[0] == '-') { buf_str(b, "("); buf_str(b, c); buf_str(b, ")"); }
    else buf_str(b, c);
    if (!IS_INT(v)) free(c);
    return;
  }
  int tag = -1, n = 0;
  V *fs = NULL;
  if (IS_NTAG(v)) tag = (int)(v >> 2);
  else {
    Obj *o = OBJ(v);
    switch (o->kind) {
    case K_TAG: case K_TAGF: tag = o->tag; n = (int)((Tag *)v)->n; fs = ((Tag *)v)->f; break;
    case K_FLT: {
      heff_show_float(FLT_OF(v), tmp);
      if (arg && tmp[0] == '-') { buf_str(b, "("); buf_str(b, tmp); buf_str(b, ")"); }
      else buf_str(b, tmp);
      return;
    }
    case K_STR: buf_json_string_as(b, v, 1); return;
    case K_BYT: heff_show_bytes(b, v); return;
    case K_BIT: heff_show_bits(b, v); return;
    case K_FGN: buf_str(b, "#foreign"); return;
    case K_ARR: {
      Arr *r = (Arr *)v;
      buf_str(b, "[");
      for (int64_t i = 0; i < r->n; i++) {
        if (i) buf_str(b, ", ");
        V x = heff_arr_get(r, i);
        heff_show(b, x, 0);
        heff_drop(x);
      }
      buf_str(b, "]");
      return;
    }
    case K_REC: {
      Rec *r = (Rec *)v;
      buf_str(b, "{ ");
      for (int64_t i = 0; i < r->n; i++) {
        if (i) buf_str(b, ", ");
        buf_str(b, heff_name_of(heff_lbl_names, heff_nlbl_names, r->lbl[i]));
        buf_str(b, " = ");
        V x = heff_rec_dup_field(r, i);
        heff_show(b, x, 0);
        heff_drop(x);
      }
      buf_str(b, " }");
      return;
    }
    default: buf_str(b, "#fun"); return;
    }
  }
  const char *name = heff_name_of(heff_tag_names, heff_ntag_names, (uint32_t)tag);
  if (n && arg) buf_str(b, "(");
  buf_str(b, name);
  for (int i = 0; i < n; i++) { buf_str(b, " "); heff_show_field(b, v, i, 1); }
  if (n && arg) buf_str(b, ")");
}

// (a definition by its name, the file's own, `heff_globals`; its value
// asked for, the thing it is shown, or why it failed)
typedef struct { const char *name; V (*get)(void); } Global;

HEFF_FN void heff_check_one(Buf *out, const Global *g) {
  jmp_buf here;
  heff_catch = &here;
  Buf b = {0};
  buf_str(out, "\"");
  buf_str(out, g->name);
  buf_str(out, "\": ");
  if (HEFF_SETJMP(here) == 0) {
    V v = heff_tr(g->get());
    heff_show(&b, v, 0);
    buf_str(out, "{\"value\": ");
    V s = heff_str_bytes(b.s, (int64_t)b.n);
    buf_json_string(out, s);
    heff_drop(s);
    buf_str(out, "}");
  } else {
    buf_str(out, "{\"threw\": ");
    buf_json_string(out, heff_str_ascii(heff_caught));
    buf_str(out, "}");
  }
  heff_catch = NULL;
}

HEFF_VAR(int heff_argc);
HEFF_VAR(char **heff_argv);
HEFF_VAR(int heff_status);

#ifndef HEFF_PART

// (the program's stack, which heff's recursion is: a call last a jump,
// and a call of itself put in a tag a loop,
// but what is left is as deep as it goes -- `-DHEFF_MAIN_STACK=BYTES`
// for another size)
#ifndef HEFF_MAIN_STACK
#define HEFF_MAIN_STACK ((size_t)1 << 30)
#endif

#ifdef HEFF_CHECK
static const Global *heff_globals = NULL;
static int heff_nglobals = 0;

// (the program's: its definitions and the names of its tags and labels)
static void heff_check_init(void);

static void *heff_thread(void *u) {
  (void)u;
  heff_tls_enter();
  heff_watch_stack();
  heff_check_init();
  Buf out = {0};
  buf_str(&out, "{");
  int first = 1;
  for (int i = 1; i < heff_argc; i++)
    for (int j = 0; j < heff_nglobals; j++)
      if (strcmp(heff_argv[i], heff_globals[j].name) == 0) {
        if (!first) buf_str(&out, ", ");
        first = 0;
        heff_check_one(&out, &heff_globals[j]);
        break;
      }
  buf_str(&out, "}");
  fputs(out.s, stdout);
  return NULL;
}
#else
static V heff_entry(void);

// (the layout the runtime's Zig reads values by, held to the one here
// where the program is not optimised: each offset and size it says)
#ifndef __OPTIMIZE__
extern const uint16_t heff_zig_layout[7];
static void heff_layout_held(void) {
  static const uint16_t here[] = {
    sizeof(Obj), __builtin_offsetof(Obj, kind), __builtin_offsetof(Obj, tag),
    sizeof(Big), __builtin_offsetof(Big, neg), __builtin_offsetof(Big, n),
    sizeof(((Big *)0)->d[0]) };
  if (memcmp(here, heff_zig_layout, sizeof here)) {
    fprintf(stderr, "heff: the runtime's Zig lays values out otherwise than its C\n");
    abort();
  }
}
#else
static void heff_layout_held(void) {}
#endif

static void *heff_thread(void *u) {
  (void)u;
  heff_tls_enter();
  heff_layout_held();
  heff_watch_stack();
  heff_tr(heff_entry());
  if (heff_returned && heff_returned() && heff_status == 0) heff_status = 1;
  return NULL;
}
#endif

// (the program's thread: the program, then its end -- the first
// thread's to make, where nothing lent runs there)
static void *heff_program(void *u) {
  heff_thread(u);
  heff_end(heff_status, 1);
  return NULL;
}

// (the first thread's part: each job lent to it run, until the
// program's end is its own to make -- then the program's status)
static int heff_first_serve(void) {
  pthread_mutex_lock(&heff_first_mu);
  for (;;) {
    if (heff_first.ended == 1 && !heff_first.running) break;
    if (!heff_first.ended && heff_first.lent && !heff_first.running) {
      void (*run)(void *) = heff_first.run;
      void *u = heff_first.u;
      heff_first.running = 1;
      pthread_mutex_unlock(&heff_first_mu);
      run(u);
      pthread_mutex_lock(&heff_first_mu);
      heff_first.running = 0;
      heff_first.lent = 0;
      continue;
    }
    pthread_cond_wait(&heff_first_cv, &heff_first_mu);
  }
  int status = heff_first.status;
  pthread_mutex_unlock(&heff_first_mu);
  return status;
}

static void heff_first_begin(void) {
  heff_first.first = pthread_self();
  heff_first.known = 1;
}

#ifdef _WIN32
// (the program's thread on Windows: its large stack reserved, not
// committed, and its bytes in and out as they are, not as text)
static DWORD WINAPI heff_win_thread(LPVOID u) {
  heff_program(u);
  return 0;
}

int main(int argc, char **argv) {
  heff_argc = argc; heff_argv = argv;
  heff_tls_begin();
  _setmode(_fileno(stdin), _O_BINARY);
  _setmode(_fileno(stdout), _O_BINARY);
  _setmode(_fileno(stderr), _O_BINARY);
  SetConsoleOutputCP(CP_UTF8);
  heff_first_begin();
  HANDLE t = CreateThread(NULL, (SIZE_T)HEFF_MAIN_STACK, heff_win_thread, NULL, STACK_SIZE_PARAM_IS_A_RESERVATION, NULL);
  if (!t) heff_fail("cannot start");
  int status = heff_first_serve();
  if (!heff_first.waits) WaitForSingleObject(t, INFINITE);
  fflush(stdout);
  return status;
}
#else
int main(int argc, char **argv) {
  heff_argc = argc; heff_argv = argv;
  heff_tls_begin();
  pthread_attr_t attr;
  pthread_attr_init(&attr);
  pthread_attr_setstacksize(&attr, HEFF_MAIN_STACK);
#ifdef HEFF_WATCHED
  pthread_attr_setguardsize(&attr, HEFF_GUARD);
#endif
  heff_watch_faults();
  heff_first_begin();
  pthread_t t;
  if (pthread_create(&t, &attr, heff_program, NULL) != 0) heff_fail("cannot start");
  int status = heff_first_serve();
  if (!heff_first.waits) pthread_join(t, NULL);
  fflush(stdout);
  return status;
}
#endif
#endif
