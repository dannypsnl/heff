// boc's side, in JavaScript: one thread, the behaviours run in turns.
// A cown is an object of this provider's, which the program holds
// itself: what it holds, the behaviours queued at it, the first the one
// holding it, and those waiting for it to be written (`once`).  A
// behaviour is queued at each of its cowns, and is ready once it is
// first at every one.  What is to be done -- a behaviour ready to run,
// what comes after an operation of this effect's -- is a turn, put at
// the back of those waiting (`ready`), each with whose it is: a
// behaviour's, an act's, a failure's being said, or the program's.  The turns are taken in a loop (`turns`), not by calls in
// calls, so the stack does not grow with them; and what fails in a turn
// is its owner's.
//
// A behaviour runs: its condition checked of what its cowns hold, a
// tuple as they are (`MkPair`), and its body given its turn -- the
// behaviour -- from which it takes what they hold (`Taken`), and to
// which it gives what they are to hold (`Given`), written back once the
// body has come to its end, the next let through at each cown.  A body
// whose rest comes later (an operation of another effect's that answers
// later) holds its cowns until then, the others going on meanwhile.
// Its condition not holding, a behaviour lets go of its cowns and waits
// on those it reads, queued again by the first body to write one.  A
// body that fails is done with that, its cowns as they were (written
// only after the body), and why is said on the console, the program to
// end by 1 (`process.exitCode`), the others going on.
//
// The program has one pool, made by its first operation of boc's, which
// counts the behaviours queued and running.  Every `when` spawns in it.
// The program ends as JavaScript's does, once nothing is left to run or
// waited for: those still waiting on a condition are dropped with it.
//
// An act awaited is a turn of its own, owned by the act -- not by any
// behaviour -- counted its pool's until it has come to its end: the act,
// then its rest, which spawns the behaviour after it.  An act that
// waits (a sleep) holds no cown meanwhile; its rest, coming later, is
// the program's turn.  One that fails, in its own turn, is given to the
// pool's `failed`, as a body is.  Two raced are two such turns, counted
// as one: the first to come to its value is told so (`Won`), and the
// pool counts the race done once that one's rest is; the other is not
// given up -- nothing here undoes a wait -- but runs on, told it was not
// first, its rest doing nothing.
export const boc = () => {
  const unit = { $: "MkUnit", a: [] };
  const open = (s) => $tr(s((v) => v));
  const why = (e) => (e instanceof Error ? e.message : String(e));
  const isCown = (v) => v !== null && typeof v === "object" && v.$heffCown === true;
  // (the cowns `cs` is, a cown or a tuple of them, in the order of the
  // tuple)
  const leaves = (cs, out) => {
    if (isCown(cs)) { out.push(cs); return out; }
    if (cs !== null && typeof cs === "object" && cs.$ === "MkUnit") return out;
    if (cs === null || typeof cs !== "object" || cs.$ !== "MkPair")
      throw new Error("boc: a behaviour on what is not a cown, nor a tuple of them");
    leaves(cs.a[0], out);
    leaves(cs.a[1], out);
    return out;
  };
  // (where the first cown of `cowns` that is there twice is, counted
  // from 1, both times; null where none is)
  const twice = (cowns) => {
    for (let j = 1; j < cowns.length; j++)
      for (let i = 0; i < j; i++) if (cowns[i] === cowns[j]) return [i + 1, j + 1];
    return null;
  };
  const nth = (n) =>
    n + (n % 100 >= 11 && n % 100 <= 13 ? "th" : ["th", "st", "nd", "rd"][n % 10] || "th");
  // (what they hold, a tuple as they are)
  const contents = (cs) =>
    isCown(cs) ? cs.v
    : cs.$ === "MkUnit" ? cs
    : { $: "MkPair", a: [contents(cs.a[0]), contents(cs.a[1])] };
  // (whether the `i`th cown's bit is set: all of them where the bits are
  // -1)
  const bit = (bits, i) => bits < 0n || (i < 62 && ((bits >> BigInt(i)) & 1n) === 1n);
  // (`v` taken apart as the cowns are, each written back where its bit
  // says)
  const written = (cs, v, ws, at) => {
    if (isCown(cs)) { if (bit(ws, at.i++)) cs.v = v; return; }
    if (cs.$ === "MkUnit") return;
    written(cs.a[0], v.a[0], ws, at);
    written(cs.a[1], v.a[1], ws, at);
  };
  // (a queue, first in first out, taken from at its front by an index:
  // no array shifted along)
  const queue = () => ({ items: [], at: 0 });
  const push = (q, v) => { q.items.push(v); };
  const size = (q) => q.items.length - q.at;
  const front = (q) => q.items[q.at];
  const shift = (q) => {
    const v = q.items[q.at++];
    if (q.at > 1024 && q.at * 2 > q.items.length) { q.items = q.items.slice(q.at); q.at = 0; }
    return v;
  };
  const ready = queue();
  let taking = false;
  // (whose the turn taken is: a behaviour, a `failed` run, or a pool --
  // its computation's -- each with its pool and what it does with a
  // failure; null, the program's)
  let owner = null;
  const take = (t) => {
    const was = owner;
    owner = t[0];
    try { t[1](); }
    catch (e) {
      if (t[0] === null) throw e;
      t[0].fail(e);
    } finally { owner = was; }
  };
  const turns = () => {
    if (taking) return unit;
    taking = true;
    try { while (size(ready) > 0) take(shift(ready)); } finally { taking = false; }
    return unit;
  };
  // (what comes after an operation, a turn of its owner's)
  const on = (k, x) => {
    push(ready, [owner, () => k(x)]);
    return turns();
  };
  // (the program's pool, opened by its first operation of boc's: one
  // that fails said, as a failure of the program's is, and the program
  // ending by 1, the others going on)
  let program;
  const failedProgram = (w) => {
    console.error(w === "heff:abandon" ? w : "heff: " + w);
    if (typeof process !== "undefined") process.exitCode = 1;
    return (k) => k(unit);
  };
  const here = () => {
    if (owner !== null) return owner.pool;
    if (program === undefined) {
      program = { live: 0, failed: failedProgram, parked: new Set(), program: true };
      program.pool = program;
    }
    return program;
  };
  // (the behaviour queued at its cowns, counted its pool's)
  const enqueue = (b) => {
    b.pool.live++;
    b.waits = 0;
    for (const c of b.cowns) {
      push(c.queue, b);
      if (size(c.queue) > 1) b.waits++;
    }
    if (b.waits === 0) push(ready, [b, () => run(b)]);
  };
  // (done: the next let through at each of its cowns)
  const release = (b) => {
    for (const c of b.cowns) {
      shift(c.queue);
      const next = front(c.queue);
      if (next !== undefined && --next.waits === 0) push(ready, [next, () => run(next)]);
    }
  };
  // (a behaviour, its body `body` on the cowns `cs`)
  const behaviour = (pool, cs, cowns, body, cond, ws, rs) => {
    const b = {
      pool, cs, cowns, body, cond, ws, rs,
      waits: 0, taken: undefined, given: undefined, finished: false,
    };
    b.fail = (e) => {
      if (b.finished) throw e;
      failedBody(b, e);
    };
    return b;
  };
  // (its condition not holding: waiting on the cowns it reads, as one
  // of its own, to be queued again)
  const park = (b) => {
    const w = { armed: true, b: behaviour(b.pool, b.cs, b.cowns, b.body, b.cond, b.ws, b.rs) };
    b.cowns.forEach((c, i) => { if (bit(b.rs, i)) c.waiting.push(w); });
    b.pool.parked.add(w);
  };
  // (those waiting on the cowns it wrote queued again, behind it, in the
  // order they came to wait)
  const woken = (b) => {
    b.cowns.forEach((c, i) => {
      if (!bit(b.ws, i) || c.waiting.length === 0) return;
      const ws = c.waiting;
      c.waiting = [];
      for (const w of ws) {
        if (!w.armed) continue;
        w.armed = false;
        w.b.pool.parked.delete(w);
        enqueue(w.b);
      }
    });
  };
  const fewer = (pool) => {
    pool.live--;
  };
  // (a body failed: `failed why` run, a turn of its own while the
  // behaviour holds its cowns, what that fails at the pool's, the first
  // kept; then the behaviour is done)
  const failedBody = (b, e) => {
    b.finished = true;
    const pool = b.pool;
    let on = false;
    const after = () => {
      if (on) return unit;
      on = true;
      release(b);
      fewer(pool);
      return unit;
    };
    const f = {
      pool,
      fail: (e2) => {
        if (on) throw e2;
        if (pool.why === undefined) pool.why = e2;
        after();
      },
    };
    push(ready, [f, () => $tr($tr(pool.failed(why(e)))((u) => after()))]);
  };
  // (an act failed: `failed why` run, a turn of its own, counted its
  // pool's, what that fails at the pool's)
  const failedAct = (pool, e) => {
    pool.live++;
    let over = false;
    const after = () => {
      if (over) return unit;
      over = true;
      fewer(pool);
      return unit;
    };
    const f = {
      pool,
      fail: (e2) => {
        if (over) throw e2;
        if (pool.why === undefined) pool.why = e2;
        after();
      },
    };
    push(ready, [f, () => $tr($tr(pool.failed(why(e)))((u) => after()))]);
  };
  // (an act, `c`, run as a turn of its own, given its turn `tn`: `settle`
  // told whether it came to its end, or failed, once)
  const act = (pool, c, tn, settle) => {
    let over = false;
    const o = {
      pool,
      fail: (e) => {
        if (over) throw e;
        over = true;
        failedAct(pool, e);
        settle(false);
      },
    };
    push(ready, [o, () => $tr($tr(c(tn))((u) => {
      if (!over) { over = true; settle(true); }
      return unit;
    }))]);
  };
  // (the behaviour run, its turn)
  const run = (b) => {
    const v = contents(b.cs);
    if (b.cond.$ === "Just" && $tr(b.cond.a[0](v)).$ !== "True") {
      b.finished = true;
      park(b);
      release(b);
      fewer(b.pool);
      return;
    }
    b.taken = v;
    const done = (u) => {
      if (b.finished) return unit;
      if (b.given === undefined) throw new Error("boc: a body ended without a value");
      b.finished = true;
      written(b.cs, b.given, b.ws, { i: 0 });
      b.given = undefined;
      woken(b);
      release(b);
      fewer(b.pool);
      return turns();
    };
    $tr($tr(b.body(b))(done));
  };
  return (p, k) => {
    const a = p.a;
    switch (p.$) {
      case "NewCown": {
        const m = open(a[0]);
        return on(k, m.a[1]({ $heffCown: true, v: m.a[0], queue: queue(), waiting: [] }));
      }
      case "When": {
        const bh = open(a[0]);
        const pool = here();
        const cs = bh.a[0];
        const cowns = leaves(cs, []);
        const at = twice(cowns);
        // (the same cown twice: a failure, said as a body's is, the
        // behaviour never queued, the spawner going on)
        if (at) {
          failedAct(pool, new Error("boc: the same cown twice in one `with`, its "
            + nth(at[0]) + " and " + nth(at[1]) + " cowns: the behaviour not spawned"));
          return on(k, a[2]);
        }
        enqueue(behaviour(pool, cs, cowns, $carriedFn(a[1]), bh.a[1], bh.a[2], bh.a[3]));
        return on(k, a[2]);
      }
      case "Taken": {
        const tk = open(a[0]);
        const tn = tk.a[0];
        const v = tn.taken;
        if (v === undefined) throw new Error("boc: what the cowns hold taken where no body runs, or twice");
        tn.taken = undefined;
        return on(k, tk.a[1](v));
      }
      case "Given": {
        const gv = open(a[0]);
        gv.a[0].given = gv.a[1];
        return on(k, gv.a[2]);
      }
      case "Awaits": {
        const pool = here();
        pool.live++;
        act(pool, $carriedFn(a[0]), unit, (ended) => fewer(pool));
        return on(k, a[1]);
      }
      case "Races": {
        const pool = here();
        const race = { won: false, winner: null, left: 2 };
        pool.live++;
        const arm = (c) => {
          const me = {};
          act(pool, c, { race, me }, (ended) => {
            race.left--;
            if (race.winner === me || (race.left === 0 && race.winner === null)) fewer(pool);
          });
        };
        arm($carriedFn(a[0]));
        arm($carriedFn(a[1]));
        return on(k, a[2]);
      }
      case "Won": {
        const tn = a[0];
        const first = tn.race.winner === null;
        if (first) tn.race.winner = tn.me;
        return on(k, a[1]({ $: first ? "True" : "False", a: [] }));
      }
      default: throw new Error("heff: not an operation of boc: " + (p && p.$));
    }
  };
};
