#!/usr/bin/env node
// The other side of the backends' network tests, by Node.js: an HTTP
// implementation of its own to hold heff's client and server to, which
// an integration test, given no network of its own, runs as a command.
//
//   node test/peers.mjs ports N     N ports nothing listens on, a line each
//   node test/peers.mjs routes      an HTTP server of the client's tests;
//                                   says `PORT REFUSED`, ends with its input
//   node test/peers.mjs slow MS     an HTTP server answering each request
//                                   after MS; says `PORT`, and, its input
//                                   ended, `most N`: how many it had in
//                                   hand at once at most
//   node test/peers.mjs client PORT a server's client: requests by
//                                   node:http, bytes written to sockets,
//                                   curl, then /stop; says what each got,
//                                   a line of JSON, `{ what, got }`
//   node test/peers.mjs burst PORT M N
//                                   a server's clients: M one after
//                                   another, then N, their connections
//                                   opened at once, a request each, then
//                                   /stop; says how many of the N were
//                                   answered
//   node test/peers.mjs idle PORT M N
//                                   a server's clients: M one after
//                                   another, then N connections opened
//                                   one after another and held open,
//                                   silent, then a request on each, then
//                                   /stop; says how many of the N were
//                                   reset before they were made (each
//                                   tried again), and how many answered
//   node test/peers.mjs head PORT HEAD
//                                   a server's clients, its head limit
//                                   HEAD ms: one sending a head a byte
//                                   every 100 ms, never all of it; one
//                                   sending a head of 4 KiB in 40 pieces,
//                                   20 ms apart; one sending it at once;
//                                   then /stop; says what each came to
//   node test/peers.mjs boc BIN IDLE N
//                                   std.http.bocserver's server, BIN
//                                   PORT IDLE, started and driven: N
//                                   clients holding their connections
//                                   open, asked twice each; `/slow`; a
//                                   silent client; SIGTERM with a
//                                   request in flight; says what each
//                                   came to, and what the server said
//   node test/peers.mjs streams PORT
//                                   std.http.bocserver's streams and
//                                   sockets (its heartbeat 200 ms, its
//                                   ping 300 ms): streams finished and
//                                   the connection read on; events
//                                   published to two, each client gone;
//                                   a client that reads nothing; a
//                                   socket echoing, pinged, closed; then
//                                   /stop; says what each came to
//   node test/peers.mjs broadcast PORT
//                                   std.http.broadcast over the
//                                   server's streams: an event
//                                   broadcast to three, one client
//                                   gone and taken out, a burst come
//                                   in order to each, a stream
//                                   finished by the group; then /stop
import { spawn, spawnSync } from "node:child_process";
import { Agent, createServer, request } from "node:http";
import { connect } from "node:net";

const [mode, arg] = process.argv.slice(2);
const listening = (s) => new Promise((ok) => s.listen(0, "127.0.0.1", () => ok(s.address().port)));
// (`n` ports nothing listens on, as the system picked them: each held
// until all are picked, so that they are not the same)
const freePorts = async (n) => {
  const held = [];
  for (let i = 0; i < n; i++) { const s = createServer(); await listening(s); held.push(s); }
  const ports = held.map((s) => s.address().port);
  await Promise.all(held.map((s) => new Promise((ok) => s.close(ok))));
  return ports;
};
const sum = (b) => b.reduce((s, c) => s + c, 0);
// (a connection to `port` once it is made, or the error it failed by;
// one reset before it is made tried again, a little later: so macOS
// answers a connection past the listener's queue -- at most
// `kern.ipc.somaxconn` long, 128 by default -- where Linux drops it and
// the client's system tries again by itself)
const reached = (port, tries = 100) => new Promise((ok) => {
  const s = connect({ host: "127.0.0.1", port });
  const failed = (e) => {
    s.destroy();
    if (e.code === "ECONNRESET" && tries > 0) setTimeout(() => reached(port, tries - 1).then(ok), 50);
    else ok(e);
  };
  s.once("error", failed);
  s.once("connect", () => { s.off("error", failed); ok(s); });
});
// (until the input ends)
const inputEnded = () => new Promise((ok) => { process.stdin.on("data", () => {}); process.stdin.on("end", ok); process.stdin.resume(); });

if (mode === "ports") console.log((await freePorts(Number(arg))).join("\n"));

if (mode === "routes") {
  const big = Buffer.from(Array.from({ length: 1 << 18 }, (_, i) => (i * 7) % 251));
  const server = createServer((q, r) => {
    const say = (status, body, headers = {}) => { r.writeHead(status, headers); r.end(body); };
    switch (q.url) {
      case "/item": return say(200, "item 3\n".repeat(4));
      // (what it was sent, said back: its method, a header of the
      // test's, its type, how long its body, whether it waits to go on;
      // and the body)
      case "/echo": {
        const parts = [];
        q.on("data", (c) => parts.push(c));
        return q.on("end", () => {
          const body = Buffer.concat(parts);
          say(200, body, {
            "X-Method": q.method, "X-Heff": q.headers["x-heff"] ?? "none", "X-Type": q.headers["content-type"] ?? "none",
            "X-Length": String(body.length), "X-Expect": q.headers.expect ?? "none",
          });
        });
      }
      case "/nope": return say(404, "not here");
      case "/fails": return say(500, "broken");
      case "/moved": return say(302, "moving", { Location: "/item" });
      case "/loop": return say(302, "", { Location: "/loop" });
      case "/slow": return setTimeout(() => say(200, "late"), 500);
      case "/big": return say(200, big, { "Content-Length": big.length });
      case "/chunked": r.write("one,"); r.write("two,"); return r.end("three");
      case "/short": r.writeHead(200, { "Content-Length": 100 }); r.write("cut"); return setTimeout(() => r.socket.destroy(), 50);
      default: return say(500);
    }
  });
  const port = await listening(server);
  const [refused] = await freePorts(1);
  console.log(`${port} ${refused}`);
  await inputEnded();
  server.closeAllConnections();
  server.close();
}

if (mode === "slow") {
  let inHand = 0, most = 0;
  const server = createServer((q, r) => {
    const i = q.url.replace(/^\/item\//, "");
    most = Math.max(most, ++inHand);
    setTimeout(() => { inHand--; r.writeHead(200, { "Content-Type": "text/plain" }); r.end(`item ${i}\n`); }, Number(arg));
  });
  console.log(await listening(server));
  await inputEnded();
  console.log(`most ${most}`);
  server.closeAllConnections();
  server.close();
}

if (mode === "client") {
  const port = Number(arg);
  const said = (what, got) => console.log(JSON.stringify({ what, got }));
  const bytesOf = (n) => Buffer.from(Array.from({ length: 256 * n }, (_, i) => i % 256));
  const big = Buffer.concat(Array.from({ length: 4096 }, () => bytesOf(4)));
  // (bytes written to a connection, in parts -- each after a pause, or
  // after what it waits for has come -- and all that came back, until the
  // server closed it)
  const raw = (parts) => new Promise((ok) => {
    const s = connect({ host: "127.0.0.1", port });
    let got = "", next = 0;
    const timer = setTimeout(() => { s.destroy(); ok(`${got}(no end)`); }, 10000);
    const send = () => {
      if (next >= parts.length) return;
      const [after, text] = parts[next];
      if (typeof after === "number") { next++; setTimeout(() => { s.write(text); send(); }, after); }
      else if (got.includes(after)) { next++; s.write(text); send(); }
    };
    s.setEncoding("latin1");
    s.on("connect", send);
    s.on("data", (d) => { got += d; send(); });
    s.on("error", (e) => { got += `(${e.code})`; });
    s.on("close", () => { clearTimeout(timer); ok(got); });
  });
  // (the server up: connected to, the connection closed at once)
  const up = async () => {
    for (let i = 0; i < 600; i++) {
      if (await new Promise((ok) => {
        const s = connect({ host: "127.0.0.1", port });
        s.on("connect", () => { s.destroy(); ok(true); });
        s.on("error", () => ok(false));
      })) return true;
      await new Promise((ok) => setTimeout(ok, 50));
    }
    return false;
  };
  if (!(await up())) { said("up", "not listening"); process.exit(0); }
  const agent = new Agent({ keepAlive: true, maxSockets: 1 });
  // (a request by node:http, on the connection kept, or `via` another)
  const ask = (method, path, body, headers = {}, via = agent) => new Promise((ok) => {
    const q = request({ host: "127.0.0.1", port, method, path, agent: via, headers }, (r) => {
      const parts = [];
      r.on("data", (c) => parts.push(c));
      r.on("end", () => ok({ status: r.statusCode, headers: r.headers, body: Buffer.concat(parts), reused: q.reusedSocket }));
    });
    q.on("error", (e) => ok({ status: e.code, headers: {}, body: Buffer.alloc(0), reused: false }));
    q.end(body);
  });
  const posted = Buffer.from(Array.from({ length: 300000 }, (_, i) => (i * 13) % 256));
  let r = await ask("GET", "/hello");
  said("get", `${r.status} ${r.headers["content-length"]} ${r.body} ${r.reused}`);
  r = await ask("POST", "/echo", posted, { "X-Heff": "node" });
  said("post", `${r.status} ${r.headers["x-method"]} ${r.headers["x-version"]} ${r.headers["x-peer"]} ${r.headers["x-heff"]} ${r.body.equals(posted)} ${r.reused}`);
  r = await ask("HEAD", "/hello");
  said("head", `${r.status} ${r.headers["content-length"]} ${r.body.length} ${r.reused}`);
  r = await ask("GET", "/nope");
  said("404", `${r.status} ${r.body} ${r.reused}`);
  r = await ask("GET", "/big");
  said("big", `${r.status} ${r.body.equals(big)} ${r.reused}`);
  // (the connection kept, closed: the server, one connection at a time,
  // goes on to the next)
  agent.destroy();
  for (const [what, parts] of [
    ["one after another, in one write",
      [[0, "GET /hello HTTP/1.1\r\nHost: x\r\n\r\nGET /hello HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n"]]],
    ["a head in parts", [[0, "GET /hel"], [50, "lo HTTP/1.1\r\nHost: x\r\nConnection: close\r"], [50, "\n\r\n"]]],
    ["HTTP/1.0", [[0, "GET /hello HTTP/1.0\r\n\r\n"]]],
    ["HTTP/1.0, kept alive", [[0, "GET /hello HTTP/1.0\r\nConnection: keep-alive\r\n\r\nGET /hello HTTP/1.0\r\n\r\n"]]],
    ["Expect: 100-continue",
      [[0, "POST /echo HTTP/1.1\r\nContent-Length: 5\r\nExpect: 100-continue\r\nConnection: close\r\n\r\n"], ["100 Continue\r\n\r\n", "hello"]]],
    ["a chunked body", [[0, "POST /echo HTTP/1.1\r\nTransfer-Encoding: chunked\r\nConnection: close\r\n\r\n3\r\nabc\r\n0\r\n\r\n"]]],
    // (a body in chunks sent a piece at a time, a piece ending within a
    // chunk's size, its data, its end; an extension, a trailer; and a
    // request after it, in its last piece)
    ["a chunked body in pieces",
      [[0, "POST /echo HTTP/1.1\r\nTransfer-Encoding: chunked\r\nExpect: 100-continue\r\n\r\n"], ["100 Continue\r\n\r\n", "5\r\nhel"],
        [50, "lo\r\n7;ext=1\r\n, worl"], [50, "d\r\n0\r\nX-Trailer: t\r"],
        [50, "\n\r\nGET /hello HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n"]]],
    ["chunks and a length", [[0, "POST /echo HTTP/1.1\r\nTransfer-Encoding: chunked\r\nContent-Length: 3\r\n\r\n3\r\nabc\r\n0\r\n\r\n"]]],
    ["a body in gzip", [[0, "POST /echo HTTP/1.1\r\nTransfer-Encoding: gzip\r\nContent-Length: 3\r\n\r\nabc"]]],
    // (refused, the client sending on after the response: drained, not
    // reset, so that it reads the response)
    ["a body too long, sent on",
      [[0, "POST /echo HTTP/1.1\r\nContent-Length: 100000000\r\n\r\n" + "x".repeat(32768)], ["Content Too Large\n", "y".repeat(524288)]]],
    ["a chunk too long, sent on",
      [[0, "POST /echo HTTP/1.1\r\nTransfer-Encoding: chunked\r\n\r\n4000001\r\n" + "x".repeat(32768)], ["Content Too Large\n", "y".repeat(524288)]]],
    ["no request", [[0, "NONSENSE\r\n\r\n"]]],
    // (replies of std.http.server's other than whole: streamed in
    // chunks, the connection kept after them; streamed to HTTP/1.0, its
    // end the connection's; a head alone; events; and the connection
    // taken over, what was sent with the request given to it)
    ["streamed, then another",
      [[0, "GET /stream HTTP/1.1\r\nHost: x\r\n\r\nGET /hello HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n"]]],
    ["streamed, HTTP/1.0", [[0, "GET /stream HTTP/1.0\r\n\r\n"]]],
    ["streamed, HEAD", [[0, "HEAD /stream HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n"]]],
    ["events", [[0, "GET /events HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n"]]],
    ["taken over",
      [[0, "GET /upgrade HTTP/1.1\r\nHost: x\r\nConnection: Upgrade\r\nUpgrade: echo\r\n\r\nearly"], ["rest: early\n", "late"]]],
  ]) said(what, await raw(parts));
  // (a WebSocket's frame, as a client sends it: masked, unless `mask`
  // is false, by a key of its own)
  const frame = (op, payload, { fin = true, mask = true } = {}) => {
    const p = Buffer.from(payload), key = Buffer.from([0x37, 0xfa, 0x21, 0x3d]);
    const head = p.length < 126 ? Buffer.from([(fin ? 128 : 0) | op, (mask ? 128 : 0) | p.length])
      : Buffer.from([(fin ? 128 : 0) | op, (mask ? 128 : 0) | 126, p.length >> 8, p.length & 255]);
    return Buffer.concat([head, mask ? key : Buffer.alloc(0), mask ? Buffer.from(p.map((c, i) => c ^ key[i % 4])) : p]);
  };
  const closeOf = (code, why = "") => Buffer.concat([Buffer.from([code >> 8, code & 255]), Buffer.from(why)]);
  const upgrade = (target = "/ws", more = "") => Buffer.from(`GET ${target} HTTP/1.1\r\nHost: x\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n`
    + `Sec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\nSec-WebSocket-Version: 13\r\n${more}\r\n`);
  // (what a server's WebSocket sent back: its head, then each frame, a
  // text's as it is, a close's code and why, any other's in hex)
  const frames = (got) => {
    const h = got.indexOf("\r\n\r\n");
    if (!got.startsWith("HTTP/1.1 101 ") || h < 0) return got;
    let b = Buffer.from(got.slice(h + 4), "latin1");
    const out = [];
    while (b.length >= 2) {
      const op = b[0] & 15, masked = b[1] & 128 ? "masked " : "";
      let n = b[1] & 127, at = 2;
      if (n === 126) { n = b.readUInt16BE(2); at = 4; } else if (n === 127) { n = Number(b.readBigUInt64BE(2)); at = 10; }
      if (b.length < at + n) break;
      const p = b.subarray(at, at + n), fin = b[0] & 128 ? "" : " (not the last)";
      const name = { 0: "continuation", 1: "text", 2: "binary", 8: "close", 9: "ping", 10: "pong" }[op] ?? `opcode ${op}`;
      out.push(`${masked}${name}${fin}` + (op === 1 ? ` ${p}` : op === 8 && p.length >= 2 ? ` ${p.readUInt16BE(0)}${p.length > 2 ? ` ${p.subarray(2)}` : ""}` : p.length ? ` ${p.toString("hex")}` : ""));
      b = b.subarray(at + n);
    }
    if (b.length) out.push(`${b.toString("latin1")}`);
    return `${got.slice(0, h + 4)}${out.join(", ")}`;
  };
  // (a WebSocket's, each frame of the client's masked but one: messages
  // echoed, the first sent with the handshake; a ping answered; a message
  // in pieces, a ping between them; a close the server sends; a frame not
  // masked; a handshake refused)
  for (const [what, parts] of [
    ["websocket, echoed",
      [[0, Buffer.concat([upgrade(), frame(1, "hello")])], [50, frame(2, [1, 2, 3])], [50, frame(8, closeOf(1000, "done"))]]],
    ["websocket, a ping", [[0, upgrade()], [50, frame(9, "hi")], [50, frame(8, closeOf(1001))]]],
    ["websocket, in pieces",
      [[0, Buffer.concat([upgrade(), frame(1, "Hel", { fin: false }), frame(9, "?")])], [50, frame(0, "l", { fin: false })], [50, frame(0, "o")],
        [50, frame(8, "")]]],
    ["websocket, closed by the server",
      [[0, Buffer.concat([upgrade(), frame(1, "bye")])], ["\x88\x05\x03\xe8bye", frame(8, closeOf(1000))]]],
    ["websocket, a frame not masked", [[0, Buffer.concat([upgrade(), frame(1, "hello", { mask: false })])]]],
    ["websocket, refused", [[0, Buffer.from("GET /ws HTTP/1.1\r\nHost: x\r\nUpgrade: websocket\r\nConnection: Upgrade, close\r\nSec-WebSocket-Version: 13\r\n\r\n")]]],
  ]) said(what, frames(await raw(parts)));
  // (a stream whose client goes after its first piece: the server, its
  // writes failing, goes on to the next connection)
  said("a stream, its client gone", await new Promise((ok) => {
    const s = connect({ host: "127.0.0.1", port });
    const timer = setTimeout(() => { s.destroy(); ok("(no piece)"); }, 10000);
    s.setEncoding("latin1");
    s.on("connect", () => s.write("GET /forever HTTP/1.1\r\nHost: x\r\n\r\n"));
    s.once("data", (d) => { clearTimeout(timer); s.destroy(); ok(d.split("\r\n")[0]); });
    s.on("error", (e) => { clearTimeout(timer); ok(`(${e.code})`); });
  }));
  if (spawnSync("curl", ["--version"]).status === 0) {
    const at = `http://127.0.0.1:${port}`;
    const c = spawnSync("curl", ["-sS", "--http1.1", "-o", "/dev/null", "-o", "/dev/null", "-w", "%{http_code} %{num_connects} %{size_download}\n",
      `${at}/hello`, `${at}/big`], { encoding: "utf8", timeout: 30000 });
    said("curl, two requests on one connection", `${c.stdout}${c.stderr}`);
  }
  const stop = await ask("GET", "/stop", undefined, {}, false);
  said("stop", `${stop.status} ${stop.body}`);
}

if (mode === "burst") {
  const port = Number(arg), before = Number(process.argv[4]), n = Number(process.argv[5]);
  // (a request on a connection of its own, closed after: what came back,
  // or the error)
  const got = async (target) => {
    const s = await reached(port);
    if (s instanceof Error) return `(${s.code})`;
    return new Promise((ok) => {
      let back = "";
      const timer = setTimeout(() => { s.destroy(); ok(`${back}(no end)`); }, 20000);
      s.setEncoding("latin1");
      s.on("data", (d) => { back += d; });
      s.on("error", (e) => { back += `(${e.code})`; });
      s.on("close", () => { clearTimeout(timer); ok(back); });
      s.write(`GET ${target} HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n`);
    });
  };
  // (the server up: a connection made, closed at once)
  for (let i = 0; i < 600 && !(await new Promise((ok) => {
    const s = connect({ host: "127.0.0.1", port });
    s.on("connect", () => { s.destroy(); ok(true); });
    s.on("error", () => ok(false));
  })); i++) await new Promise((ok) => setTimeout(ok, 50));
  for (let i = 0; i < before; i++) await got(`/before/${i}`);
  const all = await Promise.all(Array.from({ length: n }, (_, i) => got(`/${i}`)));
  const answered = all.filter((b, i) => b.startsWith("HTTP/1.1 200 ") && b.endsWith(`\r\n\r\n/${i}`)).length;
  console.log(`answered ${answered} of ${n}`);
  await got("/stop");
}

if (mode === "idle") {
  const port = Number(arg), before = Number(process.argv[4]), n = Number(process.argv[5]);
  // (a request on the connection, closed after: what came back)
  const asked = (s, target) => new Promise((ok) => {
    let back = "";
    const timer = setTimeout(() => { s.destroy(); ok(`${back}(no end)`); }, 20000);
    s.setEncoding("latin1");
    s.on("data", (d) => { back += d; });
    s.on("error", (e) => { back += `(${e.code})`; });
    s.on("close", () => { clearTimeout(timer); ok(back); });
    s.write(`GET ${target} HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n`);
  });
  const got = async (target) => {
    const s = await reached(port);
    return s instanceof Error ? `(${s.code})` : asked(s, target);
  };
  for (let i = 0; i < 600 && !(await new Promise((ok) => {
    const s = connect({ host: "127.0.0.1", port });
    s.on("connect", () => { s.destroy(); ok(true); });
    s.on("error", () => ok(false));
  })); i++) await new Promise((ok) => setTimeout(ok, 50));
  for (let i = 0; i < before; i++) await got(`/before/${i}`);
  // (each made before the next is begun: a reset counted, and tried
  // again, as `reached` does)
  let resets = 0;
  const made = (tries = 100) => new Promise((ok) => {
    const s = connect({ host: "127.0.0.1", port });
    const failed = (e) => {
      s.destroy();
      if (e.code === "ECONNRESET" && tries > 0) { resets++; setTimeout(() => made(tries - 1).then(ok), 50); }
      else ok(e);
    };
    s.once("error", failed);
    s.once("connect", () => { s.off("error", failed); ok(s); });
  });
  const held = [];
  for (let i = 0; i < n; i++) held.push(await made());
  await new Promise((ok) => setTimeout(ok, 100));
  const all = await Promise.all(held.map((s, i) => s instanceof Error ? `(${s.code})` : asked(s, `/${i}`)));
  const answered = all.filter((b, i) => b.startsWith("HTTP/1.1 200 ") && b.endsWith(`\r\n\r\n/${i}`)).length;
  console.log(`reset before they were made: ${resets} of ${n}`);
  console.log(`answered ${answered} of ${n}`);
  await got("/stop");
}

if (mode === "head") {
  const port = Number(arg), head = Number(process.argv[4]);
  const wait = (ms) => new Promise((ok) => setTimeout(ok, ms));
  // (the server up: a connection made, closed at once)
  for (let i = 0; i < 600 && !(await new Promise((ok) => {
    const s = connect({ host: "127.0.0.1", port });
    s.on("connect", () => { s.destroy(); ok(true); });
    s.on("error", () => ok(false));
  })); i++) await wait(50);
  // (a connection: `pieces` written `gap` ms apart, then what came back
  // once the server closed it, or `(open)` after 10 s; and how long that
  // took from the first write)
  const sent = async (pieces, gap) => {
    const s = await reached(port);
    if (s instanceof Error) return { back: `(${s.code})`, ms: 0 };
    s.setNoDelay(true);
    s.setEncoding("latin1");
    let back = "", closed = false;
    const t0 = Date.now();
    const ended = new Promise((ok) => s.on("close", () => { closed = true; ok(); }));
    s.on("data", (d) => { back += d; });
    s.on("error", () => {});
    (async () => {
      for (const p of pieces) {
        if (closed) return;
        s.write(p);
        await wait(gap);
      }
    })();
    await Promise.race([ended, wait(10000)]);
    if (!closed) { s.destroy(); back += "(open)"; }
    return { back, ms: Date.now() - t0 };
  };
  // (a head never ended: its first line, then a byte a write, 300 of
  // them, each write sooner than any idle limit would close it)
  const trickle = await sent(["GET /trickle HTTP/1.1\r\n", ..."X".repeat(300)], 100);
  console.log(`a head sent a byte at a time: ${trickle.back === "" && trickle.ms >= head - 50 && trickle.ms < head + 1500 ? "closed in time, unanswered" : `${JSON.stringify(trickle.back)} in ${trickle.ms} ms`}`);
  // (a head of 4 KiB, its last bytes, the blank line's, apart)
  const whole = `GET /pieces HTTP/1.1\r\nHost: x\r\nX-Pad: ${"p".repeat(4000)}\r\nConnection: close\r\n\r\n`;
  const size = Math.ceil((whole.length - 3) / 37);
  const pieces = Array.from({ length: 37 }, (_, i) => whole.slice(i * size, Math.min((i + 1) * size, whole.length - 3)));
  const inPieces = await sent([...pieces, "\n", "\r", "\n"], 20);
  console.log(`a head sent in 40 pieces: ${inPieces.back.startsWith("HTTP/1.1 200 ") && inPieces.back.endsWith("\r\n\r\n/pieces") ? "answered" : JSON.stringify(inPieces.back.slice(0, 60))}`);
  const atOnce = await sent(["GET /at-once HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n"], 0);
  console.log(`a head sent at once: ${atOnce.back.startsWith("HTTP/1.1 200 ") && atOnce.back.endsWith("\r\n\r\n/at-once") ? "answered" : JSON.stringify(atOnce.back.slice(0, 60))}`);
  await sent(["GET /stop HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n"], 0);
}

if (mode === "boc") {
  const bin = arg, idle = Number(process.argv[4]), n = Number(process.argv[5]);
  const [port] = await freePorts(1);
  const server = spawn(bin, [String(port), String(idle)], { stdio: ["ignore", "pipe", "pipe"] });
  let said = "", saidErr = "";
  server.stdout.setEncoding("utf8").on("data", (d) => { said += d; });
  server.stderr.setEncoding("utf8").on("data", (d) => { saidErr += d; });
  const exited = new Promise((ok) => server.on("exit", (code, signal) => ok({ code, signal })));
  // (a connection kept: `ask(target)`, one request on it, its response's
  // body once it is all come, or null where the connection ended first;
  // `ended`, once the other side closed it)
  const opened = async () => {
    const s = await reached(port);
    if (s instanceof Error) return null;
    s.setEncoding("latin1");
    let buf = "", waiting = null, closed = false;
    const ended = new Promise((done) => s.on("close", () => { closed = true; if (waiting) { waiting(null); waiting = null; } done(); }));
    const take = () => {
      if (!waiting) return;
      const h = buf.indexOf("\r\n\r\n");
      if (h < 0) return;
      const m = /content-length: *(\d+)/i.exec(buf.slice(0, h));
      const len = m ? Number(m[1]) : 0;
      if (buf.length < h + 4 + len) return;
      const body = buf.slice(h + 4, h + 4 + len);
      buf = buf.slice(h + 4 + len);
      const w = waiting; waiting = null; w(body);
    };
    s.on("data", (d) => { buf += d; take(); });
    s.on("error", () => {});
    const ask = (target) => new Promise((back) => {
      if (closed) return back(null);
      waiting = back;
      s.write(`GET ${target} HTTP/1.1\r\nHost: x\r\n\r\n`);
      take();
    });
    return { ask, ended, end: () => s.end(), s };
  };
  let up = null;
  for (let i = 0; i < 600 && !up; i++) {
    up = await opened();
    if (!up) await new Promise((ok) => setTimeout(ok, 50));
  }
  if (!up) { console.log("no server"); server.kill("SIGKILL"); process.exit(0); }
  up.end();
  await up.ended;
  // (N connections at once, a request each, answered while all are held
  // open; then a second request each, on the same connection)
  const cs = await Promise.all(Array.from({ length: n }, () => opened()));
  const first = await Promise.all(cs.map((c, i) => (c ? c.ask(`/a/${i}`) : null)));
  console.log(`first requests answered, every connection held open: ${first.filter((b, i) => b === `/a/${i}`).length} of ${n}`);
  const second = await Promise.all(cs.map((c, i) => (c ? c.ask(`/b/${i}`) : null)));
  console.log(`second requests answered, on the same connections: ${second.filter((b, i) => b === `/b/${i}`).length} of ${n}`);
  await Promise.all(cs.map((c) => { if (c) { c.end(); return c.ended; } }));
  // (a handler that awaits a sleep of its own)
  const slow = await opened();
  const t0 = Date.now();
  const sb = await slow.ask("/slow");
  const ms = Date.now() - t0;
  console.log(`slow, its handler awaiting a sleep: ${sb === "slow" && ms >= 280 && ms < 2000 ? "answered, in time" : `${sb} in ${ms} ms`}`);
  // (a handler that throws: its connection closed at once, unanswered,
  // and the next client answered)
  const thrower = await opened();
  const t2 = Date.now();
  const tb = await thrower.ask("/throw");
  const thrownMs = Date.now() - t2;
  const next = await opened();
  const nb = next ? await next.ask("/after") : null;
  if (next) { next.end(); await next.ended; }
  console.log(`a handler that throws: ${tb === null && thrownMs < idle ? "closed at once, unanswered" : `${tb} in ${thrownMs} ms`}; the next: ${nb === "/after" ? "answered" : nb}`);
  // (a client that sends nothing: closed by the server in `idle`)
  const silent = await opened();
  const t1 = Date.now();
  await silent.ended;
  const idled = Date.now() - t1;
  console.log(`a silent client: ${idled >= idle - 50 && idled < idle + 1500 ? "closed in time" : `closed in ${idled} ms`}`);
  // (SIGTERM with a request in flight, and a connection kept open idle:
  // the request answered, the idle one closed, the server ended)
  const kept = await opened();
  await kept.ask("/kept");
  const flight = await opened();
  const answer = flight.ask("/slow");
  await new Promise((ok) => setTimeout(ok, 100));
  server.kill("SIGTERM");
  const fb = await answer;
  console.log(`SIGTERM, a request in flight: ${fb === "slow" ? "answered" : fb}`);
  const keptClosed = await Promise.race([kept.ended.then(() => true), new Promise((ok) => setTimeout(() => ok(false), 3000))]);
  console.log(`a connection kept open, idle: ${keptClosed ? "closed by the stop" : "still open"}`);
  const end = await Promise.race([exited, new Promise((ok) => setTimeout(() => ok(null), 5000))]);
  if (!end) server.kill("SIGKILL");
  console.log(`the server: ${end ? `ended, status ${end.code}` : "still running"}`);
  await exited;
  process.stdout.write(said.split("\n").filter((l) => l).map((l) => `the server said: ${l}\n`).join(""));
  if (saidErr) process.stdout.write(`the server's errors: ${saidErr}`);
}

if (mode === "streams") {
  const port = Number(arg);
  const wait = (ms) => new Promise((ok) => setTimeout(ok, ms));
  const said = (what, got) => console.log(`${what}: ${got}`);
  for (let i = 0; i < 600 && !(await new Promise((ok) => {
    const s = connect({ host: "127.0.0.1", port });
    s.on("connect", () => { s.destroy(); ok(true); });
    s.on("error", () => ok(false));
  })); i++) await wait(50);
  // (a connection: what came back so far, `until` what is waited for
  // has come -- or 5 s passed -- and `ended` once it is closed)
  const opened = async () => {
    const s = await reached(port);
    s.setNoDelay(true);
    let got = Buffer.alloc(0), closed = false;
    const ended = new Promise((ok) => s.on("close", () => { closed = true; ok(); }));
    s.on("data", (d) => { got = Buffer.concat([got, d]); });
    s.on("error", () => {});
    const until = async (p, ms = 5000) => {
      for (let t = 0; t < ms && !p(got) && !closed; t += 10) await wait(10);
      return p(got);
    };
    const text = () => got.toString("latin1");
    return { s, until, text, bytes: () => got, ended, isClosed: () => closed, end: () => s.end() };
  };
  // (a whole response's body, on a connection of its own)
  const asked = async (method, target, body = "") => {
    const c = await opened();
    c.s.write(`${method} ${target} HTTP/1.1\r\nHost: x\r\nContent-Length: ${body.length}\r\nConnection: close\r\n\r\n${body}`);
    await Promise.race([c.ended, wait(5000)]);
    const t = c.text();
    return t.slice(t.indexOf("\r\n\r\n") + 4);
  };
  const ended = async (c, ms) => (await Promise.race([c.ended.then(() => true), wait(ms).then(() => false)]));
  const goneCount = (log, what) => log.split(",").filter((l) => l === `gone ${what}`).length;

  // (a stream, finished, then another request on the connection: one
  // after the other, and both in one write)
  {
    const c = await opened();
    c.s.write("GET /stream HTTP/1.1\r\nHost: x\r\n\r\n");
    await c.until((b) => b.toString("latin1").endsWith("0\r\n\r\n"));
    c.s.write("GET /hello HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n");
    await Promise.race([c.ended, wait(5000)]);
    said("a stream, then another request", JSON.stringify(c.text()));
  }
  {
    const c = await opened();
    c.s.write("GET /stream HTTP/1.1\r\nHost: x\r\n\r\nGET /hello HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n");
    await Promise.race([c.ended, wait(5000)]);
    said("a stream and another request, in one write", JSON.stringify(c.text().replace(/\r\n\r\n4\r\none[^]*0\r\n\r\n/, "\r\n\r\n(the stream)")));
  }
  {
    const c = await opened();
    c.s.write("GET /stream HTTP/1.0\r\n\r\n");
    await Promise.race([c.ended, wait(5000)]);
    said("a stream, HTTP/1.0", JSON.stringify(c.text()));
    const h = await opened();
    h.s.write("HEAD /stream HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n");
    await Promise.race([h.ended, wait(5000)]);
    said("a stream, HEAD", JSON.stringify(h.text()));
  }
  // (two streams of events, each sent what is published; one closed by
  // its client, gone once; the other sent heartbeats while nothing is
  // published)
  {
    const a = await opened(), b = await opened();
    for (const c of [a, b]) c.s.write("GET /events HTTP/1.1\r\nHost: x\r\n\r\n");
    await a.until((g) => g.includes("\r\n\r\n"));
    await b.until((g) => g.includes("\r\n\r\n"));
    await wait(50);
    const sent = await asked("POST", "/publish", "hello");
    const both = await Promise.all([a, b].map((c) => c.until((g) => g.includes("data: hello\n\n"))));
    said("published to two streams", `${sent}, received: ${both.join(" ")}`);
    a.s.destroy();
    await wait(300);
    const afterOne = await asked("POST", "/publish", "again");
    await asked("POST", "/publish", "and again");
    await wait(300);
    said("one stream's client gone", `${afterOne}, gone called ${goneCount(await asked("GET", "/log"), "events")} time(s)`);
    const beats = (t) => t.split("2\r\n:\n\r\n").length - 1 + t.split(": \n\n").length - 1;
    const before = beats(b.text());
    await wait(700);
    said("the other, nothing published for 700 ms", beats(b.text()) - before >= 2 ? "heartbeats sent" : `${beats(b.text()) - before} heartbeats`);
    b.s.destroy();
    await wait(300);
    said("both gone", `gone called ${goneCount(await asked("GET", "/log"), "events")} time(s)`);
  }
  // (a stream whose client reads nothing: closed once more than the
  // most is waiting to be written, its `gone` called)
  {
    const c = await opened();
    c.s.write("GET /flood HTTP/1.1\r\nHost: x\r\n\r\n");
    await c.until((g) => g.includes("\r\n\r\n"));
    c.s.pause();
    let pumps = 0, last = "";
    for (; pumps < 2000; pumps++) {
      last = await asked("GET", "/pump");
      if (last === "pumped 0") break;
    }
    c.s.resume();
    const closed = await ended(c, 5000);
    said("a client that reads nothing", `${last === "pumped 0" ? "dropped from the hub" : last}, ${closed ? "closed" : "still open"}, gone called ${goneCount(await asked("GET", "/log"), "flood")} time(s)`);
  }
  // (WebSocket: the handshake, a message echoed, a ping answered, a
  // close answered and the connection closed; a ping sent by the server
  // to a silent client, which is closed when it does not answer)
  const masked = (op, payload) => {
    const p = Buffer.from(payload), m = Buffer.from([1, 2, 3, 4]);
    return Buffer.concat([Buffer.from([0x80 | op, 0x80 | p.length]), m, Buffer.from(p.map((x, i) => x ^ m[i % 4]))]);
  };
  const frames = (b) => {
    const out = [];
    for (let i = 0; i + 2 <= b.length;) {
      const n = b[i + 1] & 127;
      if (i + 2 + n > b.length) break;
      const op = b[i] & 15, p = b.slice(i + 2, i + 2 + n);
      out.push(op === 8 && n >= 2 ? `close ${p.readUInt16BE(0)} ${p.slice(2).toString("latin1")}` : `${op}:${p.toString("latin1")}`);
      i += 2 + n;
    }
    return out;
  };
  const upgrade = "GET /ws HTTP/1.1\r\nHost: x\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\nSec-WebSocket-Version: 13\r\n\r\n";
  const afterHead = (c) => { const g = c.bytes(); const i = g.indexOf("\r\n\r\n"); return i < 0 ? Buffer.alloc(0) : g.slice(i + 4); };
  {
    const c = await opened();
    c.s.write(upgrade);
    await c.until((g) => g.includes("\r\n\r\n"));
    const head = c.text().split("\r\n")[0];
    const accept = /Sec-WebSocket-Accept: (\S+)/.exec(c.text());
    c.s.write(masked(1, "hello"));
    await c.until(() => frames(afterHead(c)).length >= 1);
    c.s.write(masked(9, "p"));
    await c.until(() => frames(afterHead(c)).length >= 2);
    c.s.write(masked(8, Buffer.from([3, 232])));
    const closed = await ended(c, 5000);
    said("a socket", `${head}, ${accept ? accept[1] : "no accept"}; ${JSON.stringify(frames(afterHead(c)))}; ${closed ? "closed" : "still open"}`);
  }
  {
    const c = await opened();
    c.s.write(Buffer.concat([Buffer.from(upgrade), masked(1, "early")]));
    await c.until(() => frames(afterHead(c)).length >= 1);
    const t0 = Date.now();
    await c.until(() => frames(afterHead(c)).length >= 2, 3000);
    const pinged = Date.now() - t0;
    const closed = await ended(c, 3000);
    const ms = Date.now() - t0;
    said("a silent socket", `${JSON.stringify(frames(afterHead(c)))}, pinged in time: ${pinged >= 200 && pinged < 1500}, closed unanswered: ${closed && ms >= 400 && ms < 2500}`);
  }
  {
    const c = await opened();
    c.s.write(upgrade.replace("Sec-WebSocket-Version: 13", "Sec-WebSocket-Version: 8") .replace("\r\n\r\n", "\r\nConnection: close\r\n\r\n"));
    await Promise.race([c.ended, wait(5000)]);
    said("a handshake refused", c.text().split("\r\n")[0]);
  }
  {
    const c = await opened();
    c.s.write(Buffer.concat([Buffer.from(upgrade), Buffer.from([0x81, 0x02, 0x68, 0x69])]));
    const closed = await ended(c, 5000);
    said("a frame not masked", `${JSON.stringify(frames(afterHead(c)))}, ${closed ? "closed" : "still open"}`);
  }
  // (a body in chunks sent a piece at a time, after `100 Continue`, a
  // piece ending within a chunk's size, its data, its end; an extension,
  // a trailer; and a request after it, in its last piece.  Then chunks
  // beside a length, refused)
  {
    const c = await opened();
    c.s.write("POST /echo HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\nExpect: 100-continue\r\n\r\n");
    await c.until((g) => g.toString("latin1").includes("100 Continue\r\n\r\n"));
    for (const p of ["5\r\nhel", "lo\r\n7;ext=1\r\n, worl", "d\r\n0\r\nX-Trailer: t\r", "\n\r\nGET /hello HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n"]) {
      c.s.write(p);
      await wait(50);
    }
    await Promise.race([c.ended, wait(5000)]);
    said("a chunked body in pieces", JSON.stringify(c.text()));
    const l = await opened();
    l.s.write("POST /echo HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\nContent-Length: 3\r\n\r\n3\r\nabc\r\n0\r\n\r\n");
    await Promise.race([l.ended, wait(5000)]);
    said("chunks and a length", l.text().split("\r\n")[0]);
  }
  await wait(200);
  said("gone, sockets", `${goneCount(await asked("GET", "/log"), "socket")} time(s)`);
  // (the server stopped, a stream and a socket open: the stream ended,
  // the socket closed, 1001)
  const ev = await opened(), ws = await opened();
  ev.s.write("GET /events HTTP/1.1\r\nHost: x\r\n\r\n");
  ws.s.write(upgrade);
  await ev.until((g) => g.includes("\r\n\r\n"));
  await ws.until((g) => g.includes("\r\n\r\n"));
  await asked("GET", "/stop");
  const evClosed = await ended(ev, 5000), wsClosed = await ended(ws, 5000);
  said("stopped, a stream open", `${ev.text().endsWith("0\r\n\r\n") ? "its last chunk" : JSON.stringify(ev.text())}, ${evClosed ? "closed" : "still open"}`);
  said("stopped, a socket open", `${JSON.stringify(frames(afterHead(ws)).filter((f) => f.startsWith("close")))}, ${wsClosed ? "closed" : "still open"}`);
}

if (mode === "broadcast") {
  const port = Number(arg);
  const wait = (ms) => new Promise((ok) => setTimeout(ok, ms));
  const said = (what, got) => console.log(`${what}: ${got}`);
  for (let i = 0; i < 600 && !(await new Promise((ok) => {
    const s = connect({ host: "127.0.0.1", port });
    s.on("connect", () => { s.destroy(); ok(true); });
    s.on("error", () => ok(false));
  })); i++) await wait(50);
  const opened = async () => {
    const s = await reached(port);
    s.setNoDelay(true);
    let got = Buffer.alloc(0), closed = false;
    const ended = new Promise((ok) => s.on("close", () => { closed = true; ok(); }));
    s.on("data", (d) => { got = Buffer.concat([got, d]); });
    s.on("error", () => {});
    const until = async (p, ms = 5000) => {
      for (let t = 0; t < ms && !p(got.toString("latin1")) && !closed; t += 10) await wait(10);
      return p(got.toString("latin1"));
    };
    return { s, until, text: () => got.toString("latin1"), ended };
  };
  const asked = async (target, body = "") => {
    const c = await opened();
    c.s.write(`POST ${target} HTTP/1.1\r\nHost: x\r\nContent-Length: ${body.length}\r\nConnection: close\r\n\r\n${body}`);
    await Promise.race([c.ended, wait(5000)]);
    const t = c.text();
    return t.slice(t.indexOf("\r\n\r\n") + 4);
  };
  // (the data of each event a stream was sent, its chunks undone)
  const data = (t) => [...t.matchAll(/data: ([^\n]*)\n\n/g)].map((m) => m[1]);
  const streams = [];
  for (let i = 0; i < 3; i++) {
    const c = await opened();
    c.s.write("GET /events HTTP/1.1\r\nHost: x\r\n\r\n");
    await c.until((g) => g.includes("\r\n\r\n"));
    streams.push(c);
  }
  await wait(100);
  const sent = await asked("/publish", "hello");
  const got = await Promise.all(streams.map((c) => c.until((g) => data(g).includes("hello"))));
  said("broadcast to three", `${sent}, received: ${got.join(" ")}`);
  const [gone, ...kept] = streams;
  gone.s.destroy();
  await wait(300);
  said("one client gone", `in the group ${await asked("/size")}`);
  const again = await asked("/publish", "again");
  const both = await Promise.all(kept.map((c) => c.until((g) => data(g).includes("again"))));
  said("broadcast to the others", `${again}, received: ${both.join(" ")}`);
  await asked("/burst?200");
  const want = Array.from({ length: 200 }, (_, i) => String(i + 1)).join(",");
  const inOrder = await Promise.all(kept.map(async (c) => {
    await c.until((g) => data(g).includes("200"));
    return data(c.text()).filter((d) => /^\d+$/.test(d)).join(",") === want;
  }));
  said("a burst of 200, in order", inOrder.join(" "));
  const last = await opened();
  last.s.write("GET /last HTTP/1.1\r\nHost: x\r\n\r\n");
  const finished = await last.until((g) => g.endsWith("0\r\n\r\n"));
  said("a stream finished by the group", `${JSON.stringify(data(last.text()))}, finished: ${finished}, in the group ${await asked("/size")}`);
  last.s.destroy();
  await asked("/stop");
  const closed = await Promise.all(kept.map((c) => Promise.race([c.ended.then(() => true), wait(5000).then(() => false)])));
  said("stopped", `streams closed: ${closed.join(" ")}`);
}
