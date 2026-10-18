// The tab's WebSocket to the dashboard bridge (src/protocol.rs): numbered
// requests answered by `reply`/`failure`, and pushed frames (`hello`,
// `event`, `approval`, `resync`, `unavailable`). Reconnects with backoff,
// and at once when the tab comes back (iOS suspends hidden sockets).

import { store, type State } from "./store.ts";
import type { ServerFrame } from "./types.ts";

const FRAME_RING = 2000;
const HELLO_WAIT_MS = 400;
const BACKOFF_START_MS = 500;
const BACKOFF_MAX_MS = 5000;

type Waiter = { resolve: (data: unknown) => void; reject: (error: Error) => void };
type FrameType = ServerFrame["type"];
type FrameOf<T extends FrameType> = Extract<ServerFrame, { type: T }>;

let socket: WebSocket | null = null;
let nextId = 1;
let delay = BACKOFF_START_MS;
let retryTimer = 0;
let readyTimer = 0;
let frameSeq = 0;
const pending = new Map<number, Waiter>();
const listeners = new Set<(frame: ServerFrame) => void>();
const readyListeners = new Set<() => void>();

function setLink(patch: Partial<State["link"]>) {
  store.set((state) => ({ link: { ...state.link, ...patch } }));
}

function record(dir: "in" | "out", frame: Record<string, unknown>) {
  const { frames } = store.get();
  frameSeq += 1;
  const type =
    typeof frame.type === "string" ? frame.type : typeof frame.op === "string" ? frame.op : "?";
  frames.push({ seq: frameSeq, at: Date.now(), dir, type, data: frame });
  if (frames.length > FRAME_RING) frames.splice(0, frames.length - FRAME_RING);
  store.set({ framesSeq: frameSeq });
}

function ready() {
  clearTimeout(readyTimer);
  readyTimer = 0;
  for (const listener of readyListeners) listener();
}

function receive(text: string) {
  let frame: ServerFrame;
  try {
    frame = JSON.parse(text);
  } catch {
    return;
  }
  record("in", frame);
  if (frame.type === "reply" || frame.type === "failure") {
    const waiter = pending.get(frame.id);
    if (!waiter) return;
    pending.delete(frame.id);
    if (frame.type === "reply") waiter.resolve(frame.data);
    else waiter.reject(new Error(frame.error));
    return;
  }
  if (frame.type === "hello") {
    setLink({ hello: { protocol: frame.protocol, build: frame.build, ops: frame.ops ?? [] } });
    if (readyTimer) ready();
  }
  if (frame.type === "unavailable") setLink({ status: "unavailable", error: frame.error });
  for (const listener of listeners) listener(frame);
}

function schedule() {
  clearTimeout(retryTimer);
  setLink({ status: "offline", retryAt: Date.now() + delay });
  retryTimer = window.setTimeout(connect, delay);
  delay = Math.min(delay * 2, BACKOFF_MAX_MS);
}

/** Open the socket (no-op while one is open or opening). */
export function connect(): void {
  if (
    socket &&
    (socket.readyState === WebSocket.OPEN || socket.readyState === WebSocket.CONNECTING)
  )
    return;
  clearTimeout(retryTimer);
  const url = new URL("api/ws", location.href);
  url.protocol = location.protocol === "https:" ? "wss:" : "ws:";
  url.hash = "";
  url.search = "";
  const current = new WebSocket(url);
  socket = current;
  const unavailable = store.get().link.status === "unavailable";
  setLink({ status: unavailable ? "unavailable" : "connecting", retryAt: 0 });
  current.addEventListener("open", () => {
    if (socket !== current) return;
    setLink({ status: "open", everOpen: true, error: null, hello: null });
    // A v2 bridge says `hello` first; an older one never does.
    readyTimer = window.setTimeout(ready, HELLO_WAIT_MS);
  });
  current.addEventListener("message", (event: MessageEvent<string>) => receive(event.data));
  current.addEventListener("close", () => {
    if (socket !== current) return;
    socket = null;
    clearTimeout(readyTimer);
    readyTimer = 0;
    for (const { reject } of pending.values()) reject(new Error("The connection dropped."));
    pending.clear();
    const keepUnavailable = store.get().link.status === "unavailable";
    schedule();
    if (keepUnavailable) setLink({ status: "unavailable" });
  });
}

/** Reconnect now, skipping the backoff. */
export function reconnect(): void {
  delay = BACKOFF_START_MS;
  connect();
}

/**
 * The bridge served a session (`open` or `new` succeeded): the next drop
 * retries at once again. A socket that opens and then hears `unavailable`
 * keeps doubling its delay (0.5 s to 5 s), so a missing daemon is not
 * asked for every half second.
 */
export function linkServed(): void {
  delay = BACKOFF_START_MS;
}

/** Send `{ id, op, ...fields }`; resolves with the reply's data. */
export function request<T = unknown>(op: string, fields: Record<string, unknown> = {}): Promise<T> {
  const open = socket;
  if (!open || open.readyState !== WebSocket.OPEN) return Promise.reject(new Error("Offline."));
  const id = nextId;
  nextId += 1;
  const frame = { id, op, ...fields };
  const { promise, resolve, reject } = Promise.withResolvers<T>();
  pending.set(id, { resolve: resolve as (data: unknown) => void, reject });
  record("out", frame);
  open.send(JSON.stringify(frame));
  return promise;
}

/** Run one DaemonCommand (`type` snake_case, camelCase fields) on the bound session. */
export function run<T = unknown>(command: { type: string; [field: string]: unknown }): Promise<T> {
  return request<T>("run", { command });
}

/** Hear frames of one `type`. */
export function onFrame<T extends FrameType>(
  type: T,
  listener: (frame: FrameOf<T>) => void,
): () => void {
  const isType = (frame: ServerFrame): frame is FrameOf<T> => frame.type === type;
  const hear = (frame: ServerFrame) => {
    if (isType(frame)) listener(frame);
  };
  listeners.add(hear);
  return () => listeners.delete(hear);
}

/** Called each time a fresh socket is ready for requests (after `hello`, or its timeout). */
export function onReady(listener: () => void): () => void {
  readyListeners.add(listener);
  return () => readyListeners.delete(listener);
}

/** True while the socket is open. */
export function linkOpen(): boolean {
  return socket?.readyState === WebSocket.OPEN;
}

/** True when the bridge advertised `op` (v2), or for the v1 ops on an older bridge. */
export function supports(op: string): boolean {
  const { hello } = store.get().link;
  if (hello) return hello.ops.includes(op);
  return ["sessions", "open", "new", "prompt", "abort", "memory"].includes(op);
}

function wake() {
  if (document.visibilityState === "visible" && !socket) reconnect();
}

document.addEventListener("visibilitychange", wake);
window.addEventListener("pageshow", wake);
window.addEventListener("online", wake);
