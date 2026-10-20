// The tab's WebSocket to the dashboard bridge (src/protocol.rs): the
// pairing frame first (the kept token, lib/pairing.ts), then numbered
// requests answered by `reply`/`failure`, and pushed frames (`hello`,
// `event`, `approval`, `resync`, `unavailable`, `unpaired`). Reconnects with
// backoff, and at once when the tab comes back (iOS suspends hidden
// sockets). With no token, or after `unpaired`, it waits for a new one.

import { adoptToken, forgetToken, pairingToken, takeFromAddress } from "./pairing.ts";
import { store, type State } from "./store.ts";
import type { ServerFrame } from "./types.ts";

const FRAME_RING = 2000;
const BACKOFF_START_MS = 500;
const BACKOFF_MAX_MS = 5000;

type Waiter = { resolve: (data: unknown) => void; reject: (error: Error) => void };
type FrameType = ServerFrame["type"];
type FrameOf<T extends FrameType> = Extract<ServerFrame, { type: T }>;

let socket: WebSocket | null = null;
let nextId = 1;
let delay = BACKOFF_START_MS;
let retryTimer = 0;
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
    ready();
  }
  if (frame.type === "unavailable") setLink({ status: "unavailable", error: frame.error });
  if (frame.type === "unpaired") {
    forgetToken();
    setLink({ status: "unpaired", error: frame.error });
  }
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
  const token = pairingToken();
  if (!token) {
    setLink({ status: "unpaired", retryAt: 0 });
    return;
  }
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
    // The pairing frame stays out of the frame log: it holds the token.
    current.send(JSON.stringify({ op: "pair", token }));
    setLink({ status: "open", everOpen: true, error: null, hello: null });
  });
  current.addEventListener("message", (event: MessageEvent<string>) => receive(event.data));
  current.addEventListener("close", () => {
    if (socket !== current) return;
    socket = null;
    for (const { reject } of pending.values()) reject(new Error("The connection dropped."));
    pending.clear();
    const { status } = store.get().link;
    // Unpaired: wait for a new link instead of retrying with no token.
    if (status === "unpaired") return;
    schedule();
    if (status === "unavailable") setLink({ status: "unavailable" });
  });
}

/** Reconnect now, skipping the backoff. */
export function reconnect(): void {
  delay = BACKOFF_START_MS;
  connect();
}

/** Drop the socket (it paired with another token or none) and pair again. */
function repair() {
  const old = socket;
  socket = null;
  old?.close();
  for (const { reject } of pending.values()) reject(new Error("The connection dropped."));
  pending.clear();
  setLink({ status: "connecting", error: null });
  reconnect();
}

/** Pair with the link or token in `text` and connect; false when it holds no token. */
export function pair(text: string): boolean {
  if (!adoptToken(text)) return false;
  repair();
  return true;
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

/** Called each time a fresh socket is ready for requests (after `hello`). */
export function onReady(listener: () => void): () => void {
  readyListeners.add(listener);
  return () => readyListeners.delete(listener);
}

/** True while the socket is open. */
export function linkOpen(): boolean {
  return socket?.readyState === WebSocket.OPEN;
}

/** True when the bridge advertised `op` in its `hello`. */
export function supports(op: string): boolean {
  return store.get().link.hello?.ops.includes(op) ?? false;
}

function wake() {
  if (document.visibilityState === "visible" && !socket) reconnect();
}

document.addEventListener("visibilitychange", wake);
window.addEventListener("pageshow", wake);
window.addEventListener("online", wake);
// A pairing link opened in this tab (only the fragment changes, so the page
// does not load again).
window.addEventListener("hashchange", () => {
  if (takeFromAddress()) repair();
});
