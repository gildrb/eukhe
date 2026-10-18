// The tab's WebSocket to the dashboard bridge (src/protocol.rs): numbered
// requests answered by `reply`/`failure`, and pushed frames (`hello`,
// `event`, `approval`, `resync`, `unavailable`). Reconnects with backoff,
// and at once when the tab comes back (iOS suspends hidden sockets).

import { store } from './store.js';

const FRAME_RING = 2000;
const HELLO_WAIT_MS = 400;
const BACKOFF_START_MS = 500;
const BACKOFF_MAX_MS = 5000;

let socket = null;
let nextId = 1;
let delay = BACKOFF_START_MS;
let retryTimer = 0;
let readyTimer = 0;
const pending = new Map();
const listeners = new Map();
const readyListeners = new Set();
let frameSeq = 0;

function setLink(patch) {
  store.set((state) => ({ link: { ...state.link, ...patch } }));
}

function record(dir, frame) {
  const { frames } = store.get();
  frameSeq += 1;
  frames.push({ seq: frameSeq, at: Date.now(), dir, type: frame.type || frame.op || '?', data: frame });
  let dropped = 0;
  while (frames.length > FRAME_RING) {
    frames.shift();
    dropped += 1;
  }
  store.set((state) => ({ framesSeq: frameSeq, framesDropped: state.framesDropped + dropped }));
}

function emit(type, frame) {
  for (const key of [type, '*']) {
    const set = listeners.get(key);
    if (!set) continue;
    for (const fn of [...set]) fn(frame);
  }
}

function ready() {
  clearTimeout(readyTimer);
  readyTimer = 0;
  for (const fn of [...readyListeners]) fn();
}

function receive(text) {
  let frame;
  try {
    frame = JSON.parse(text);
  } catch {
    return;
  }
  record('in', frame);
  if (frame.type === 'reply' || frame.type === 'failure') {
    const waiter = pending.get(frame.id);
    if (!waiter) return;
    pending.delete(frame.id);
    if (frame.type === 'reply') waiter.resolve(frame.data);
    else waiter.reject(new Error(frame.error));
    return;
  }
  if (frame.type === 'hello') {
    setLink({ hello: { protocol: frame.protocol, build: frame.build, ops: frame.ops || [] } });
    if (readyTimer) ready();
  }
  if (frame.type === 'unavailable') setLink({ status: 'unavailable', error: frame.error });
  emit(frame.type, frame);
}

function schedule() {
  clearTimeout(retryTimer);
  setLink({ status: 'offline', retryAt: Date.now() + delay });
  retryTimer = setTimeout(connect, delay);
  delay = Math.min(delay * 2, BACKOFF_MAX_MS);
}

/** Open the socket (no-op while one is open or opening). */
export function connect() {
  if (socket && (socket.readyState === WebSocket.OPEN || socket.readyState === WebSocket.CONNECTING)) return;
  clearTimeout(retryTimer);
  const url = new URL('api/ws', location.href);
  url.protocol = location.protocol === 'https:' ? 'wss:' : 'ws:';
  url.hash = '';
  url.search = '';
  const current = new WebSocket(url);
  socket = current;
  const unavailable = store.get().link.status === 'unavailable';
  setLink({ status: unavailable ? 'unavailable' : 'connecting', retryAt: 0 });
  current.addEventListener('open', () => {
    if (socket !== current) return;
    delay = BACKOFF_START_MS;
    setLink({ status: 'open', error: null, hello: null });
    // A v2 bridge says `hello` first; an older one never does.
    readyTimer = setTimeout(ready, HELLO_WAIT_MS);
  });
  current.addEventListener('message', (event) => receive(event.data));
  current.addEventListener('close', () => {
    if (socket !== current) return;
    socket = null;
    clearTimeout(readyTimer);
    readyTimer = 0;
    for (const { reject } of pending.values()) reject(new Error('The connection dropped.'));
    pending.clear();
    const keepUnavailable = store.get().link.status === 'unavailable';
    schedule();
    if (keepUnavailable) setLink({ status: 'unavailable' });
  });
}

/** Reconnect now, skipping the backoff. */
export function reconnect() {
  delay = BACKOFF_START_MS;
  connect();
}

/** Send `{ id, op, ...fields }`; resolves with the reply's data. */
export function request(op, fields = {}) {
  const open = socket;
  if (!open || open.readyState !== WebSocket.OPEN) {
    return Promise.reject(new Error('Offline.'));
  }
  const id = nextId;
  nextId += 1;
  const frame = { id, op, ...fields };
  return new Promise((resolve, reject) => {
    pending.set(id, { resolve, reject });
    record('out', frame);
    open.send(JSON.stringify(frame));
  });
}

/** Run one DaemonCommand (`type` snake_case, camelCase fields) on the bound session. */
export function run(command) {
  return request('run', { command });
}

/** Hear frames of one `type` (`'*'` hears every inbound frame). */
export function onFrame(type, fn) {
  if (!listeners.has(type)) listeners.set(type, new Set());
  listeners.get(type).add(fn);
  return () => listeners.get(type).delete(fn);
}

/** Called each time a fresh socket is ready for requests (after `hello`, or its timeout). */
export function onReady(fn) {
  readyListeners.add(fn);
  return () => readyListeners.delete(fn);
}

/** 'connecting' | 'open' | 'offline'. */
export function linkState() {
  if (socket && socket.readyState === WebSocket.OPEN) return 'open';
  if (socket && socket.readyState === WebSocket.CONNECTING) return 'connecting';
  return 'offline';
}

/** True when the bridge advertised `op` (v2), or for the v1 ops on an older bridge. */
export function supports(op) {
  const { hello } = store.get().link;
  if (hello) return hello.ops.includes(op);
  return ['sessions', 'open', 'new', 'prompt', 'abort', 'memory'].includes(op);
}

function wake() {
  if (document.visibilityState === 'visible' && linkState() === 'offline') reconnect();
}

document.addEventListener('visibilitychange', wake);
window.addEventListener('pageshow', wake);
window.addEventListener('online', wake);
