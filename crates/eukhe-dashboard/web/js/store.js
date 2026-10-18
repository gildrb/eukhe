// The tab's one state object. `set` merges a patch into the top level;
// subscribers hear about it once per animation frame.
//
// State (WebPages codes against this shape):
//   link:      { status: 'connecting'|'open'|'offline'|'unavailable', catchingUp, retryAt, error,
//                hello: { protocol, build, ops } | null }
//   sessions:  { rows: [{ id, path, cwd, title, modified, … }], loading, error, at }
//   session:   null | turn.js `openSession` shape: { id, path, title, state (AgentConnectionState),
//                summary (SessionSummary|null), cursor, messages, live, tools {callId→tool}, queue,
//                turn, last, bash, goal, serviceTier, memory {stamp,last}, notes, pending }
//   approvals: [{ requestId, step, command, effect, status: 'pending'|'answering'|'elsewhere' }]
//   stats:     null | GetSessionStats reply (pages may set it)
//   prefs:     { theme: 'system'|'light'|'dark', enterSendsOnTouch, notify }
//   frames:    [{ seq, at, dir: 'in'|'out', type, data }] ring (≤2000), mutated in place;
//              framesSeq changes on every frame, framesDropped counts evicted frames
//   opening:   null | { id, error } while (or after failing) binding a session
//   ui:        { inbox: bool (desktop Inbox shown), hidden: bool (tab hidden) }

const PREFS_KEY = 'eukhe.prefs';

function storedPrefs() {
  const defaults = { theme: 'system', enterSendsOnTouch: false, notify: false };
  try {
    const saved = JSON.parse(localStorage.getItem(PREFS_KEY) || '{}');
    const theme = localStorage.getItem('theme');
    return {
      ...defaults,
      ...saved,
      theme: theme === 'dark' || theme === 'light' ? theme : 'system',
    };
  } catch {
    return defaults;
  }
}

let state = {
  link: { status: 'connecting', catchingUp: false, retryAt: 0, error: null, hello: null },
  sessions: { rows: [], loading: false, error: null, at: 0 },
  session: null,
  approvals: [],
  opening: null,
  stats: null,
  prefs: storedPrefs(),
  frames: [],
  framesSeq: 0,
  framesDropped: 0,
  ui: { inbox: true, hidden: document.hidden },
};

const listeners = new Set();
let scheduled = false;

function flush() {
  scheduled = false;
  for (const listener of [...listeners]) listener(state);
}

export const store = {
  get() {
    return state;
  },
  set(patch) {
    const next = typeof patch === 'function' ? patch(state) : patch;
    if (!next) return;
    state = { ...state, ...next };
    if (scheduled) return;
    scheduled = true;
    // A hidden tab gets no animation frames; status still has to move.
    if (document.hidden) queueMicrotask(flush);
    else requestAnimationFrame(flush);
  },
  subscribe(fn) {
    listeners.add(fn);
    return () => listeners.delete(fn);
  },
};

export { PREFS_KEY };
