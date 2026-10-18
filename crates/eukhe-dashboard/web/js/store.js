// The tab's one state object. `set` merges a patch into the top level;
// subscribers hear about it once per animation frame.
//
// State:
//   link:      { status: 'connecting'|'open'|'offline'|'unavailable', everOpen, catchingUp, retryAt, error,
//                hello: { protocol, build, ops } | null }
//   sessions:  { rows: [{ id, path, cwd, title, modified }], loaded, loading, error }
//   session:   null | turn.js `openSession` shape: { id, path, title, state (AgentConnectionState),
//                summary, cursor, messages, live, tools {callId→tool}, queue, turn, last, bash,
//                goal, serviceTier, memory {stamp,last}, notes, pending }
//   approvals: [{ requestId, step, command, effect, status: 'pending'|'answering'|'elsewhere' }]
//   prefs:     { theme: 'system'|'light'|'dark', enterSendsOnTouch, notify, lane: 'steer'|'followUp' }
//   frames:    [{ seq, at, dir: 'in'|'out', type, data }] ring (≤2000), mutated in place;
//              framesSeq changes on every frame
//   opening:   null | { id, error } while (or after failing) binding a session
//   tick:      changes at 4 Hz while a turn runs (elapsed counters)

const PREFS_KEY = 'eukhe.prefs';

function storedPrefs() {
  const defaults = { theme: 'system', enterSendsOnTouch: false, notify: false, lane: 'steer' };
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
  link: { status: 'connecting', everOpen: false, catchingUp: false, retryAt: 0, error: null, hello: null },
  sessions: { rows: [], loaded: false, loading: false, error: null },
  session: null,
  approvals: [],
  opening: null,
  prefs: storedPrefs(),
  frames: [],
  framesSeq: 0,
  framesDropped: 0,
  tick: 0,
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
