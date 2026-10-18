// Which session this tab is bound to: `open` (with the resume cursor when
// re-binding the same session), `new`, and the adoption of their replies.

import { store } from './store.js';
import { request, supports } from './link.js';
import { openSession } from './turn.js';
import { clearApprovals } from './approvals.js';
import { refreshSessions } from './sessions.js';

let inflight = null;

function adopt(reply) {
  const previous = store.get().session;
  const session = openSession(reply, previous, Date.now());
  if (!previous || previous.id !== session.id) clearApprovals();
  store.set((state) => ({
    session,
    opening: null,
    stats: previous && previous.id === session.id ? state.stats : null,
    link: { ...state.link, catchingUp: false },
  }));
  return session;
}

async function openFields(sessionId, resume) {
  if (supports('run')) {
    const fields = sessionId ? { sessionId } : {};
    if (resume) fields.resume = resume;
    return fields;
  }
  // A v1 bridge opens by path: resolve the id through the list.
  if (!sessionId) return { path: null };
  let rows = store.get().sessions.rows;
  if (!rows.some((row) => row.id === sessionId)) rows = (await refreshSessions()) || [];
  const row = rows.find((entry) => entry.id === sessionId);
  if (!row) throw new Error('There is no saved session with this id.');
  return { path: row.path };
}

/**
 * Bind the tab to `sessionId` (null = the most recent session). Re-binding
 * the session already in hand resumes from its cursor. Resolves the
 * session; concurrent calls for the same id share one request.
 */
export function bind(sessionId, { force = false } = {}) {
  const state = store.get();
  if (!force && state.session && sessionId && state.session.id === sessionId && !state.opening) return Promise.resolve(state.session);
  if (inflight && inflight.id === sessionId) return inflight.promise;
  const same = state.session && sessionId && state.session.id === sessionId;
  const resume = same && state.session.cursor ? state.session.cursor : null;
  store.set((current) => ({
    opening: { id: sessionId, error: null },
    link: { ...current.link, catchingUp: Boolean(same) },
  }));
  const entry = { id: sessionId, promise: null };
  entry.promise = openFields(sessionId, resume)
    .then((fields) => request('open', fields))
    .then((reply) => {
      if (inflight === entry) inflight = null;
      return adopt(reply);
    }, (error) => {
      if (inflight === entry) inflight = null;
      store.set((current) => ({ opening: { id: sessionId, error: error.message }, link: { ...current.link, catchingUp: false } }));
      throw error;
    });
  inflight = entry;
  return entry.promise;
}

/** True while an `open` is in flight (its session's events are held by the bridge). */
export function opening() {
  return inflight !== null;
}

/** Start a new session (in `cwd`, else the dashboard's default) and bind to it. */
export async function createSession(cwd = null) {
  store.set({ opening: { id: null, error: null } });
  try {
    const reply = await request('new', cwd ? { cwd } : {});
    const session = adopt(reply);
    refreshSessions().catch(() => {});
    return session;
  } catch (error) {
    store.set({ opening: null });
    throw error;
  }
}
