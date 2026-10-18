// The saved-session list (`sessions` op), shared by the Inbox and pages.

import { store } from './store.js';
import { request } from './link.js';

let inflight = null;

/** Fetch the list into `state.sessions`; concurrent calls share one request. */
export function refreshSessions() {
  if (inflight) return inflight;
  store.set((state) => ({ sessions: { ...state.sessions, loading: true, error: null } }));
  inflight = request('sessions')
    .then((rows) => {
      store.set({ sessions: { rows: Array.isArray(rows) ? rows : [], loading: false, error: null, at: Date.now() } });
      return rows;
    }, (error) => {
      store.set((state) => ({ sessions: { ...state.sessions, loading: false, error: error.message } }));
      throw error;
    })
    .finally(() => {
      inflight = null;
    });
  return inflight;
}
