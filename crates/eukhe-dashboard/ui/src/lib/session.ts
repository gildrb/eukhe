// Which session this tab is bound to (`open`, with the resume cursor when
// re-binding the same one; `new`) and the saved-session list behind the
// sidebar.

import { linkServed, request, supports } from "./link.ts";
import { store } from "./store.ts";
import { openSession, type Session } from "./turn.ts";
import type { OpenReply, SessionRow } from "./types.ts";

let sessionsInflight: Promise<SessionRow[]> | null = null;

/** Fetch the list into `state.sessions`; concurrent calls share one request. */
export function refreshSessions(): Promise<SessionRow[]> {
  if (sessionsInflight) return sessionsInflight;
  store.set((state) => ({ sessions: { ...state.sessions, loading: true, error: null } }));
  sessionsInflight = request<SessionRow[]>("sessions")
    .then(
      (rows) => {
        const list = Array.isArray(rows) ? rows : [];
        store.set({ sessions: { rows: list, loaded: true, loading: false, error: null } });
        return list;
      },
      (error: Error) => {
        store.set((state) => ({
          sessions: { ...state.sessions, loading: false, error: error.message },
        }));
        throw error;
      },
    )
    .finally(() => {
      sessionsInflight = null;
    });
  return sessionsInflight;
}

function adopt(reply: OpenReply): Session {
  linkServed();
  const previous = store.get().session;
  const session = openSession(reply, previous, Date.now());
  store.set((state) => ({
    session,
    opening: null,
    link: { ...state.link, catchingUp: false },
  }));
  return session;
}

async function openFields(
  sessionId: string | null,
  resume: unknown,
): Promise<Record<string, unknown>> {
  if (supports("run")) {
    const fields: Record<string, unknown> = sessionId ? { sessionId } : {};
    if (resume) fields.resume = resume;
    return fields;
  }
  // A v1 bridge opens by path: resolve the id through the list.
  if (!sessionId) return { path: null };
  let rows = store.get().sessions.rows;
  if (!rows.some((row) => row.id === sessionId)) rows = await refreshSessions();
  const row = rows.find((entry) => entry.id === sessionId);
  if (!row) throw new Error("There is no saved session with this id.");
  return { path: row.path };
}

let inflight: { id: string | null; promise: Promise<Session> } | null = null;

/**
 * Bind the tab to `sessionId` (null = the most recent session). Re-binding
 * the session already in hand resumes from its cursor. Concurrent calls
 * for the same id share one request.
 */
export function bind(sessionId: string | null, force = false): Promise<Session> {
  const state = store.get();
  const same = Boolean(state.session && sessionId && state.session.id === sessionId);
  if (!force && same && state.session && !state.opening) return Promise.resolve(state.session);
  if (inflight && inflight.id === sessionId) return inflight.promise;
  const resume = same && state.session?.cursor ? state.session.cursor : null;
  store.set((current) => ({
    opening: { id: sessionId, error: null },
    link: { ...current.link, catchingUp: same },
  }));
  const entry: { id: string | null; promise: Promise<Session> } = {
    id: sessionId,
    promise: openFields(sessionId, resume)
      .then((fields) => request<OpenReply>("open", fields))
      .then(
        (reply) => {
          if (inflight === entry) inflight = null;
          return adopt(reply);
        },
        (error: Error) => {
          if (inflight === entry) inflight = null;
          store.set((current) => ({
            opening: { id: sessionId, error: error.message },
            link: { ...current.link, catchingUp: false },
          }));
          throw error;
        },
      ),
  };
  inflight = entry;
  return entry.promise;
}

/** True while an `open` is in flight (its session's events are held by the bridge). */
export function opening(): boolean {
  return inflight !== null;
}

/** Start a new session (in `cwd`, else the dashboard's default) and bind to it. */
export async function createSession(cwd: string | null = null): Promise<Session> {
  store.set({ opening: { id: null, error: null } });
  try {
    const session = adopt(await request<OpenReply>("new", cwd ? { cwd } : {}));
    void refreshSessions().catch(() => {});
    return session;
  } catch (error) {
    store.set({ opening: null });
    throw error;
  }
}
