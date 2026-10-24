// Which session this tab is bound to (`open`, with the resume cursor when
// re-binding the same one; `new`), the saved-session list behind the
// sidebar, and shell approvals.

import { linkServed, request, run, supports } from "./link.ts";
import { store } from "./store.ts";
import { openSession, type Session } from "./turn.ts";
import type { ApprovalRequest, OpenReply, SessionRow } from "./types.ts";

const ELSEWHERE_SHOWN_MS = 3000;

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
    approvals: previous && previous.id === session.id ? state.approvals : [],
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

// ------------------------------------------------------------ approvals --

function setApproval(requestId: string, status: "answering" | "elsewhere") {
  store.set((state) => ({
    approvals: state.approvals.map((item) =>
      item.requestId === requestId ? { ...item, status } : item,
    ),
  }));
}

function dropApproval(requestId: string) {
  store.set((state) => ({
    approvals: state.approvals.filter((item) => item.requestId !== requestId),
  }));
}

/** Add the request of one `approval` frame (deduplicated by id). */
export function addApproval(asked: ApprovalRequest): void {
  if (!asked.requestId) return;
  store.set((state) => {
    if (state.approvals.some((item) => item.requestId === asked.requestId)) return null;
    return {
      approvals: [
        ...state.approvals,
        {
          requestId: asked.requestId,
          step: asked.step ?? 0,
          command: asked.command || "",
          effects: Array.isArray(asked.effects) ? asked.effects : [],
          status: "pending",
        },
      ],
    };
  });
}

/** The session no longer waits on a request (an `approval_settled` frame): one still pending was settled elsewhere, so say so briefly, then drop it; one this tab is answering goes when its answer returns. */
export function approvalSettled(requestId: string): void {
  const settled = store.get().approvals.find((item) => item.requestId === requestId);
  if (settled?.status !== "pending") return;
  setApproval(requestId, "elsewhere");
  setTimeout(() => dropApproval(requestId), ELSEWHERE_SHOWN_MS);
}

/** Answer one request; one answered elsewhere shows for a moment, then goes. */
export async function answerApproval(
  requestId: string,
  verdict: "approve" | "deny",
): Promise<void> {
  setApproval(requestId, "answering");
  try {
    await run({ type: "answer_shell_approval", requestId, verdict });
    dropApproval(requestId);
  } catch {
    setApproval(requestId, "elsewhere");
    setTimeout(() => dropApproval(requestId), ELSEWHERE_SHOWN_MS);
  }
}
