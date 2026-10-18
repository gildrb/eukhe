// Shell approvals (`approval` frames → `state.approvals`) and the one
// path that answers them.

import { store } from './store.js';
import { run } from './link.js';

const ELSEWHERE_SHOWN_MS = 1000;

function setStatus(requestId, status) {
  store.set((state) => ({
    approvals: state.approvals.map((item) => (item.requestId === requestId ? { ...item, status } : item)),
  }));
}

function drop(requestId) {
  store.set((state) => ({ approvals: state.approvals.filter((item) => item.requestId !== requestId) }));
}

/** Add the request of one `approval` frame (deduplicated by id). */
export function addApproval(frame) {
  const request = frame.request || frame;
  if (!request || !request.requestId) return;
  store.set((state) => {
    if (state.approvals.some((item) => item.requestId === request.requestId)) return null;
    return {
      approvals: [...state.approvals, {
        requestId: request.requestId,
        step: request.step ?? 0,
        command: request.command || '',
        effect: request.effect || 'exec',
        status: 'pending',
      }],
    };
  });
}

/** Clear every request the agent moved past (answered by another client). */
export function settleApprovals() {
  const { approvals } = store.get();
  if (!approvals.some((item) => item.status === 'pending')) return;
  store.set({ approvals: approvals.filter((item) => item.status === 'answering') });
}

/** Drop all requests (the tab bound another session). */
export function clearApprovals() {
  store.set({ approvals: [] });
}

/**
 * Answer one request. Resolves true when the daemon took the answer;
 * false when it was answered elsewhere (shown for a second, then dropped).
 */
export async function answerApproval(requestId, verdict) {
  setStatus(requestId, 'answering');
  try {
    await run({ type: 'answer_shell_approval', requestId, verdict });
    drop(requestId);
    return true;
  } catch {
    setStatus(requestId, 'elsewhere');
    setTimeout(() => drop(requestId), ELSEWHERE_SHOWN_MS);
    return false;
  }
}
