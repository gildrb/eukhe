// Chat and session actions shared by the sidebar, the Chat menu, the
// Model menu and Settings. Each resolves with a short success sentence
// or rejects with an Error whose message is shown inline.

import { store } from './store.js';
import { request, run, supports } from './link.js';
import { bind, createSession } from './binding.js';
import { refreshSessions } from './sessions.js';
import { chatHref, navigate } from './router.js';
import { download, confirmDialog } from './ui.js';
import { fmt } from './format.js';

/** Re-read the bound session's AgentConnectionState (switch commands carry no event). */
export async function reloadState() {
  const id = store.get().session ? store.get().session.id : null;
  const fresh = await run({ type: 'get_connection_state' });
  store.set((state) => (state.session && state.session.id === id && fresh
    ? { session: { ...state.session, state: { ...state.session.state, ...fresh } } }
    : null));
  return fresh;
}

/** Run one switch command, then re-read the state so the UI shows the daemon's value. */
export async function setAndReload(command) {
  await run(command);
  await reloadState();
}

/** Start a new chat in the current chat's folder and open it. */
export async function newChat() {
  const current = store.get().session;
  const cwd = current && current.state && current.state.cwd ? current.state.cwd : null;
  const session = await createSession(cwd);
  navigate(chatHref(session.id));
  return session;
}

/** Rename chat `id` (the bridge's `rename` op: through its live worker, else the catalog). */
export async function renameChat(id, name) {
  const trimmed = name.trim();
  if (!trimmed) throw new Error('A name cannot be empty.');
  await request('rename', { sessionId: id, name: trimmed });
  store.set((state) => ({
    sessions: { ...state.sessions, rows: state.sessions.rows.map((row) => (row.id === id ? { ...row, title: trimmed } : row)) },
    ...(state.session && state.session.id === id
      ? { session: { ...state.session, title: trimmed, state: { ...state.session.state, sessionName: trimmed } } }
      : {}),
  }));
  // No list refresh here: the catalog can still answer the old name for a moment.
  return 'Renamed.';
}

/** Fork the whole chat (at its latest entry) into a new chat and open it. */
export async function forkChat() {
  const tree = await run({ type: 'get_session_tree' });
  if (!tree || !tree.leafId) throw new Error('There is nothing to fork yet.');
  const reply = await run({ type: 'fork', entryId: tree.leafId, position: 'at' });
  if (reply && reply.cancelled) throw new Error('The fork was cancelled.');
  const stats = await run({ type: 'get_session_stats' });
  await refreshSessions().catch(() => {});
  if (stats && stats.sessionId) {
    navigate(chatHref(stats.sessionId));
    await bind(stats.sessionId, { force: true }).catch(() => {});
  }
  return 'Forked into a new chat.';
}

/** Download the bound chat as HTML or JSONL (the bridge's `export` op). */
export async function exportChat(format) {
  if (!supports('export')) throw new Error('This eukhe build cannot export from the dashboard.');
  const file = await request('export', { format });
  download(file.name, file.mimeType, file.data);
  return `Downloaded ${file.name}`;
}

/** Compact the bound chat's context (optional instructions). */
export async function compactChat(instructions = '') {
  const text = instructions.trim();
  const result = await run(text ? { type: 'compact', customInstructions: text } : { type: 'compact' });
  return result && Number.isFinite(result.tokensBefore) ? `Compacted ${fmt.tokens(result.tokensBefore)} of context.` : 'Compacted.';
}

/**
 * Delete chat `id` with the bridge's `delete` op (it stops the chat's
 * worker first; a chat open in another window is refused). Resolves with
 * whether it was the tab's current chat (the bridge unbound the tab).
 */
export async function deleteChat(id) {
  const current = store.get().session;
  const wasCurrent = Boolean(current && current.id === id);
  await request('delete', { sessionId: id });
  store.set((state) => ({
    sessions: { ...state.sessions, rows: state.sessions.rows.filter((row) => row.id !== id) },
    ...(wasCurrent ? { session: null, approvals: [] } : {}),
  }));
  refreshSessions().catch(() => {});
  return wasCurrent;
}

/** After deleting the current chat: open the newest remaining one, or a new chat. */
export async function leaveDeletedChat(cwd = null) {
  const rows = (await refreshSessions().catch(() => null)) || store.get().sessions.rows;
  const newest = [...rows].sort((a, b) => (Date.parse(b.modified) || 0) - (Date.parse(a.modified) || 0))[0];
  if (newest) {
    navigate(chatHref(newest.id), { replace: true });
    await bind(newest.id, { force: true }).catch(() => {});
    return;
  }
  const fresh = await createSession(cwd);
  navigate(chatHref(fresh.id), { replace: true });
}

/**
 * Confirm, then delete chat `row` (`{ id, title }`); errors (e.g. open in
 * another window) show inside the dialog. Deleting the current chat lands
 * on the newest remaining one, or a new chat.
 */
export async function confirmDelete(row) {
  const session = store.get().session;
  const cwd = session && session.state ? session.state.cwd : null;
  let wasCurrent = false;
  const yes = await confirmDialog({
    title: 'Delete this chat?',
    body: `“${row.title || 'New chat'}” and its transcript are removed from this computer.`,
    confirm: 'Delete',
    busyLabel: 'Deleting',
    action: async () => {
      try {
        wasCurrent = await deleteChat(row.id);
      } catch (error) {
        const reason = error.message ? error.message.charAt(0).toUpperCase() + error.message.slice(1) : 'eukhe kept it.';
        throw new Error(`Not deleted. ${reason.endsWith('.') ? reason : `${reason}.`}`);
      }
    },
  });
  if (yes && wasCurrent) await leaveDeletedChat(cwd);
  return yes;
}

/** Switch the bound chat's model. */
export async function setModel(model) {
  await setAndReload({ type: 'set_model', provider: model.provider, modelId: model.id });
}

/** The usable models (`get_available_models`) or, with `all`, the catalog. */
export async function listModels(all = false) {
  const reply = await run({ type: all ? 'get_model_catalog' : 'get_available_models' });
  const models = (reply && reply.models) || [];
  return [...models].sort((a, b) => `${a.provider}/${a.name || a.id}`.localeCompare(`${b.provider}/${b.name || b.id}`));
}

/** `provider/id` of a model object. */
export function modelKey(model) {
  return model ? `${model.provider}/${model.id || model.modelId}` : '';
}

export const SERVICE_TIERS = [
  { value: 'auto', label: 'Auto' },
  { value: 'default', label: 'Default' },
  { value: 'flex', label: 'Flex' },
  { value: 'scale', label: 'Scale' },
  { value: 'priority', label: 'Priority' },
];

const LEVEL_WORDS = { off: 'Off', minimal: 'Minimal', low: 'Low', medium: 'Medium', high: 'High', xhigh: 'Max' };

/** A thinking level as a word. */
export function levelWord(level) {
  return LEVEL_WORDS[level] || String(level).charAt(0).toUpperCase() + String(level).slice(1);
}
