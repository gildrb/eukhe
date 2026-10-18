// The session sheet (tap the title or `⋯`): model, thinking level, service
// tier, context, cost, rename, fork, export, compact, delete, theme and
// the session's pages. Also the session actions the Sessions page shares.

import { store } from '../store.js';
import { href } from '../router.js';
import { refreshSessions } from '../sessions.js';
import { createSession } from '../binding.js';
import { setPref } from '../prefs.js';
import { derivePhase } from '../turn.js';
import { actionButton, contextMeter, failed, modelName, reloadState, segmented, stats, whenBound } from './kit.js';

const UNDO_MS = 6000;
const SERVICE_TIERS = [
  { value: 'auto', label: 'Auto' },
  { value: 'default', label: 'Default' },
  { value: 'flex', label: 'Flex' },
  { value: 'scale', label: 'Scale' },
  { value: 'priority', label: 'Priority' },
];
const THEMES = [
  { value: 'system', label: 'System' },
  { value: 'light', label: 'Light' },
  { value: 'dark', label: 'Dark' },
];

function basename(path) {
  const parts = String(path || '').split('/').filter(Boolean);
  return parts.length ? parts[parts.length - 1] : '/';
}

/** Bind the tab to `row` (via its chat route) unless it already is; resolves with the session. */
export async function bindRow(ctx, row) {
  const { session } = store.get();
  if (session && session.id === row.id) return session;
  ctx.navigate(href('chat', { sessionId: row.id }));
  return whenBound(row.id);
}

/** Rename: the bound session by `set_session_name`, a saved one by `rename_saved_session`. */
export async function renameSession(ctx, row, name) {
  const trimmed = name.trim();
  if (!trimmed) throw new Error('A name cannot be empty.');
  const { session } = store.get();
  if (session && session.id === row.id) await ctx.run({ type: 'set_session_name', name: trimmed });
  else await ctx.run({ type: 'rename_saved_session', sessionPath: row.path, name: trimmed });
  await refreshSessions().catch(() => {});
}

/** A sheet with one name field; Save renames. */
export function renameSheet(ctx, row) {
  const { ui } = ctx;
  let value = row.title || '';
  let handle = null;
  const save = actionButton({
    label: 'Save',
    busyLabel: 'Saving',
    kind: 'primary',
    work: async () => {
      await renameSession(ctx, row, value);
      handle.close();
      ui.toast({ text: 'Renamed.' });
    },
    onError: (error) => failed(error, 'Not renamed'),
  });
  handle = ui.sheet({
    title: 'Rename',
    content: ui.field({
      label: 'Name',
      value,
      name: 'session-name',
      onInput: (next) => {
        value = next;
      },
      onCommit: (next) => {
        value = next;
        save.click();
      },
    }),
    actions: save,
  });
  const input = handle.body.querySelector('input');
  if (input) requestAnimationFrame(() => input.select());
  return handle;
}

/** Export the bound session; the bridge has no download route, so the host path is shown with Copy. */
export async function exportSession(ctx, format) {
  const { ui } = ctx;
  const reply = await ctx.run({ type: format === 'html' ? 'export_html' : 'export_jsonl' });
  const path = reply && reply.path ? reply.path : '';
  ui.toast({
    text: path ? `Exported to ${path}` : 'Exported.',
    action: path ? { label: 'Copy path', onClick: () => navigator.clipboard.writeText(path).catch(() => {}) } : null,
  });
}

/**
 * Fork the bound session from one of its user messages
 * (`get_user_messages_for_forking` → `fork`). The worker moves to the
 * fork; `get_session_stats` names it, and the tab follows.
 */
export async function forkSheet(ctx) {
  const { ui, fmt } = ctx;
  const listing = ctx.run({ type: 'get_user_messages_for_forking' });
  let handle = null;
  const pick = async (entry, position) => {
    const reply = await ctx.run({ type: 'fork', entryId: entry.entryId, position });
    if (reply && reply.cancelled) {
      ui.toast({ text: 'Fork cancelled.' });
      return;
    }
    const after = await ctx.run({ type: 'get_session_stats' });
    const forkId = after && after.sessionId;
    if (forkId && reply && reply.selectedText) {
      try {
        localStorage.setItem(`eukhe.draft.${forkId}`, reply.selectedText);
      } catch {
        // Private mode: the text stays in the old session only.
      }
    }
    if (handle) handle.close();
    await refreshSessions().catch(() => {});
    if (forkId) ctx.navigate(href('chat', { sessionId: forkId }));
    ui.toast({ text: position === 'before' ? 'Forked. The message is back in the composer.' : 'Forked.' });
  };
  const render = (data) => {
    const messages = data && Array.isArray(data.messages) ? [...data.messages].reverse() : [];
    if (!messages.length) return ui.empty({ title: 'Nothing to fork from yet.', body: 'A fork starts at one of your messages.' });
    const list = ui.el('ol', { class: 'pg-forks' });
    for (const entry of messages) {
      const text = entry.text.split('\n')[0];
      list.append(ui.el('li', { class: 'pg-fork' },
        ui.el('p', { class: 'pg-fork-text', text }),
        ui.el('div', { class: 'pg-actions' },
          actionButton({ label: 'Fork before', busyLabel: 'Forking', work: () => pick(entry, 'before'), onError: (error) => failed(error, 'Not forked') }),
          actionButton({ label: 'Fork after', busyLabel: 'Forking', work: () => pick(entry, 'at'), onError: (error) => failed(error, 'Not forked') }))));
    }
    return ui.el('div', { class: 'pg-stack' },
      ui.el('p', { class: 'pg-line small', text: `${fmt.num(messages.length)} of your messages, newest first. “Before” puts the message back in the composer; “after” keeps it.` }),
      list);
  };
  handle = ui.sheet({ title: 'Fork from…', content: ui.delayed(listing, render, { lines: 6, retry: () => ctx.run({ type: 'get_user_messages_for_forking' }) }) });
  return handle;
}

/**
 * Delete a saved session with a 6 s Undo. The daemon refuses to delete
 * the bound session, so the tab first switches to the newest other one.
 */
export async function deleteSession(ctx, row) {
  const { ui } = ctx;
  const yes = await ui.confirm({
    title: `Delete “${row.title || 'this session'}”?`,
    body: 'Its transcript file is removed from disk. You have a few seconds to undo.',
    action: 'Delete',
  });
  if (!yes) return;
  const { session, sessions } = store.get();
  if (session && session.id === row.id) {
    const other = sessions.rows.find((candidate) => candidate.id !== row.id);
    if (!other) {
      ui.toast({ text: 'This is the only session. Start another before deleting it.', error: true });
      return;
    }
    ctx.navigate(href('chat', { sessionId: other.id }));
    try {
      await whenBound(other.id);
    } catch (error) {
      failed(error, 'Not deleted');
      return;
    }
  }
  const index = store.get().sessions.rows.findIndex((candidate) => candidate.id === row.id);
  store.set((state) => ({ sessions: { ...state.sessions, rows: state.sessions.rows.filter((candidate) => candidate.id !== row.id) } }));
  const restore = () => store.set((state) => {
    if (state.sessions.rows.some((candidate) => candidate.id === row.id)) return null;
    const rows = state.sessions.rows.slice();
    rows.splice(Math.max(0, Math.min(index, rows.length)), 0, row);
    return { sessions: { ...state.sessions, rows } };
  });
  const note = ui.toast({ text: 'Session deleted.', undo: UNDO_MS });
  if (await note.undone) {
    restore();
    return;
  }
  try {
    const reply = await ctx.run({ type: 'delete_saved_session', sessionPath: row.path });
    if (reply && reply.ok === false) throw new Error(reply.error || 'the daemon kept it');
  } catch (error) {
    restore();
    failed(error, 'Not deleted');
  }
  refreshSessions().catch(() => {});
}

/** A sheet asking for the new session's folder; `createSession` binds it, then the tab opens it. */
export function newSessionSheet(ctx, cwd) {
  const { ui } = ctx;
  let value = cwd || '';
  let handle = null;
  const start = actionButton({
    label: 'Start',
    busyLabel: 'Starting',
    kind: 'primary',
    work: async () => {
      const session = await createSession(value.trim() || null);
      handle.close();
      ctx.navigate(href('chat', { sessionId: session.id }));
    },
    onError: (error) => failed(error, 'Not started'),
  });
  handle = ui.sheet({
    title: 'New session',
    content: ui.el('div', { class: 'pg-stack' },
      ui.field({
        label: 'Folder',
        value,
        name: 'session-cwd',
        placeholder: 'Home folder…',
        onInput: (next) => {
          value = next;
        },
        onCommit: (next) => {
          value = next;
          start.click();
        },
      }),
      ui.el('p', { class: 'pg-line small', text: 'The agent works in this folder. Leave it empty for your home folder.' })),
    actions: start,
  });
  return handle;
}

/** The session's pages as one compact grid (two rows at phone width), first in the sheet. */
function pageLinks(ctx, session) {
  const { ui } = ctx;
  const queued = session.queue.steering.length + session.queue.followUps.length;
  const link = (label, page, note = null) => ui.el('a', { class: 'pg-tile target', href: href(page, { sessionId: session.id }) },
    ui.el('span', { class: 'pg-tile-label', text: label }),
    note ? ui.el('span', { class: 'pg-tile-note fig', text: note }) : null);
  return ui.el('nav', { class: 'pg-tiles', 'aria-label': 'Session pages' },
    link('Turn', 'turn', session.turn.running ? 'live' : null),
    link('Queue', 'queue', queued ? String(queued) : null),
    link('Memory', 'memory'),
    link('Usage', 'usage'),
    link('Model', 'model'),
    link('Settings', 'settings'),
    link('Events', 'events'));
}

function sheetContent(ctx, session, state) {
  const { ui, fmt } = ctx;
  const row = { id: session.id, path: session.path, title: session.title };
  const phase = derivePhase(state, Date.now(), fmt);
  const levels = session.state.availableThinkingLevels && session.state.availableThinkingLevels.length ? session.state.availableThinkingLevels : ['off'];
  const usage = state.stats && state.stats.sessionId === session.state.sessionId ? state.stats : null;
  const summary = session.summary;
  const others = summary && summary.attachedClients > 1 ? summary.attachedClients - 1 : 0;
  const messages = usage ? usage.totalMessages : session.state.messageCount;
  return ui.el('div', { class: 'pg-stack pg-sheet' },
    pageLinks(ctx, session),
    ui.el('p', { class: 'pg-status' },
      ui.el('span', { class: 'pg-status-phase', text: phase.label }),
      phase.detail ? ui.el('span', { class: 'pg-status-detail', text: ` · ${phase.detail}` }) : null),
    ui.field({
      label: 'Name',
      value: session.title,
      name: 'session-name',
      onCommit: (name) => {
        if (name.trim() === session.title) return;
        renameSession(ctx, row, name).then(() => ui.toast({ text: 'Renamed.' }), (error) => failed(error, 'Not renamed'));
      },
    }),
    ui.row({
      lead: 'Model',
      title: modelName(session.state.model),
      trail: '→',
      href: href('model', { sessionId: session.id }),
    }),
    segmented({
      label: 'Thinking',
      options: levels,
      value: session.state.thinkingLevel,
      onPick: async (level) => {
        await ctx.run({ type: 'set_thinking_level', level });
        await reloadState(ctx);
      },
    }),
    segmented({
      label: 'Service tier',
      options: SERVICE_TIERS,
      value: session.serviceTier || session.state.serviceTier,
      onPick: (serviceTier) => ctx.run({ type: 'set_service_tier', serviceTier }),
    }),
    ui.el('div', { class: 'pg-field' }, ui.el('span', { class: 'pg-field-label', text: 'Context' }), contextMeter(session.state.contextUsage)),
    stats([
      ['Cost', usage ? fmt.cost(usage.cost) : null],
      ['Tokens', usage ? fmt.tokens(usage.tokens.total) : null],
      ['Messages', Number.isFinite(messages) ? fmt.num(messages) : null],
      ['Folder', basename(session.state.cwd)],
      others ? ['Also open in', `${fmt.num(others)} other ${others === 1 ? 'client' : 'clients'}`] : [null, null],
    ]),
    ui.el('div', { class: 'pg-actions pg-actions-wrap' },
      ui.button({ label: 'Fork…', onClick: () => forkSheet(ctx) }),
      actionButton({ label: 'Export HTML', busyLabel: 'Exporting', work: () => exportSession(ctx, 'html') }),
      actionButton({ label: 'Export JSONL', busyLabel: 'Exporting', work: () => exportSession(ctx, 'jsonl') }),
      actionButton({
        label: 'Compact',
        busyLabel: 'Compacting',
        work: async () => {
          const result = await ctx.run({ type: 'compact' });
          ui.toast({ text: result && Number.isFinite(result.tokensBefore) ? `Compacted ${fmt.tokens(result.tokensBefore)} of context.` : 'Compacted.' });
        },
        onError: (error) => failed(error, 'Not compacted'),
      })),
    segmented({
      label: 'Theme',
      options: THEMES,
      value: state.prefs.theme,
      onPick: (theme) => setPref('theme', theme),
    }),
    ui.el('div', { class: 'pg-actions pg-sheet-danger' },
      ui.button({ label: 'Delete…', kind: 'danger', onClick: () => deleteSession(ctx, row) })));
}

/**
 * Open the session sheet over the current page. It follows the store
 * while open (model, level and tier changes repaint it); links close it.
 */
export function openSessionSheet(ctx) {
  const { ui } = ctx;
  const host = ui.el('div', { class: 'pg-sheet-host' });
  let painted = null;
  const paint = (state) => {
    const { session } = state;
    const key = session ? [session.state, session.title, session.serviceTier, session.turn.running, session.queue, state.stats, state.prefs.theme] : null;
    if (painted && key && painted.length === key.length && painted.every((part, index) => part === key[index])) return;
    if (host.contains(document.activeElement) && document.activeElement.tagName === 'INPUT') return;
    painted = key;
    host.replaceChildren(session
      ? sheetContent({ ...ctx, state }, session, state)
      : ui.empty({ title: 'No session is open.', action: { label: 'See all sessions', href: href('sessions') } }));
  };
  paint(store.get());
  const stop = store.subscribe(paint);
  const handle = ui.sheet({ title: 'Session', content: host, onClose: stop });
  host.addEventListener('click', (event) => {
    if (event.target.closest('a[href]')) handle.close();
  });
  if (store.get().session) {
    ctx.run({ type: 'get_session_stats' }).then((data) => store.set({ stats: data }), () => {});
  }
  return { close: handle.close };
}
