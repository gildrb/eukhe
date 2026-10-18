// Sessions (`#/sessions?q=`): every saved root session, the ones that need
// you first, then running, then recent; search; per-row rename, fork,
// export, delete (confirm + Undo); a new session in a chosen folder.

import { definePage } from '../pages.js';
import { store } from '../store.js';
import { refreshSessions } from '../sessions.js';
import { derivePhase } from '../turn.js';
import { failed, frame, keyed, place, replaceSoon } from './kit.js';
import { bindRow, deleteSession, exportSession, forkSheet, newSessionSheet, renameSheet } from './session-sheet.js';

const views = new WeakMap();

function basename(path) {
  const parts = String(path || '').split('/').filter(Boolean);
  return parts.length ? parts[parts.length - 1] : '/';
}

/** Split rows into Needs you / Running / Recent; only the bound session has live status. */
function groups(state, rows, now, fmt) {
  const needs = [];
  const running = [];
  const recent = [];
  const bound = state.session;
  for (const row of rows) {
    if (bound && bound.id === row.id) {
      const phase = derivePhase(state, now, fmt);
      const entry = { row, status: [phase.label, phase.detail].filter(Boolean).join(' · '), live: true };
      if (phase.urgent) needs.push(entry);
      else if (bound.turn.running) running.push(entry);
      else recent.push(entry);
    } else {
      recent.push({ row, status: `Idle · ${fmt.relative(row.modified, now)}`, live: false });
    }
  }
  return { needs, running, recent };
}

function rowActions(ctx, row) {
  const { ui } = ctx;
  let handle = null;
  const run = (work) => async () => {
    handle.close();
    try {
      await work();
    } catch (error) {
      failed(error);
    }
  };
  const item = (label, onClick, kind = 'plain') => ui.button({ label, kind, onClick });
  handle = ui.sheet({
    title: row.title || 'Session',
    content: ui.el('div', { class: 'pg-menu' },
      ui.el('a', { class: 'row', href: ctx.href('chat', { sessionId: row.id }), onClick: () => handle.close() },
        ui.el('span', { class: 'row-body' }, ui.el('span', { class: 'row-title', text: 'Open' }))),
      item('Rename…', run(() => renameSheet(ctx, row))),
      item('Fork…', run(async () => {
        await bindRow(ctx, row);
        await forkSheet(ctx);
      })),
      item('Export HTML', run(async () => {
        await bindRow(ctx, row);
        await exportSession(ctx, 'html');
      })),
      item('Export JSONL', run(async () => {
        await bindRow(ctx, row);
        await exportSession(ctx, 'jsonl');
      })),
      item('Delete…', run(() => deleteSession(ctx, row)), 'danger'),
      ui.el('p', { class: 'pg-line small mono', translate: 'no', text: row.cwd || '' })),
  });
}

function sessionRow(ctx, entry) {
  const { ui } = ctx;
  const { row } = entry;
  const title = row.title || 'Untitled session';
  return ui.el('li', { class: 'pg-session', 'data-live': entry.live ? 'true' : null },
    ui.el('a', { class: 'pg-session-link', href: ctx.href('chat', { sessionId: row.id }), 'aria-current': ctx.state.session && ctx.state.session.id === row.id ? 'true' : null },
      ui.el('span', { class: 'pg-session-title', title, text: title }),
      ui.el('span', { class: 'pg-session-status', text: entry.status }),
      ui.el('span', { class: 'pg-session-where mono', translate: 'no', text: basename(row.cwd) })),
    ui.button({ label: `Actions for ${title}`, icon: '⋯', onClick: () => rowActions(ctx, row) }));
}

function listKeys(event) {
  if (event.key !== 'ArrowDown' && event.key !== 'ArrowUp') return;
  const links = [...event.currentTarget.querySelectorAll('.pg-session-link')];
  const index = links.indexOf(document.activeElement);
  if (index < 0) return;
  const next = links[index + (event.key === 'ArrowDown' ? 1 : -1)];
  if (!next) return;
  event.preventDefault();
  next.focus();
}

function listing(ctx, state, query) {
  const { ui, fmt } = ctx;
  const { rows, loading, error } = state.sessions;
  if (!rows.length && error) {
    return ui.empty({ title: 'Sessions did not load.', body: error, action: { label: 'Try again', onClick: () => refreshSessions().catch(() => {}) } });
  }
  if (!rows.length && (loading || !state.sessions.at)) return ui.skeleton(10);
  if (!rows.length) {
    return ui.empty({ title: 'No sessions yet.', action: { label: 'Start one', onClick: () => newSessionSheet(ctx, '') } });
  }
  const needle = query.trim().toLowerCase();
  const shown = needle
    ? rows.filter((row) => `${row.title || ''} ${row.cwd || ''} ${row.id}`.toLowerCase().includes(needle))
    : rows;
  if (!shown.length) {
    return ui.empty({
      title: `No sessions match “${query.trim()}”.`,
      body: 'Search looks at titles and folders.',
      action: { label: 'Clear search', href: ctx.href('sessions') },
    });
  }
  const { needs, running, recent } = groups(state, shown, Date.now(), fmt);
  const block = (title, entries) => (entries.length
    ? ui.section(title, ui.el('ol', { class: 'pg-sessions', onKeydown: listKeys }, ...entries.map((entry) => sessionRow(ctx, entry))))
    : null);
  return ui.el('div', { class: 'pg-stack' },
    block('Needs you', needs),
    block('Running', running),
    block('Recent', recent));
}

function render(root, ctx) {
  const { ui } = ctx;
  const parts = frame(root, ctx, { title: 'Sessions', back: ctx.state.session ? { label: 'Chat', href: ctx.href('chat', { sessionId: ctx.state.session.id }) } : null });
  const view = { parts, cache: new Map(), ctx };
  views.set(root, view);
  view.search = ui.field({
    label: 'Search sessions',
    value: ctx.route.params.get('q') || '',
    type: 'search',
    placeholder: 'Search sessions…',
    name: 'session-search',
    onInput: (value) => {
      const live = view.ctx;
      replaceSoon(live, live.href('sessions', { params: value.trim() ? { q: value } : null, aside: live.route.aside }));
    },
  });
  view.search.classList.add('pg-search');
  parts.setActions(ui.button({ label: 'New session', kind: 'primary', onClick: () => {
    const { session } = store.get();
    newSessionSheet(view.ctx, session ? session.state.cwd : '');
  } }));
  refreshSessions().catch(() => {});
  update(root, ctx);
}

function update(root, ctx) {
  const view = views.get(root);
  if (!view) return;
  view.ctx = ctx;
  const { state, fmt } = ctx;
  const query = ctx.route.params.get('q') || '';
  const input = view.search.querySelector('input');
  if (input && document.activeElement !== input && input.value !== query) input.value = query;
  const { rows } = state.sessions;
  view.parts.setTitle(rows.length ? `Sessions · ${fmt.num(rows.length)}` : 'Sessions');
  const bound = state.session;
  const phase = bound ? derivePhase(state, Date.now(), fmt) : null;
  const liveKey = bound ? `${bound.id}|${phase.label}|${phase.detail}|${bound.turn.running}|${bound.title}` : '';
  const listNode = keyed(view.cache, 'list', [state.sessions, query, liveKey], () => listing(ctx, state, query));
  place(view.parts.body, [listNode, view.search]);
}

export default definePage({
  id: 'sessions',
  title: () => 'Sessions',
  render,
  update,
  dispose(root) {
    views.delete(root);
  },
});
