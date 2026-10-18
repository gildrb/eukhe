// Memory (`#/s/<id>/memory[/<id>:<count>]`): the chat memory's status
// gauge and its tree (`memory` op → MemoryTreeReply). Phones drill down one
// level per route, so Back walks up; wider screens show an expandable tree
// whose open set lives in `?open=` and whose filter lives in `?q=`. A
// `memory_update` refetches what is shown, keeping it open.

import { definePage } from '../pages.js';
import { store } from '../store.js';
import { announce } from '../ui.js';
import { backToChat, boundSession, frame, gauge, keyed, paneHref, place, replaceSoon, waiting } from './kit.js';

/** `MEMORY_VIEW_CEILING` (eukhe-types/src/daemon/memory.rs): the view's sawtooth ceiling in bytes. */
const VIEW_CEILING = 128_000;
const REFRESH_AFTER_MS = 800;
const KIND_WORDS = { talk: 'eukhe' };
const wide = matchMedia('(min-width: 768px)');
const locales = navigator.languages && navigator.languages.length ? [...navigator.languages] : undefined;
const monthDay = new Intl.DateTimeFormat(locales, { month: 'short', day: 'numeric' });
const monthDayYear = new Intl.DateTimeFormat(locales, { month: 'short', day: 'numeric', year: 'numeric' });

const views = new WeakMap();

function nodeKey(node) {
  return node ? `${node.id}:${node.count}` : 'top';
}

function parseNode(text) {
  if (!text) return null;
  const match = /^(\d+):(\d+)$/.exec(text);
  return match ? { id: Number(match[1]), count: Number(match[2]) } : null;
}

function label(node) {
  return `${node.id}+${node.count}`;
}

function dateSpan(first, last) {
  const start = new Date(first);
  const end = new Date(last);
  if (Number.isNaN(start.getTime())) return '';
  if (Number.isNaN(end.getTime()) || start.toDateString() === end.toDateString()) return monthDay.format(start);
  const format = start.getFullYear() === end.getFullYear() && end.getFullYear() === new Date().getFullYear() ? monthDay : monthDayYear;
  return `${format.format(start)} – ${format.format(end)}`;
}

function kindWords(fmt, kinds) {
  return kinds.map((kind) => `${fmt.num(kind.count)} ${KIND_WORDS[kind.kind] || kind.kind}`).join(' · ');
}

/** Load (or reuse) one level; `fresh` drops the cached copy. */
function level(view, ctx, node, fresh = false) {
  const key = nodeKey(node);
  const cached = view.levels.get(key);
  if (cached && !fresh) return cached;
  const entry = { promise: null, data: cached && fresh ? cached.data : null, error: null, loading: true };
  entry.promise = ctx.request('memory', node ? { node } : {}).then((data) => {
    entry.data = data;
    entry.loading = false;
    if (data && data.tree) view.status = data.tree.status;
    else if (key === 'top') view.status = null;
    view.version += 1;
    view.repaint();
    return data;
  }, (error) => {
    entry.error = error;
    entry.loading = false;
    view.version += 1;
    view.repaint();
    throw error;
  });
  entry.promise.catch(() => {});
  view.levels.set(key, entry);
  return entry;
}

function statusBlock(ctx, view) {
  const { ui, fmt } = ctx;
  const status = view.status;
  if (!status) {
    const top = view.levels.get('top');
    if (top && top.data && !top.data.tree) return null;
    return ui.el('div', { class: 'pg-memory-status' }, ui.el('p', { class: 'pg-line small', text: 'Reading the memory…' }));
  }
  const words = [
    `${fmt.num(status.messages)} messages`,
    `view ${fmt.bytes(status.viewBytes)} of ${fmt.bytes(VIEW_CEILING)}`,
    `${fmt.num(status.lines)} lines`,
    status.unsummarized ? `${fmt.num(status.unsummarized)} unsummarized` : null,
    status.running ? `${fmt.num(status.running)} compacting` : null,
  ].filter(Boolean).join(' · ');
  const node = ui.el('div', { class: 'pg-memory-status' },
    ui.el('p', { class: 'pg-line fig', text: words }),
    gauge(status.viewBytes / VIEW_CEILING, 'Memory view size'));
  if (status.model) node.append(ui.el('p', { class: 'pg-line small' }, 'Compactor ', ui.el('span', { class: 'mono', translate: 'no', text: status.model })));
  if (status.lastError) node.append(ui.el('p', { class: 'pg-line', 'data-kind': 'error' }, ui.el('strong', { text: 'Compactor failed' }), ` · ${status.lastError}`));
  if (view.stale) {
    node.append(ui.el('p', { class: 'pg-line' }, 'Memory changed · ', ui.button({ label: 'Refresh', kind: 'primary', onClick: () => refresh(view) })));
  }
  return node;
}

function summaryText(ui, node) {
  if (node.summary === null || node.summary === undefined) return ui.el('p', { class: 'pg-node-summary', 'data-empty': 'true', text: 'Not summarized yet.' });
  return ui.el('p', { class: 'pg-node-summary', text: node.summary });
}

function messageView(ctx, message) {
  const { ui, fmt } = ctx;
  return ui.el('article', { class: 'pg-memory-message' },
    ui.el('p', { class: 'pg-line fig' }, `message ${fmt.num(message.id)} · ${dateSpan(message.date, message.date)} · ${KIND_WORDS[message.kind] || message.kind}`),
    ui.el('p', { class: 'pg-prose', text: message.text }),
    ui.el('div', { class: 'pg-actions' }, ui.copyButton(() => message.text, 'Copy text')));
}

/** An answered level that is not a list of lines: a message, no line, or no memory. */
function levelState(ctx, data) {
  const { ui } = ctx;
  if (!data || !data.tree) return ui.empty({ title: 'This session keeps no chat memory.' });
  const { level: shown } = data.tree;
  switch (shown.kind) {
    case 'message':
      return messageView(ctx, shown.message);
    case 'no_line':
      return ui.empty({ title: 'Nothing under this line.' });
    case 'lines':
      return shown.nodes.length ? null : ui.empty({ title: 'Nothing under this line.' });
    default:
      return ui.empty({ title: 'This level has an unknown shape.', body: shown.kind });
  }
}

function errorState(ctx, view, node, error) {
  return ctx.ui.empty({
    title: 'The memory did not load.',
    body: error.message,
    action: { label: 'Try again', onClick: () => {
      level(view, ctx, node, true);
      view.repaint();
    } },
  });
}

// ---------- Drill-down (phones) ----------

function drillRow(ctx, node) {
  const { ui, fmt } = ctx;
  return ui.el('li', {},
    ui.el('a', { class: 'pg-node', href: paneHref(ctx, { page: 'memory', rest: [`${node.id}:${node.count}`] }) },
      ui.el('span', { class: 'pg-node-head' },
        ui.el('span', { class: 'pg-node-label fig', text: label(node) }),
        ui.el('span', { class: 'pg-node-dates fig', text: dateSpan(node.firstDate, node.lastDate) })),
      ui.el('span', { class: 'pg-node-kinds fig', text: kindWords(fmt, node.kinds) }),
      summaryText(ui, node),
      ui.el('span', { class: 'pg-node-go', 'aria-hidden': 'true', text: '›' })));
}

function drillBody(ctx, view, node) {
  const { ui } = ctx;
  const entry = level(view, ctx, node);
  if (entry.error && !entry.data) return errorState(ctx, view, node, entry.error);
  if (!entry.data) return ui.skeleton(9);
  const state = levelState(ctx, entry.data);
  if (state) return state;
  return ui.el('ol', { class: 'pg-nodes' }, ...entry.data.tree.level.nodes.map((child) => drillRow(ctx, child)));
}

// ---------- Tree (wider screens) ----------

function openSet(ctx) {
  const raw = ctx.route.params.get('open');
  return new Set(raw ? raw.split(',').filter(Boolean) : []);
}

function withOpen(ctx, open) {
  const params = new URLSearchParams(ctx.route.params);
  if (open.size) params.set('open', [...open].join(','));
  else params.delete('open');
  return paneHref(ctx, { page: 'memory', rest: ctx.route.rest, params });
}

function matches(node, query) {
  if (!query) return true;
  const text = `${label(node)} ${node.summary || ''}`.toLowerCase();
  return text.includes(query);
}

function treeItem(ctx, view, node, depth, open, query, focus) {
  const { ui, fmt } = ctx;
  const key = `${node.id}:${node.count}`;
  const expanded = open.has(key);
  const item = ui.el('li', {
    class: 'pg-treeitem',
    role: 'treeitem',
    'aria-level': String(depth),
    'aria-expanded': expanded ? 'true' : 'false',
    'aria-selected': focus === key ? 'true' : 'false',
    'data-key': key,
    'data-dim': matches(node, query) ? null : 'true',
    tabindex: '-1',
  });
  const toggle = ui.el('button', {
    type: 'button',
    class: 'pg-tree-toggle target',
    tabindex: '-1',
    'aria-label': `${expanded ? 'Close' : 'Open'} ${label(node)}`,
    text: expanded ? '↓' : '→',
    onClick: (event) => {
      event.stopPropagation();
      toggleNode(view, key, { keepFocus: false });
    },
  });
  const focusLink = ui.el('a', {
    class: 'pg-node-label fig',
    tabindex: '-1',
    href: paneHref(ctx, { page: 'memory', rest: [key], params: ctx.route.params }),
    text: label(node),
  });
  item.append(ui.el('div', { class: 'pg-tree-row' },
    toggle,
    ui.el('div', { class: 'pg-tree-main' },
      ui.el('span', { class: 'pg-node-head' }, focusLink, ui.el('span', { class: 'pg-node-dates fig', text: dateSpan(node.firstDate, node.lastDate) })),
      ui.el('span', { class: 'pg-node-kinds fig', text: kindWords(fmt, node.kinds) }),
      summaryText(ui, node))));
  if (expanded) {
    const entry = level(view, ctx, { id: node.id, count: node.count });
    const group = ui.el('ul', { class: 'pg-tree-group', role: 'group' });
    if (entry.error && !entry.data) group.append(ui.el('li', { role: 'none' }, errorState(ctx, view, { id: node.id, count: node.count }, entry.error)));
    else if (!entry.data) group.append(ui.el('li', { role: 'none', class: 'pg-line small', text: 'Loading…' }));
    else {
      const state = levelState(ctx, entry.data);
      if (state) group.append(ui.el('li', { role: 'none' }, state));
      else for (const child of entry.data.tree.level.nodes) group.append(treeItem(ctx, view, child, depth + 1, open, query, focus));
    }
    item.append(group);
  }
  return item;
}

/** Open or close one tree node (`?open=` via replaceState); `keepFocus` refocuses it after the rebuild. */
function toggleNode(view, key, { keepFocus }) {
  const live = view.ctx;
  const open = openSet(live);
  if (open.has(key)) open.delete(key);
  else open.add(key);
  view.focusKey = keepFocus ? key : null;
  live.navigate(withOpen(live, open), { replace: true });
}

function treeKeys(event, tree, view) {
  const ctx = view.ctx;
  const items = [...tree.querySelectorAll('[role="treeitem"]')].filter((item) => item.offsetParent !== null);
  const current = document.activeElement && document.activeElement.closest('[role="treeitem"]');
  const index = items.indexOf(current);
  const focusAt = (next) => {
    if (next < 0 || next >= items.length) return;
    for (const item of items) item.tabIndex = -1;
    items[next].tabIndex = 0;
    items[next].focus();
  };
  const key = current ? current.dataset.key : null;
  switch (event.key) {
    case 'ArrowDown':
      focusAt(index + 1);
      break;
    case 'ArrowUp':
      focusAt(index - 1);
      break;
    case 'Home':
      focusAt(0);
      break;
    case 'End':
      focusAt(items.length - 1);
      break;
    case 'ArrowRight':
      if (current && current.getAttribute('aria-expanded') === 'false') toggleNode(view, key, { keepFocus: true });
      else focusAt(index + 1);
      break;
    case 'ArrowLeft':
      if (current && current.getAttribute('aria-expanded') === 'true') toggleNode(view, key, { keepFocus: true });
      else if (current) {
        const parent = current.parentElement.closest('[role="treeitem"]');
        if (parent) focusAt(items.indexOf(parent));
      }
      break;
    case 'Enter':
      if (key) ctx.navigate(paneHref(ctx, { page: 'memory', rest: [key], params: ctx.route.params }));
      break;
    default:
      return;
  }
  event.preventDefault();
}

function treeBody(ctx, view) {
  const { ui } = ctx;
  const entry = level(view, ctx, null);
  if (entry.error && !entry.data) return errorState(ctx, view, null, entry.error);
  if (!entry.data) return ui.skeleton(9);
  const state = levelState(ctx, entry.data);
  if (state) return state;
  const open = openSet(ctx);
  const query = (ctx.route.params.get('q') || '').trim().toLowerCase();
  const focus = ctx.route.rest[0] || null;
  const tree = ui.el('ul', { class: 'pg-memory-tree', role: 'tree', 'aria-label': 'Chat memory' });
  for (const node of entry.data.tree.level.nodes) tree.append(treeItem(ctx, view, node, 1, open, query, focus));
  const first = tree.querySelector(focus ? `[data-key="${CSS.escape(focus)}"]` : '[role="treeitem"]');
  if (first) first.tabIndex = 0;
  tree.addEventListener('keydown', (event) => treeKeys(event, tree, view));
  if (view.focusKey) {
    const target = tree.querySelector(`[data-key="${CSS.escape(view.focusKey)}"]`);
    view.focusKey = null;
    if (target) {
      if (first) first.tabIndex = -1;
      target.tabIndex = 0;
      requestAnimationFrame(() => target.focus());
    }
  }
  const focusNode = focus ? parseNode(focus) : null;
  const nodes = [tree];
  if (focusNode) {
    const focused = level(view, ctx, focusNode);
    if (focused.data && focused.data.tree && focused.data.tree.level.kind === 'message') {
      nodes.unshift(ui.section(`Message ${label(focusNode)}`, messageView(ctx, focused.data.tree.level.message)));
    }
  }
  return ui.el('div', { class: 'pg-stack' }, ...nodes);
}

function filterField(ctx, view) {
  return ctx.ui.field({
    label: 'Filter loaded lines',
    value: ctx.route.params.get('q') || '',
    type: 'search',
    placeholder: 'Words in summaries…',
    onInput: (value) => {
      const live = view.ctx;
      const params = new URLSearchParams(live.route.params);
      if (value.trim()) params.set('q', value);
      else params.delete('q');
      replaceSoon(live, paneHref(live, { page: 'memory', rest: live.route.rest, params }));
    },
  });
}

// ---------- Live refresh ----------

/** Refetch every level on screen, keeping what is open. */
function refresh(view) {
  const ctx = view.ctx;
  view.stale = false;
  const visible = new Set(['top']);
  if (ctx.route.rest[0]) visible.add(ctx.route.rest[0]);
  if (wide.matches) for (const key of openSet(ctx)) visible.add(key);
  const loads = [];
  for (const key of [...view.levels.keys()]) {
    if (!visible.has(key)) {
      view.levels.delete(key);
      continue;
    }
    loads.push(level(view, ctx, parseNode(key), true).promise);
  }
  view.version += 1;
  view.repaint();
  Promise.allSettled(loads).then((results) => {
    if (results.some((result) => result.status === 'rejected')) {
      view.stale = true;
      view.version += 1;
      view.repaint();
    } else if (loads.length) {
      announce('Memory updated');
    }
  });
}

function onMemoryUpdate(view, session) {
  const last = session.memory.last;
  if (last && view.status) {
    const viewBytes = last.kind === 'merged' ? last.afterBytes : last.viewBytes;
    if (Number.isFinite(viewBytes)) view.status = { ...view.status, viewBytes };
  }
  clearTimeout(view.refreshTimer);
  view.refreshTimer = setTimeout(() => {
    if (document.hidden) {
      view.stale = true;
      view.version += 1;
      view.repaint();
      return;
    }
    refresh(view);
  }, REFRESH_AFTER_MS);
}

// ---------- Page ----------

function render(root, ctx) {
  const parts = frame(root, ctx, { title: 'Memory', back: backToChat(ctx) });
  const view = {
    parts,
    ctx,
    cache: new Map(),
    levels: new Map(),
    status: null,
    stale: false,
    version: 0,
    boundTo: null,
    stamp: null,
    refreshTimer: 0,
  };
  view.repaint = () => update(root, { ...view.ctx, state: store.get() });
  view.onWide = () => view.repaint();
  wide.addEventListener('change', view.onWide);
  views.set(root, view);
  update(root, ctx);
}

function update(root, ctx) {
  const view = views.get(root);
  if (!view) return;
  view.ctx = ctx;
  const { ui } = ctx;
  const session = boundSession(ctx);
  if (!session) {
    place(view.parts.body, [waiting(ctx, view.cache, 9)]);
    return;
  }
  if (view.boundTo !== session.id) {
    view.boundTo = session.id;
    view.levels.clear();
    view.status = null;
    view.stamp = session.memory.stamp;
  } else if (view.stamp !== session.memory.stamp) {
    view.stamp = session.memory.stamp;
    onMemoryUpdate(view, session);
  }
  const focus = parseNode(ctx.route.rest[0]);
  const isTree = wide.matches;
  view.parts.setTitle(focus ? `Memory · ${label(focus)}` : 'Memory');
  const back = focus && !isTree
    ? { label: 'Up', href: paneHref(ctx, { page: 'memory' }) }
    : null;
  const backLink = view.parts.foot.querySelector('.pg-back');
  if (backLink) {
    backLink.textContent = back ? `← ${back.label}` : '← Chat';
    backLink.href = back ? back.href : backToChat(ctx).href;
  }
  const routeKey = `${ctx.route.rest.join('/')}?${ctx.route.params.toString()}`;
  const statusNode = keyed(view.cache, 'status', [view.status, view.stale, view.version], () => statusBlock(ctx, view));
  const bodyNode = keyed(view.cache, 'body', [view.version, routeKey, isTree], () => (isTree ? treeBody(ctx, view) : drillBody(ctx, view, focus)));
  const filterNode = isTree ? keyed(view.cache, 'filter', [], () => filterField(ctx, view)) : null;
  const crumbs = focus && !isTree
    ? keyed(view.cache, 'crumbs', [routeKey], () => ui.el('nav', { class: 'pg-crumbs', 'aria-label': 'Memory path' },
      ui.el('a', { class: 'link target', href: paneHref(ctx, { page: 'memory' }), text: 'Memory' }),
      ui.el('span', { class: 'pg-crumb-sep', 'aria-hidden': 'true', text: '→' }),
      ui.el('span', { 'aria-current': 'page', text: label(focus) })))
    : null;
  place(view.parts.body, [statusNode, crumbs, filterNode, bodyNode]);
}

export default definePage({
  id: 'memory',
  title(ctx) {
    const focus = parseNode(ctx.route.rest[0]);
    return focus ? `Memory · ${label(focus)}` : 'Memory';
  },
  render,
  update,
  dispose(root) {
    const view = views.get(root);
    if (view) {
      clearTimeout(view.refreshTimer);
      wide.removeEventListener('change', view.onWide);
    }
    views.delete(root);
  },
});
