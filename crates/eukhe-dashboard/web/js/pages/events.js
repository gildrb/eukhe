// Events (`#/events[/<seq>]?type=&text=&follow=0`): a live tail of every
// frame this tab sent or received (the core's 2,000-frame ring), with type
// and text filters, pause, and a JSON view of the selected frame. Debug.

import { definePage } from '../pages.js';
import { store } from '../store.js';
import { frame, keyed, place, replaceSoon } from './kit.js';

const SHOWN_ROWS = 300;
const JSON_CAP = 64_000;
const TYPE_CHIPS = 10;

const views = new WeakMap();
const jsonCache = new WeakMap();
const clock = new Intl.DateTimeFormat(navigator.languages && navigator.languages.length ? [...navigator.languages] : undefined, {
  hour: '2-digit',
  minute: '2-digit',
  second: '2-digit',
  fractionalSecondDigits: 3,
  hourCycle: 'h23',
});

/** The name a frame shows under: the event's type for `event` frames, else the frame type or op. */
function kindOf(entry) {
  const data = entry.data || {};
  if (data.type === 'event' && data.event && data.event.type) return data.event.type;
  if (entry.dir === 'out') return data.op === 'run' && data.command ? `run:${data.command.type}` : data.op || entry.type;
  return data.type || entry.type;
}

function jsonOf(entry) {
  let text = jsonCache.get(entry);
  if (text === undefined) {
    try {
      text = JSON.stringify(entry.data);
    } catch {
      text = String(entry.data);
    }
    jsonCache.set(entry, text);
  }
  return text;
}

/** A short hint after the kind: tool name, request id, reply id. */
function hintOf(entry) {
  const data = entry.data || {};
  const event = data.type === 'event' ? data.event || {} : null;
  if (event && event.toolName) return `${event.toolName} ${event.toolCallId || ''}`.trim();
  if (event && event.message && event.message.role) return event.message.role;
  if (data.type === 'reply' || data.type === 'failure' || entry.dir === 'out') return data.id !== undefined ? `#${data.id}` : '';
  if (data.type === 'approval' && data.request) return data.request.command || '';
  return '';
}

function filtersOf(ctx) {
  const raw = ctx.route.params.get('type') || '';
  return {
    types: new Set(raw.split(',').filter(Boolean)),
    text: (ctx.route.params.get('text') || '').trim().toLowerCase(),
    following: ctx.route.params.get('follow') !== '0',
  };
}

function matches(entry, filters) {
  if (filters.types.size && !filters.types.has(kindOf(entry))) return false;
  if (filters.text && !jsonOf(entry).toLowerCase().includes(filters.text)) return false;
  return true;
}

function withParam(ctx, key, value, rest = ctx.route.rest) {
  const params = new URLSearchParams(ctx.route.params);
  if (value) params.set(key, value);
  else params.delete(key);
  return ctx.href('events', { rest, params, aside: ctx.route.aside });
}

function eventRow(ctx, entry, selected) {
  const { ui, fmt } = ctx;
  const params = new URLSearchParams(ctx.route.params);
  return ui.el('li', {},
    ui.el('a', {
      class: 'pg-event mono',
      href: ctx.href('events', { rest: [String(entry.seq)], params, aside: ctx.route.aside }),
      'aria-current': selected ? 'true' : null,
      'data-dir': entry.dir,
      translate: 'no',
    },
    ui.el('span', { class: 'pg-event-at fig', text: clock.format(entry.at) }),
    ui.el('span', { class: 'pg-event-dir', text: entry.dir === 'in' ? '↓' : '↑', 'aria-label': entry.dir === 'in' ? 'received' : 'sent' }),
    ui.el('span', { class: 'pg-event-kind', text: kindOf(entry) }),
    ui.el('span', { class: 'pg-event-hint', text: hintOf(entry) }),
    ui.el('span', { class: 'pg-event-size fig', text: fmt.bytes(jsonOf(entry).length) })));
}

function chips(ctx, view, frames) {
  const { ui } = ctx;
  const counts = new Map();
  for (const entry of frames) {
    const kind = kindOf(entry);
    counts.set(kind, (counts.get(kind) || 0) + 1);
  }
  const { types } = filtersOf(ctx);
  const top = [...counts].sort((a, b) => b[1] - a[1]).slice(0, TYPE_CHIPS).map(([kind]) => kind);
  for (const kind of types) if (!top.includes(kind)) top.push(kind);
  return ui.el('div', { class: 'pg-chips', role: 'group', 'aria-label': 'Show only these types' }, ...top.map((kind) => {
    const on = types.has(kind);
    const next = new Set(types);
    if (on) next.delete(kind);
    else next.add(kind);
    return ui.el('a', {
      class: 'pg-chip mono',
      href: withParam(ctx, 'type', [...next].join(',')),
      'aria-pressed': on ? 'true' : 'false',
      translate: 'no',
      text: `${kind} ${counts.get(kind) || 0}`,
      onClick: (event) => {
        event.preventDefault();
        view.ctx.navigate(withParam(view.ctx, 'type', [...next].join(',')), { replace: true });
      },
    });
  }));
}

function detail(ctx, view, frames) {
  const { ui } = ctx;
  const seq = Number(ctx.route.rest[0]);
  if (!Number.isFinite(seq)) return null;
  const entry = frames.find((candidate) => candidate.seq === seq);
  const back = ui.el('a', { class: 'link target', href: ctx.href('events', { params: ctx.route.params, aside: ctx.route.aside }), text: '← All events' });
  if (!entry) {
    return ui.el('div', { class: 'pg-event-detail' }, back, ui.empty({ title: `Frame ${seq} left the ring.`, body: 'The tab keeps the newest 2,000 frames.' }));
  }
  let text;
  try {
    text = JSON.stringify(entry.data, null, 2);
  } catch {
    text = String(entry.data);
  }
  const all = ctx.route.params.get('all') === '1';
  const cut = !all && text.length > JSON_CAP;
  return ui.el('div', { class: 'pg-event-detail' },
    back,
    ui.el('p', { class: 'pg-line fig' }, `${clock.format(entry.at)} · ${entry.dir === 'in' ? 'received' : 'sent'} · `, ui.el('span', { class: 'mono', translate: 'no', text: kindOf(entry) }), ` · frame ${entry.seq}`),
    ui.el('div', { class: 'pg-actions' },
      ui.copyButton(() => text, 'Copy JSON'),
      cut ? ui.el('a', { class: 'link target', href: withParam(ctx, 'all', '1'), text: `Show all ${ctx.fmt.bytes(text.length)}` }) : null),
    ui.el('pre', { class: 'pg-json mono', translate: 'no', tabindex: '0', text: cut ? `${text.slice(0, JSON_CAP)}\n…` : text }));
}

function rebuild(ctx, view) {
  const { state } = ctx;
  const filters = filtersOf(ctx);
  const frames = state.frames;
  const limit = filters.following ? Infinity : view.pausedAt;
  const shown = [];
  for (let index = frames.length - 1; index >= 0 && shown.length < SHOWN_ROWS; index -= 1) {
    const entry = frames[index];
    if (entry.seq > limit || entry.seq <= view.clearedAt) continue;
    if (matches(entry, filters)) shown.push(entry);
  }
  shown.reverse();
  const selected = Number(ctx.route.rest[0]);
  view.list.replaceChildren(...shown.map((entry) => eventRow(ctx, entry, entry.seq === selected)));
  view.lastSeq = frames.length ? frames[frames.length - 1].seq : 0;
  view.filterKey = `${ctx.route.params.toString()}|${ctx.route.rest.join('/')}|${view.clearedAt}`;
}

/** Append the frames that arrived since the last paint (while following). */
function append(ctx, view) {
  const filters = filtersOf(ctx);
  const frames = ctx.state.frames;
  const fresh = [];
  for (let index = frames.length - 1; index >= 0 && frames[index].seq > view.lastSeq; index -= 1) fresh.push(frames[index]);
  fresh.reverse();
  for (const entry of fresh) if (matches(entry, filters)) view.list.append(eventRow(ctx, entry, false));
  while (view.list.children.length > SHOWN_ROWS) view.list.firstElementChild.remove();
  if (frames.length) view.lastSeq = frames[frames.length - 1].seq;
}

function render(root, ctx) {
  const { ui } = ctx;
  const parts = frame(root, ctx, { title: 'Events', back: ctx.state.session ? { label: 'Chat', href: ctx.href('chat', { sessionId: ctx.state.session.id }) } : null });
  const view = {
    parts,
    ctx,
    cache: new Map(),
    list: ui.el('ol', { class: 'pg-events', 'aria-label': 'Frames, oldest first' }),
    scroller: null,
    lastSeq: 0,
    filterKey: null,
    pausedAt: store.get().framesSeq,
    clearedAt: 0,
    chipsAt: 0,
  };
  views.set(root, view);
  view.text = ui.field({
    label: 'Filter text',
    value: ctx.route.params.get('text') || '',
    type: 'search',
    placeholder: 'call_12, error…',
    name: 'events-text',
    onInput: (value) => replaceSoon(view.ctx, withParam(view.ctx, 'text', value.trim())),
  });
  view.pause = ui.button({ label: 'Pause', onClick: () => {
    const live = view.ctx;
    const following = filtersOf(live).following;
    if (following) view.pausedAt = store.get().framesSeq;
    live.navigate(withParam(live, 'follow', following ? '0' : ''), { replace: true });
  } });
  view.clear = ui.button({ label: 'Clear', onClick: () => {
    view.clearedAt = store.get().framesSeq;
    update(root, { ...view.ctx, state: store.get() });
  } });
  view.status = ui.el('p', { class: 'pg-line small fig', role: 'status' });
  parts.setActions(view.pause);
  update(root, ctx);
}

function update(root, ctx) {
  const view = views.get(root);
  if (!view) return;
  view.ctx = ctx;
  const { state, fmt } = ctx;
  const filters = filtersOf(ctx);
  const filterKey = `${ctx.route.params.toString()}|${ctx.route.rest.join('/')}|${view.clearedAt}`;
  const pinned = !view.scroller || view.scroller.scrollHeight - view.scroller.scrollTop - view.scroller.clientHeight < 32;
  if (view.filterKey !== filterKey) rebuild(ctx, view);
  else if (filters.following && state.framesSeq !== view.lastSeq) append(ctx, view);
  const label = view.pause.querySelector('.btn-label');
  label.textContent = filters.following ? 'Pause' : 'Resume';
  const waiting = filters.following ? 0 : Math.max(0, state.framesSeq - view.pausedAt);
  view.status.textContent = [
    `${fmt.num(state.frames.length)} frames kept`,
    state.framesDropped ? `${fmt.num(state.framesDropped)} older dropped` : null,
    filters.following ? 'following' : `paused${waiting ? ` · ${fmt.num(waiting)} new` : ''}`,
  ].filter(Boolean).join(' · ');
  const second = Math.floor(state.framesSeq / 50);
  const chipsNode = keyed(view.cache, 'chips', [filterKey, second], () => chips(ctx, view, state.frames));
  const detailNode = keyed(view.cache, 'detail', [filterKey], () => detail(ctx, view, state.frames));
  const tools = keyed(view.cache, 'tools', [], () => ctx.ui.el('div', { class: 'pg-filters' }, view.text, ctx.ui.el('div', { class: 'pg-actions' }, view.clear)));
  const listNode = keyed(view.cache, 'list', [], () => ctx.ui.el('div', { class: 'pg-events-frame' }, view.list));
  const split = keyed(view.cache, 'split', [], () => ctx.ui.el('div', { class: 'pg-events-split' }));
  view.scroller = listNode;
  root.dataset.selected = detailNode ? 'true' : 'false';
  place(split, [listNode, detailNode]);
  place(view.parts.body, [view.status, tools, chipsNode, split]);
  if (filters.following && pinned) listNode.scrollTop = listNode.scrollHeight;
}

export default definePage({
  id: 'events',
  title: () => 'Events',
  render,
  update,
  dispose(root) {
    views.delete(root);
  },
});
