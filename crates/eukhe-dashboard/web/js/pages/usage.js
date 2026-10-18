// Usage (`#/s/<id>/usage`): this session's totals (GetSessionStats:
// tokens in/out/cache, cost, messages, context) and every model call with
// its tokens, cost, first-token time and decode speed (message `usage` and
// `timing`).

import { definePage } from '../pages.js';
import { store } from '../store.js';
import { messageSpeed } from '../turn.js';
import { backToChat, boundSession, contextMeter, frame, keyed, modelName, paneHref, place, stats, waiting } from './kit.js';

const SHOWN_CALLS = 100;

const views = new WeakMap();

function fetchStats(ctx, view) {
  view.statsPromise = ctx.run({ type: 'get_session_stats' }).then((data) => {
    store.set({ stats: data });
    return data;
  });
  return view.statsPromise;
}

function totals(ctx, data, contextUsage) {
  const { ui, fmt } = ctx;
  const { tokens } = data;
  const cachedShare = tokens.input + tokens.cacheRead > 0 ? tokens.cacheRead / (tokens.input + tokens.cacheRead + tokens.cacheWrite) : null;
  return ui.el('div', { class: 'pg-stack' },
    stats([
      ['Cost', fmt.cost(data.cost)],
      ['Input', fmt.tokens(tokens.input)],
      ['Output', fmt.tokens(tokens.output)],
      ['Cache read', fmt.tokens(tokens.cacheRead)],
      ['Cache write', fmt.tokens(tokens.cacheWrite)],
      ['Cached share', cachedShare === null ? null : fmt.percent(cachedShare)],
      ['All tokens', fmt.tokens(tokens.total)],
    ]),
    stats([
      ['Messages', fmt.num(data.totalMessages)],
      ['From you', fmt.num(data.userMessages)],
      ['From eukhe', fmt.num(data.assistantMessages)],
      ['Tool calls', fmt.num(data.toolCalls)],
    ]),
    ui.el('h3', { class: 'pg-subtitle', text: 'Context' }),
    contextMeter(data.contextUsage || contextUsage));
}

function calls(messages) {
  const found = [];
  for (const message of messages) {
    if (message.role !== 'assistant' || !message.usage) continue;
    found.push({ message, speed: messageSpeed(message) });
  }
  return found.reverse();
}

function median(values) {
  if (!values.length) return null;
  const sorted = [...values].sort((a, b) => a - b);
  const middle = Math.floor(sorted.length / 2);
  return sorted.length % 2 ? sorted[middle] : (sorted[middle - 1] + sorted[middle]) / 2;
}

function callsTable(ctx, list, showAll) {
  const { ui, fmt } = ctx;
  const shown = showAll ? list : list.slice(0, SHOWN_CALLS);
  const head = ui.el('thead', {}, ui.el('tr', {},
    ...['Time', 'Model', 'In', 'Out', 'Cache', 'First token', 'Speed', 'Cost'].map((label) => ui.el('th', { scope: 'col', text: label }))));
  const body = ui.el('tbody');
  for (const { message, speed } of shown) {
    const usage = message.usage;
    const cell = (label, text, extra = {}) => ui.el('td', { 'data-label': label, ...extra, text });
    body.append(ui.el('tr', { 'data-stop': message.stopReason },
      cell('Time', fmt.time(message.timestamp), { class: 'fig' }),
      cell('Model', message.responseModel || message.model || '—', { class: 'mono', translate: 'no' }),
      cell('In', fmt.tokens(usage.input, { unit: false }), { class: 'fig' }),
      cell('Out', fmt.tokens(usage.output, { unit: false }), { class: 'fig' }),
      cell('Cache', fmt.tokens(usage.cacheRead, { unit: false }), { class: 'fig' }),
      cell('First token', speed && Number.isFinite(speed.ttftMs) ? fmt.duration(speed.ttftMs) : '—', { class: 'fig' }),
      cell('Speed', speed && speed.rate ? fmt.rate(speed.rate) : '—', { class: 'fig' }),
      cell('Cost', usage.cost ? fmt.cost(usage.cost.total) : '—', { class: 'fig' })));
  }
  const table = ui.el('table', { class: 'pg-table' }, ui.el('caption', { class: 'sr-only', text: 'Model calls, newest first' }), head, body);
  const nodes = [ui.el('div', { class: 'pg-table-frame' }, table)];
  if (!showAll && list.length > SHOWN_CALLS) {
    const params = new URLSearchParams(ctx.route.params);
    params.set('all', '1');
    nodes.push(ui.el('a', { class: 'link target', href: paneHref(ctx, { page: 'usage', params }), text: `Show all ${fmt.num(list.length)} calls` }));
  }
  return nodes;
}

function render(root, ctx) {
  const parts = frame(root, ctx, { title: 'Usage', back: backToChat(ctx) });
  const view = { parts, cache: new Map(), statsPromise: null, boundTo: null, wasRunning: false };
  views.set(root, view);
  parts.setActions(ctx.ui.button({ label: 'Refresh', onClick: () => {
    fetchStats(view.ctx, view);
    update(root, { ...view.ctx, state: store.get() });
  } }));
  update(root, ctx);
}

function update(root, ctx) {
  const view = views.get(root);
  if (!view) return;
  view.ctx = ctx;
  const { ui, fmt } = ctx;
  const session = boundSession(ctx);
  if (!session) {
    place(view.parts.body, [waiting(ctx, view.cache, 10)]);
    return;
  }
  if (view.boundTo !== session.id || (view.wasRunning && !session.turn.running)) {
    view.boundTo = session.id;
    fetchStats(ctx, view);
  }
  view.wasRunning = session.turn.running;
  const totalsNode = keyed(view.cache, 'totals', [view.statsPromise], () => ui.section('This session',
    ui.delayed(view.statsPromise, (data) => totals(ctx, data, session.state.contextUsage), {
      lines: 8,
      retry: () => fetchStats(ctx, view),
    })));
  const showAll = ctx.route.params.get('all') === '1';
  const callsNode = keyed(view.cache, 'calls', [session.messages, showAll], () => {
    const list = calls(session.messages);
    if (!list.length) {
      return ui.section('Model calls', ui.empty({ title: 'No model calls yet.', body: 'Each reply’s tokens, cost and speed show here.' }));
    }
    const ttfts = list.map(({ speed }) => speed && speed.ttftMs).filter(Number.isFinite);
    const rates = list.map(({ speed }) => speed && speed.rate).filter(Number.isFinite);
    const summary = stats([
      ['Calls', fmt.num(list.length)],
      ['Median first token', ttfts.length ? fmt.duration(median(ttfts)) : null],
      ['Median speed', rates.length ? fmt.rate(median(rates)) : null],
      ['Model', modelName(session.state.model)],
    ]);
    return ui.section('Model calls', summary, ...callsTable(ctx, list, showAll));
  });
  place(view.parts.body, [totalsNode, callsNode]);
}

export default definePage({
  id: 'usage',
  title: () => 'Usage',
  render,
  update,
  dispose(root) {
    views.delete(root);
  },
});
