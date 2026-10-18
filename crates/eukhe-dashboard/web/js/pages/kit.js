// Shared parts of the secondary pages: in-pane links, the page frame
// (heading on top, thumb bar at the bottom on phones), tool rows and
// gauges.

import { current, href } from '../router.js';
import { store } from '../store.js';
import { el, button, toast, empty, skeleton } from '../ui.js';
import { bind } from '../binding.js';
import { fmt } from '../format.js';
import { contentText, toolTarget } from '../turn.js';

let navigatedInApp = false;
window.addEventListener('hashchange', () => {
  navigatedInApp = true;
});

/**
 * The hash for `page` in the pane the page renders in: the aside keeps the
 * main route and swaps its own part; the main pane keeps the aside.
 */
export function paneHref(ctx, { page = ctx.route.page, rest = [], params = null } = {}) {
  const now = current();
  if (ctx.pane === 'aside') {
    return href(now.page, {
      sessionId: now.sessionId,
      rest: now.rest,
      params: now.params,
      aside: { page, rest, params },
    });
  }
  return href(page, { sessionId: ctx.route.sessionId, rest, params, aside: now.aside });
}

/** The bound session when it is the one the route names, else null. */
export function boundSession(ctx) {
  const { session } = ctx.state;
  if (!session) return null;
  if (ctx.route.sessionId && session.id !== ctx.route.sessionId) return null;
  return session;
}

/**
 * What a session page shows until its session is bound: a skeleton, or
 * the open failure (`state.opening.error`) with Try again.
 */
export function waiting(ctx, cache, lines) {
  const { opening } = ctx.state;
  const failure = opening && opening.error && (!opening.id || opening.id === ctx.route.sessionId) ? opening.error : null;
  return keyed(cache, 'waiting', [failure, lines], () => (failure
    ? empty({
      title: 'This session did not open.',
      body: typeof failure === 'string' ? failure : failure.message || String(failure),
      action: { label: 'Try again', onClick: () => bind(ctx.route.sessionId, { force: true }).catch(() => {}) },
    })
    : skeleton(lines)));
}

/** Resolves once the tab is bound to session `id` with an open link. */
export function whenBound(id, timeoutMs = 20_000) {
  return new Promise((resolve, reject) => {
    const check = (state) => state.session && state.session.id === id && state.link.status === 'open';
    if (check(store.get())) {
      resolve(store.get().session);
      return;
    }
    const timer = setTimeout(() => {
      stop();
      reject(new Error('The session did not open in time.'));
    }, timeoutMs);
    const stop = store.subscribe((state) => {
      if (!check(state)) return;
      clearTimeout(timer);
      stop();
      resolve(state.session);
    });
  });
}

/**
 * Re-read the bound session's AgentConnectionState (`get_connection_state`)
 * after a switch command: model, thinking level and modes carry no event.
 */
export async function reloadState(ctx) {
  const id = store.get().session ? store.get().session.id : null;
  const fresh = await ctx.run({ type: 'get_connection_state' });
  store.set((state) => (state.session && state.session.id === id ? { session: { ...state.session, state: { ...state.session.state, ...fresh } } } : null));
  return fresh;
}

/**
 * A row of text buttons, one per option, the current one pressed (gildrb:
 * state is a gray level plus `aria-pressed`). `onPick(value)` may return a
 * promise; the picked label shows `…` until it settles.
 */
export function segmented({ label, options, value, onPick }) {
  const group = el('div', { class: 'pg-segmented', role: 'group', 'aria-label': label });
  for (const option of options) {
    const spec = typeof option === 'string' ? { value: option, label: option } : option;
    const node = button({ label: spec.label, current: spec.value === value, onClick: async () => {
      if (spec.value === value) return;
      const text = node.querySelector('.btn-label');
      node.setAttribute('aria-busy', 'true');
      text.textContent = `${spec.label}…`;
      try {
        await onPick(spec.value);
      } catch (error) {
        failed(error);
      } finally {
        node.removeAttribute('aria-busy');
        text.textContent = spec.label;
      }
    } });
    group.append(node);
  }
  return el('div', { class: 'pg-field' }, el('span', { class: 'pg-field-label', text: label }), group);
}

/**
 * The page frame: an `<h1>` header (with Open in main / Close in the
 * aside), the body, and a bar with Back, the title and the page's actions:
 * pinned to the bottom on phones (thumb reach), a toolbar under the
 * heading on wider panes. `setTitle` and `setActions` repaint them.
 */
export function frame(root, ctx, { title, back = null }) {
  const heading = el('h1', { class: 'pg-title', tabindex: '-1', text: title });
  const tools = el('div', { class: 'pg-head-actions' });
  const head = el('header', { class: 'pg-head' }, heading, tools);
  if (ctx.pane === 'aside') {
    const now = current();
    const own = now.aside || { page: ctx.route.page, rest: [], params: null };
    tools.append(el('a', {
      class: 'link target',
      href: href(own.page, { sessionId: now.sessionId, rest: own.rest, params: own.params }),
      text: 'Open in main',
    }));
  }
  const body = el('div', { class: 'pg-body' });
  const actions = el('div', { class: 'pg-foot-actions' });
  const footTitle = el('span', { class: 'pg-foot-title', text: title });
  const foot = el('nav', { class: 'pg-foot', 'aria-label': 'Page' });
  if (back) {
    const link = el('a', { class: 'link target pg-back', href: back.href, text: `← ${back.label}` });
    link.addEventListener('click', (event) => {
      if (!navigatedInApp || event.metaKey || event.ctrlKey || event.shiftKey || event.button !== 0) return;
      event.preventDefault();
      history.back();
    });
    foot.append(link);
  } else {
    foot.append(el('span'));
  }
  foot.append(footTitle, actions);
  root.classList.add('pg', ctx.pane === 'aside' ? 'pg-in-aside' : 'pg-in-main');
  root.replaceChildren(head, body, foot);
  return {
    head,
    body,
    foot,
    setTitle(text) {
      if (heading.textContent !== text) heading.textContent = text;
      if (footTitle.textContent !== text) footTitle.textContent = text;
    },
    setActions(...nodes) {
      actions.replaceChildren(...nodes.filter(Boolean));
      foot.dataset.actions = nodes.some(Boolean) ? 'true' : 'false';
    },
  };
}

/** The Back target of a session page: its chat. */
export function backToChat(ctx) {
  return { label: 'Chat', href: href('chat', { sessionId: ctx.route.sessionId }) };
}

/** `{label, value}` pairs as a `<dl>`; a missing value reads `—`, never 0. */
export function stats(pairs) {
  const list = el('dl', { class: 'pg-stats' });
  for (const [label, value] of pairs) {
    if (label === null) continue;
    list.append(
      el('div', { class: 'pg-stat' },
        el('dt', { text: label }),
        el('dd', { class: 'fig', text: value === null || value === undefined || value === '' ? '—' : value })),
    );
  }
  return list;
}

/** A hairline meter with a primary fill (`fraction` 0..1). */
export function gauge(fraction, label) {
  const clamped = Number.isFinite(fraction) ? Math.min(1, Math.max(0, fraction)) : 0;
  const fill = el('span', { class: 'pg-gauge-fill' });
  fill.style.transform = `scaleX(${clamped})`;
  return el('div', {
    class: 'pg-gauge',
    role: 'meter',
    'aria-label': label,
    'aria-valuemin': '0',
    'aria-valuemax': '100',
    'aria-valuenow': String(Math.round(clamped * 100)),
  }, fill);
}

/** `{tokens, contextWindow, percent}` as `76k of 200k · 38%` plus a gauge. */
export function contextMeter(usage) {
  if (!usage || !Number.isFinite(usage.contextWindow) || usage.contextWindow <= 0) {
    return el('p', { class: 'pg-line small', text: 'Context size unknown for this model.' });
  }
  const fraction = Number.isFinite(usage.percent) ? usage.percent / 100 : usage.tokens / usage.contextWindow;
  const words = `${fmt.tokens(usage.tokens, { unit: false })} of ${fmt.tokens(usage.contextWindow)} · ${fmt.percent(fraction)}${fraction >= 0.8 ? ' · High' : ''}`;
  return el('div', { class: 'pg-meter' }, el('p', { class: 'pg-line fig', text: words }), gauge(fraction, 'Context used'));
}

/** The text of a ToolOutput (`{content, details}`). */
export function outputText(output) {
  return output ? contentText(output.content) : '';
}

/** Status word plus figure: `running 0:42`, `12 s`, `failed`. */
export function toolStatus(tool, now = Date.now()) {
  switch (tool.status) {
    case 'running':
      return `running ${Number.isFinite(tool.startedAt) ? fmt.duration(now - tool.startedAt) : ''}`.trim();
    case 'failed':
      return Number.isFinite(tool.durationMs) ? `failed · ${fmt.duration(tool.durationMs)}` : 'failed';
    case 'done':
      return Number.isFinite(tool.durationMs) ? fmt.duration(tool.durationMs) : 'done';
    case 'stopped':
      return 'stopped';
    default:
      return tool.status || '';
  }
}

const settledCache = new WeakMap();
const knownCache = new WeakMap();

/** Tool calls of the settled transcript: `toolCall` blocks matched with `toolResult` messages. */
function settledTools(messages) {
  const cached = settledCache.get(messages);
  if (cached) return cached;
  const tools = new Map();
  for (const message of messages) {
    if (message.role === 'assistant' && Array.isArray(message.content)) {
      for (const block of message.content) {
        if (block.type !== 'toolCall') continue;
        tools.set(block.id, {
          id: block.id,
          name: block.name,
          args: block.arguments,
          status: message.stopReason === 'aborted' ? 'stopped' : 'done',
          partial: null,
          result: null,
          isError: false,
          startedAt: message.timestamp,
          endedAt: 0,
          durationMs: null,
        });
      }
    } else if (message.role === 'toolResult') {
      const known = tools.get(message.toolCallId) || {
        id: message.toolCallId,
        name: message.toolName,
        args: null,
        partial: null,
        startedAt: 0,
      };
      tools.set(message.toolCallId, {
        ...known,
        status: message.isError ? 'failed' : 'done',
        result: { content: message.content, details: message.details === undefined ? null : message.details },
        isError: message.isError,
        endedAt: message.timestamp,
        durationMs: Number.isFinite(message.durationMs) ? message.durationMs : null,
      });
    }
  }
  settledCache.set(messages, tools);
  return tools;
}

/**
 * Every tool call the session knows, by call id: the settled transcript's,
 * then the live records (`session.tools`) on top. Cached per transcript
 * and live-record identity, so page updates stay cheap.
 */
export function knownTools(session) {
  const messages = session.messages || [];
  const live = session.tools || {};
  const cached = knownCache.get(live);
  if (cached && cached.messages === messages) return cached.tools;
  const tools = new Map(settledTools(messages));
  for (const [id, record] of Object.entries(live)) {
    const known = tools.get(id) || {};
    const durationMs = record.endedAt > 0 && record.startedAt > 0 ? record.endedAt - record.startedAt : known.durationMs;
    tools.set(id, {
      ...known,
      ...record,
      args: record.args === undefined || record.args === null ? known.args : record.args,
      result: record.result || known.result || null,
      durationMs: Number.isFinite(durationMs) ? durationMs : null,
    });
  }
  knownCache.set(live, { messages, tools });
  return tools;
}

/**
 * One tool call as a mono row linking to its Tool page; a running call
 * shows its last three output lines beneath.
 */
export function toolRow(ctx, tool, now = Date.now()) {
  const node = el('a', {
    class: 'pg-tool',
    href: paneHref(ctx, { page: 'tool', rest: [tool.id] }),
    'data-status': tool.status,
  },
  el('span', { class: 'pg-tool-name mono', translate: 'no', text: tool.name || 'tool' }),
  el('span', { class: 'pg-tool-target mono', translate: 'no', text: toolTarget(tool.args) }),
  el('span', { class: 'pg-tool-status fig', text: toolStatus(tool, now) }));
  if (tool.status === 'running') {
    const tail = outputText(tool.partial).replace(/\s+$/, '').split('\n').slice(-3).join('\n');
    if (tail) node.append(el('pre', { class: 'pg-tool-tail mono', translate: 'no', text: tail }));
  }
  return node;
}

/** The model's display name from a Model object or `{id, provider}`. */
export function modelName(model) {
  if (!model) return '—';
  if (typeof model === 'string') return model;
  return model.name || model.id || model.modelId || '—';
}

/** Report a failed action where the user is looking. */
export function failed(error, what = 'That did not work') {
  toast({ text: `${what}: ${error && error.message ? error.message : String(error)}`, error: true });
}

/** A button that runs `work` and shows `busy` with an ellipsis meanwhile. */
export function actionButton({ label, busyLabel = label, kind = 'plain', work, onError = (error) => failed(error) }) {
  const node = button({ label, kind, onClick: async () => {
    const text = node.querySelector('.btn-label');
    node.disabled = true;
    node.setAttribute('aria-busy', 'true');
    if (text) text.textContent = `${busyLabel}…`;
    try {
      await work();
    } catch (error) {
      onError(error);
    } finally {
      node.disabled = false;
      node.removeAttribute('aria-busy');
      if (text) text.textContent = label;
    }
  } });
  return node;
}

/** Calls `fn` every `ms` while `root` is mounted; the page's dispose stops it. */
const tickers = new WeakMap();
export function tick(root, fn, ms = 1000) {
  stopTick(root);
  tickers.set(root, setInterval(fn, ms));
}
export function stopTick(root) {
  clearInterval(tickers.get(root));
  tickers.delete(root);
}

/**
 * The node `build()` makes, rebuilt only when one of `deps` changed (by
 * identity) since the last call for `name`.
 */
export function keyed(cache, name, deps, build) {
  const previous = cache.get(name);
  if (previous && previous.deps.length === deps.length && previous.deps.every((dep, index) => dep === deps[index])) return previous.node;
  const node = build();
  cache.set(name, { deps, node });
  return node;
}

/** Make `nodes` the children of `container`, touching the DOM only on a change. */
export function place(container, nodes) {
  const wanted = nodes.filter(Boolean);
  const children = container.children;
  if (children.length === wanted.length && wanted.every((node, index) => children[index] === node)) return;
  container.replaceChildren(...wanted);
}

/** Debounced `navigate(..., {replace})` for filter typing (300ms). */
let replaceTimer = 0;
export function replaceSoon(ctx, target) {
  clearTimeout(replaceTimer);
  replaceTimer = setTimeout(() => ctx.navigate(target, { replace: true }), 300);
}
