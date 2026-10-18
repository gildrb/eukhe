// Turn (`#/s/<id>/turn`): the live activity of the current or last turn —
// status, phase timeline, prefill progress, first-token time and decode
// speed, every tool with its live output, retries, compaction, context,
// usage and the queue. Also the desktop aside's default page.

import { definePage } from '../pages.js';
import { store } from '../store.js';
import { derivePhase, liveRate, messageSpeed, prefillRate } from '../turn.js';
import {
  actionButton, backToChat, boundSession, contextMeter, failed, frame, gauge, keyed, knownTools,
  paneHref, place, stats, stopTick, tick, toolRow, waiting,
} from './kit.js';

const views = new WeakMap();

const LOG_LABELS = {
  start: 'Started',
  turn: 'Model request',
  prefill: 'Prefill',
  thinking: 'Thinking',
  writing: 'Writing',
  tool: 'Tools',
  toolEnd: 'Tools',
  retry: 'Retrying',
  retryEnd: 'Retry over',
  compaction: 'Compacting',
  compactionEnd: 'Compaction over',
  wait: 'Waiting for the chat turn',
  error: 'Error',
  end: 'Ended',
};

/** Phase rows from the turn log: consecutive tool entries merge into one `Tools` span. */
function phases(turn, now) {
  const rows = [];
  for (const entry of turn.log) {
    const label = LOG_LABELS[entry.kind] || entry.kind;
    const previous = rows[rows.length - 1];
    if (previous && previous.label === label && (entry.kind === 'tool' || entry.kind === 'toolEnd')) {
      if (entry.kind === 'tool') previous.names.add(entry.name);
      continue;
    }
    let detail = '';
    switch (entry.kind) {
      case 'retry':
        detail = `attempt ${entry.attempt}${entry.text ? ` · ${entry.text}` : ''}`;
        break;
      case 'retryEnd':
        detail = entry.success ? 'succeeded' : 'gave up';
        break;
      case 'compaction':
        detail = entry.reason || '';
        break;
      case 'compactionEnd':
        detail = entry.aborted ? 'cancelled' : 'done';
        break;
      case 'error':
        detail = entry.text || '';
        break;
      default:
        break;
    }
    rows.push({ at: entry.at, kind: entry.kind, label, detail, names: new Set(entry.kind === 'tool' ? [entry.name] : []) });
  }
  const startedAt = rows.length ? rows[0].at : now;
  return rows.map((row, index) => {
    const next = rows[index + 1];
    const end = next ? next.at : turn.running ? now : turn.endedAt || row.at;
    const open = !next && turn.running;
    return { ...row, offset: row.at - startedAt, span: row.kind === 'end' ? null : end - row.at, open };
  });
}

function timeline(ctx, turn, now) {
  const { ui, fmt } = ctx;
  const rows = phases(turn, now);
  if (!rows.length) return ui.el('p', { class: 'pg-line small', text: 'No phases recorded for this turn in this tab.' });
  const list = ui.el('ol', { class: 'pg-timeline' });
  for (const row of rows) {
    const names = [...row.names].filter(Boolean);
    const detail = names.length ? names.join(', ') : row.detail;
    list.append(ui.el('li', { class: 'pg-phase', 'data-open': row.open ? 'true' : null },
      ui.el('span', { class: 'pg-phase-at fig', text: `+${fmt.duration(row.offset)}` }),
      ui.el('span', { class: 'pg-phase-label', text: row.label }),
      ui.el('span', { class: 'pg-phase-detail', text: detail }),
      ui.el('span', { class: 'pg-phase-span fig', text: row.span === null ? '' : `${fmt.duration(row.span)}${row.open ? ' …' : ''}` })));
  }
  return list;
}

function prefillBlock(ctx, progress) {
  const { ui, fmt } = ctx;
  const fraction = progress.total ? progress.processed / progress.total : 0;
  const { rate, etaMs } = prefillRate(progress);
  const cached = progress.total ? progress.cache / progress.total : null;
  const words = [
    `${fmt.percent(fraction)}`,
    `${fmt.num(progress.processed)} / ${fmt.tokens(progress.total)}`,
    rate ? fmt.rate(rate) : null,
    etaMs !== null && Number.isFinite(etaMs) && fraction < 1 ? `~${fmt.duration(etaMs)} left` : null,
    cached !== null ? `${fmt.percent(cached)} cached` : null,
  ].filter(Boolean).join(' · ');
  return ui.el('div', { class: 'pg-meter' }, ui.el('p', { class: 'pg-line fig', text: `Prefill ${words}` }), gauge(fraction, 'Prompt read'));
}

function speedBlock(ctx, session, now) {
  const { fmt } = ctx;
  const { turn, last } = session;
  if (turn.running) {
    const ttft = turn.firstTokenAt && turn.requestAt ? turn.firstTokenAt - turn.requestAt : null;
    const estimate = liveRate(turn, now);
    return stats([
      ['First token', ttft === null ? (turn.requestAt ? `waiting · ${fmt.duration(now - turn.requestAt)}` : null) : fmt.duration(ttft)],
      ['Decode', estimate ? `≈${fmt.rate(estimate)}` : null],
      ['Turn so far', fmt.duration(now - turn.startedAt)],
    ]);
  }
  if (!last) return null;
  // Seen live in this tab: every figure is the one turn agent_end settled.
  if (Number.isFinite(last.durationMs) && last.durationMs > 0) {
    return stats([
      ['First token', Number.isFinite(last.ttftMs) ? fmt.duration(last.ttftMs) : null],
      ['Decode', last.rate ? fmt.rate(last.rate) : null],
      ['Output', Number.isFinite(last.outputTokens) ? fmt.tokens(last.outputTokens) : null],
      ['Turn took', fmt.duration(last.durationMs)],
    ]);
  }
  // Otherwise every figure comes from ONE reply: the newest with timing,
  // labelled with its time when a newer reply without timing exists.
  const settled = settledTurn(session.messages);
  if (!settled) return null;
  const { speed, reply, tookMs } = settled;
  const newest = [...session.messages].reverse().find((message) => message.role === 'assistant');
  return ctx.ui.el('div', { class: 'pg-stack' },
    newest !== reply
      ? ctx.ui.el('p', { class: 'pg-line small fig', text: `From the reply at ${fmt.time(reply.timestamp)}; the newest reply has no timing.` })
      : null,
    stats([
      ['First token', Number.isFinite(speed.ttftMs) ? fmt.duration(speed.ttftMs) : null],
      ['Decode', speed.rate ? fmt.rate(speed.rate) : null],
      ['Output', Number.isFinite(speed.outputTokens) ? fmt.tokens(speed.outputTokens) : null],
      ['Turn took', Number.isFinite(tookMs) && tookMs > 0 ? fmt.duration(tookMs) : null],
    ]));
}

/**
 * The last timed turn from the transcript (after a reload this tab saw
 * none of it): the newest assistant reply carrying `durationMs` or
 * `timing`, its speed, and its length from the user message before it to
 * the reply's end (`timestamp` + `durationMs`, else `timing.lastTokenMs`).
 */
function settledTurn(messages) {
  for (let index = messages.length - 1; index >= 0; index -= 1) {
    const reply = messages[index];
    if (reply.role !== 'assistant') continue;
    const spent = Number.isFinite(reply.durationMs) ? reply.durationMs : reply.timing && reply.timing.lastTokenMs;
    if (!Number.isFinite(spent) || !Number.isFinite(reply.timestamp)) continue;
    let from = index - 1;
    while (from >= 0 && messages[from].role !== 'user') from -= 1;
    const asked = from >= 0 ? messages[from].timestamp : null;
    return {
      reply,
      speed: messageSpeed(reply),
      tookMs: Number.isFinite(asked) && reply.timestamp + spent > asked ? reply.timestamp + spent - asked : spent,
    };
  }
  return null;
}

/** The tool calls of the live or last turn: from this tab's log, else after the last user message. */
function turnTools(session) {
  const tools = knownTools(session);
  const ids = session.turn.log.filter((entry) => entry.kind === 'tool').map((entry) => entry.id);
  if (ids.length) return [...new Set(ids)].map((id) => tools.get(id)).filter(Boolean);
  const { messages } = session;
  let from = messages.length - 1;
  while (from >= 0 && messages[from].role !== 'user') from -= 1;
  const found = [];
  for (const message of messages.slice(from + 1)) {
    if (message.role !== 'assistant' || !Array.isArray(message.content)) continue;
    for (const block of message.content) {
      if (block.type === 'toolCall' && tools.has(block.id)) found.push(tools.get(block.id));
    }
  }
  return found;
}

/** Cost and tokens of the assistant messages since the last user message. */
function turnUsage(messages) {
  let from = messages.length - 1;
  while (from >= 0 && messages[from].role !== 'user') from -= 1;
  let cost = 0;
  let output = 0;
  let seen = false;
  for (const message of messages.slice(from + 1)) {
    if (message.role !== 'assistant' || !message.usage) continue;
    seen = true;
    output += message.usage.output || 0;
    cost += message.usage.cost && Number.isFinite(message.usage.cost.total) ? message.usage.cost.total : 0;
  }
  return seen ? { cost, output } : null;
}

async function loadStats(ctx) {
  const data = await ctx.run({ type: 'get_session_stats' });
  store.set({ stats: data });
}

function controls(ctx, session) {
  const { ui } = ctx;
  const { turn } = session;
  const nodes = [];
  if (turn.running) {
    nodes.push(actionButton({ label: 'Stop', busyLabel: 'Stopping', work: () => ctx.request('abort') }));
  }
  if (turn.retry) {
    nodes.push(actionButton({ label: 'Cancel retry', busyLabel: 'Cancelling', work: () => ctx.run({ type: 'abort_retry' }) }));
  }
  if (turn.compacting) {
    nodes.push(actionButton({ label: 'Cancel compaction', busyLabel: 'Cancelling', work: () => ctx.run({ type: 'abort_compaction' }) }));
  } else {
    nodes.push(actionButton({
      label: 'Compact now',
      busyLabel: 'Compacting',
      work: async () => {
        const result = await ctx.run({ type: 'compact' });
        ui.toast({ text: result && Number.isFinite(result.tokensBefore) ? `Compacted ${ctx.fmt.tokens(result.tokensBefore)} of context.` : 'Compacted.' });
      },
      onError: (error) => failed(error, 'Not compacted'),
    }));
  }
  return ui.el('div', { class: 'pg-actions' }, ...nodes);
}

function render(root, ctx) {
  const parts = frame(root, ctx, { title: 'Turn', back: backToChat(ctx) });
  const view = { parts, cache: new Map(), wasRunning: null, statsFor: null, ctx };
  views.set(root, view);
  tick(root, () => update(root, { ...view.ctx, state: store.get() }));
  update(root, ctx);
}

function update(root, ctx) {
  const view = views.get(root);
  if (!view) return;
  view.ctx = ctx;
  const { ui, fmt, state } = ctx;
  const session = boundSession(ctx);
  const now = Date.now();
  if (!session) {
    view.parts.setTitle('Turn');
    place(view.parts.body, [waiting(ctx, view.cache, 8)]);
    return;
  }
  const { turn } = session;
  if (view.statsFor !== session.id || (view.wasRunning && !turn.running)) {
    view.statsFor = session.id;
    loadStats(ctx).catch(() => {});
  }
  view.wasRunning = turn.running;
  const second = turn.running ? Math.floor(now / 1000) : 0;
  const hasTurn = turn.running || turn.log.length > 0 || session.messages.some((message) => message.role === 'assistant');
  view.parts.setTitle(turn.running ? 'Turn · live' : hasTurn ? 'Last turn' : 'Turn');

  const phase = derivePhase(state, now, fmt);
  const statusNode = keyed(view.cache, 'status', [phase.label, phase.detail, phase.metrics.join('·'), phase.progress], () => {
    const line = ui.el('p', { class: 'pg-status', role: 'status' },
      ui.el('span', { class: 'pg-status-phase', text: phase.label }),
      phase.detail ? ui.el('span', { class: 'pg-status-detail mono', translate: 'no', text: ` · ${phase.detail}` }) : null,
      phase.metrics.length ? ui.el('span', { class: 'pg-status-metrics fig', text: ` · ${phase.metrics.join(' · ')}` }) : null);
    return ui.el('div', { class: 'pg-status-block', 'data-urgent': phase.urgent ? 'true' : null },
      line,
      Number.isFinite(phase.progress) && phase.progress !== null ? gauge(phase.progress, 'Progress') : null);
  });

  if (!hasTurn) {
    place(view.parts.body, [statusNode, keyed(view.cache, 'none', [], () => ui.empty({
      title: 'No turns yet.',
      body: 'Send a message and its activity shows here: phases, speed and every tool.',
      action: { label: 'Go to the chat', href: ctx.href('chat', { sessionId: session.id }) },
    }))]);
    return;
  }

  const timelineNode = keyed(view.cache, 'timeline', [turn.log, second], () => ui.section('Phases', timeline(ctx, turn, now)));
  const prefillNode = turn.prefill && turn.running && !turn.firstTokenAt
    ? keyed(view.cache, 'prefill', [turn.prefill], () => ui.section('Prompt', prefillBlock(ctx, turn.prefill)))
    : null;
  const speedNode = keyed(view.cache, 'speed', [turn, session.last, second], () => {
    const block = speedBlock(ctx, session, now);
    return block ? ui.section('Speed', block) : null;
  });

  const tools = turnTools(session);
  const toolsNode = keyed(view.cache, 'tools', [session.tools, session.messages, turn.log, second], () => {
    if (!tools.length) return ui.section('Tools', ui.el('p', { class: 'pg-line small', text: turn.running ? 'No tools yet in this turn.' : 'This turn used no tools.' }));
    const list = ui.el('div', { class: 'pg-tools' }, ...tools.map((tool) => toolRow(ctx, tool, now)));
    const running = tools.filter((tool) => tool.status === 'running').length;
    const failedCount = tools.filter((tool) => tool.status === 'failed').length;
    const words = [`${tools.length} ${tools.length === 1 ? 'tool' : 'tools'}`, running ? `${running} running` : null, failedCount ? `${failedCount} failed` : null].filter(Boolean).join(' · ');
    return ui.section('Tools', ui.el('p', { class: 'pg-line small fig', text: words }), list);
  });

  const noticeNode = keyed(view.cache, 'notices', [turn.retry, turn.compacting, turn.error, second], () => {
    const lines = [];
    if (turn.retry) {
      const left = Math.max(0, turn.retry.at + turn.retry.delayMs - now);
      const of = turn.retry.maxAttempts ? `${turn.retry.attempt} of ${turn.retry.maxAttempts}` : `attempt ${turn.retry.attempt}`;
      lines.push(ui.el('p', { class: 'pg-notice' }, `Retrying ${of} ${left > 0 ? `in ${fmt.duration(left)}` : 'now'}`,
        turn.retry.errorMessage ? ui.el('span', { class: 'pg-notice-detail', text: ` · ${turn.retry.errorMessage}` }) : null,
        turn.retry.backupModel ? ui.el('span', { class: 'pg-notice-detail', text: ` · falling back to ${turn.retry.backupModel.id || turn.retry.backupModel}` }) : null));
    }
    if (turn.compacting) {
      lines.push(ui.el('p', { class: 'pg-notice' }, `Compacting context (${turn.compacting.reason}) · ${fmt.duration(now - turn.compacting.at)}`));
      if (turn.compacting.summary) lines.push(ui.el('p', { class: 'pg-prose', text: turn.compacting.summary }));
    }
    if (turn.error && !turn.running) lines.push(ui.el('p', { class: 'pg-notice', 'data-kind': 'error' }, ui.el('strong', { text: 'Failed' }), ` · ${turn.error}`));
    return lines.length ? ui.section('Notices', ...lines) : null;
  });

  const contextNode = keyed(view.cache, 'context', [session.state.contextUsage], () => ui.section('Context', contextMeter(session.state.contextUsage)));
  const usageNode = keyed(view.cache, 'usage', [state.stats, session.messages], () => {
    const thisTurn = turnUsage(session.messages);
    const total = state.stats && state.stats.sessionId === session.state.sessionId ? state.stats : null;
    return ui.section('Usage', stats([
      ['This turn', thisTurn ? `${fmt.cost(thisTurn.cost)} · ${fmt.tokens(thisTurn.output)} out` : null],
      ['Session', total ? `${fmt.cost(total.cost)} · ${fmt.tokens(total.tokens.total)}` : null],
    ]), ui.el('a', { class: 'link target', href: paneHref(ctx, { page: 'usage' }), text: 'All usage →' }));
  });
  const queueNode = keyed(view.cache, 'queue', [session.queue], () => {
    const count = session.queue.steering.length + session.queue.followUps.length;
    return ui.section('Queue',
      ui.el('p', { class: 'pg-line fig', text: count ? `${count} queued · ${session.queue.steering.length} steer, ${session.queue.followUps.length} next` : 'Nothing queued.' }),
      ui.el('a', { class: 'link target', href: paneHref(ctx, { page: 'queue' }), text: 'Manage the queue →' }));
  });
  const controlsNode = keyed(view.cache, 'controls', [turn.running, turn.retry, turn.compacting], () => controls(ctx, session));
  place(view.parts.body, [statusNode, controlsNode, noticeNode, prefillNode, speedNode, toolsNode, timelineNode, contextNode, usageNode, queueNode]);
}

export default definePage({
  id: 'turn',
  title(ctx) {
    const session = boundSession(ctx);
    return session && session.turn.running ? 'Turn · live' : 'Turn';
  },
  render,
  update,
  dispose(root) {
    stopTick(root);
    views.delete(root);
  },
});
