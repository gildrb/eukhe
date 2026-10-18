// PURE session state: the open reply plus every SessionEvent folded in
// (`reduce`), and `derivePhase`, the one source of the status line, the
// Inbox row status, the document title, the badge and announcements.
// No DOM, no clock reads: callers pass `now`.

const CHARS_PER_TOKEN = 4; // eukhe-tui/src/gen_speed.rs
const LIVE_RATE_AFTER_MS = 250;
const BASH_TAIL_CHARS = 64_000;
const NOTE_LIMIT = 200;
const LOG_LIMIT = 400;
const SIGNAL_RULES = '[Signal reply rules:';

/** Plain text of message content (a string, or text blocks). */
export function contentText(content) {
  if (typeof content === 'string') return content;
  if (!Array.isArray(content)) return '';
  return content
    .filter((block) => block && (block.type === 'text' || (!block.type && typeof block.text === 'string')))
    .map((block) => block.text)
    .join('\n\n');
}

/** A user prompt without the Signal gateway's reply rules. */
export function withoutSignalRules(text) {
  if (!text.startsWith(SIGNAL_RULES)) return text;
  const end = text.indexOf(']');
  return end < 0 ? text : text.slice(end + 1).trimStart();
}

function freshTurn(now) {
  return {
    running: false,
    startedAt: now,
    endedAt: 0,
    requestAt: 0,
    firstTokenAt: 0,
    prefill: null,
    prefillAt: 0,
    stream: null,
    deltaChars: 0,
    deltaStartAt: 0,
    retry: null,
    compacting: null,
    chatWait: false,
    error: null,
    stopped: false,
    log: [],
  };
}

const EMPTY_QUEUE = { queuedCount: 0, steering: [], followUps: [] };

/**
 * The session state for an `open` reply. With `replay: 'complete'` and the
 * same session already in hand, the transcript is kept (the bridge replays
 * what was missed as ordinary events).
 */
export function openSession(reply, previous, now) {
  const state = reply.state || {};
  const keep = previous && previous.id === reply.session.id && reply.replay === 'complete' && !Array.isArray(reply.messages);
  const base = keep ? previous : {
    messages: [],
    live: null,
    openIndex: -1,
    tools: {},
    turn: freshTurn(now),
    last: null,
    bash: null,
    memory: { stamp: 0, last: null },
    notes: [],
    pending: previous && previous.id === reply.session.id ? previous.pending : [],
  };
  const session = {
    ...base,
    id: reply.session.id,
    path: reply.session.path,
    state,
    summary: reply.summary || null,
    cursor: reply.cursor || (keep ? previous.cursor : null),
    queue: state.sessionActions || EMPTY_QUEUE,
    goal: state.goal ?? null,
    serviceTier: state.serviceTier || null,
  };
  if (!keep) {
    session.messages = Array.isArray(reply.messages) ? reply.messages : [];
    session.last = lastFromMessages(session.messages);
    if (state.isStreaming) session.turn = { ...freshTurn(now), running: true };
    if (state.isCompacting) session.turn = { ...session.turn, compacting: { reason: 'threshold', at: now, summary: '' } };
  }
  session.title = sessionTitle(session);
  return session;
}

/** The session's display title. */
export function sessionTitle(session, fallback = 'New session') {
  const name = session.state && session.state.sessionName;
  if (name) return name;
  if (session.summary && session.summary.sessionName) return session.summary.sessionName;
  const first = session.messages.find((message) => message.role === 'user');
  const text = first ? withoutSignalRules(contentText(first.content)).trim() : '';
  return text ? text.split('\n')[0].slice(0, 80) : fallback;
}

function log(turn, entry) {
  const next = turn.log.length >= LOG_LIMIT ? turn.log.slice(-LOG_LIMIT + 1) : turn.log.slice();
  next.push(entry);
  return next;
}

function note(session, kind, text, now, extra = {}) {
  const notes = session.notes.length >= NOTE_LIMIT ? session.notes.slice(1) : session.notes.slice();
  notes.push({ at: now, kind, text, index: session.messages.length, ...extra });
  return notes;
}

/** Exact speed of a settled assistant message, from `usage` and `timing`. */
export function messageSpeed(message) {
  if (!message || message.role !== 'assistant') return null;
  const timing = message.timing || {};
  const output = message.usage ? message.usage.output : 0;
  const decodeMs = timing.lastTokenMs !== undefined && timing.firstTokenMs !== undefined ? timing.lastTokenMs - timing.firstTokenMs : 0;
  return {
    ttftMs: timing.firstTokenMs ?? null,
    rate: decodeMs > 0 && output > 0 ? output / (decodeMs / 1000) : null,
    outputTokens: output || null,
    durationMs: message.durationMs ?? (timing.lastTokenMs ?? null),
  };
}

function lastFromMessages(messages) {
  for (let index = messages.length - 1; index >= 0; index -= 1) {
    if (messages[index].role === 'assistant') return { ...messageSpeed(messages[index]), durationMs: null };
  }
  return null;
}

/** Live decode estimate (≈ chars / 4), once 250ms of deltas came in. */
export function liveRate(turn, now) {
  if (!turn.deltaStartAt || turn.deltaChars <= 0) return null;
  const elapsed = now - turn.deltaStartAt;
  if (elapsed < LIVE_RATE_AFTER_MS) return null;
  return turn.deltaChars / CHARS_PER_TOKEN / (elapsed / 1000);
}

/** Prefill throughput and ETA from `prompt_progress`. */
export function prefillRate(progress) {
  if (!progress || !progress.timeMs) return { rate: null, etaMs: null };
  const fresh = progress.processed - progress.cache;
  const rate = fresh > 0 ? fresh / (progress.timeMs / 1000) : null;
  const etaMs = rate ? ((progress.total - progress.processed) / rate) * 1000 : null;
  return { rate, etaMs };
}

function reconcilePending(pending, message) {
  if (!pending.length) return pending;
  const admissionId = message.admissionId || (message.details && message.details.admissionId);
  const text = withoutSignalRules(contentText(message.content)).trim();
  const index = pending.findIndex((item) => (admissionId ? item.admissionId === admissionId : item.text.trim() === text));
  if (index < 0) return pending;
  return [...pending.slice(0, index), ...pending.slice(index + 1)];
}

function onStreamUpdate(turn, update, now) {
  if (!update) return turn;
  switch (update.type) {
    case 'text_delta':
    case 'thinking_delta':
    case 'toolcall_delta': {
      const stream = update.type === 'thinking_delta' ? 'thinking' : 'writing';
      const next = {
        ...turn,
        deltaChars: turn.deltaChars + update.delta.length,
        deltaStartAt: turn.deltaStartAt || now,
        firstTokenAt: turn.firstTokenAt || now,
        stream,
      };
      if (turn.stream !== stream) next.log = log(turn, { at: now, kind: stream });
      return next;
    }
    case 'start':
    case 'text_start':
    case 'text_end':
    case 'thinking_start':
    case 'thinking_end':
    case 'toolcall_start':
    case 'toolcall_end':
    case 'message':
      return turn;
    default:
      return turn;
  }
}

/** Fold one SessionEvent into the session. Returns a new object when anything changed. */
export function reduce(session, event, now) {
  if (!session) return session;
  const { turn } = session;
  switch (event.type) {
    case 'agent_start':
      return { ...session, live: null, turn: { ...freshTurn(now), running: true, log: [{ at: now, kind: 'start' }] } };
    case 'agent_end': {
      const lastAssistant = [...session.messages].reverse().find((message) => message.role === 'assistant');
      const speed = messageSpeed(lastAssistant);
      const stopped = Boolean(lastAssistant && lastAssistant.stopReason === 'aborted');
      const failed = lastAssistant && lastAssistant.stopReason === 'error' ? lastAssistant.errorMessage || 'The model request failed.' : null;
      const tools = { ...session.tools };
      for (const [id, tool] of Object.entries(tools)) {
        if (tool.status === 'running') tools[id] = { ...tool, status: stopped ? 'stopped' : 'done', endedAt: now };
      }
      return {
        ...session,
        live: null,
        tools,
        bash: null,
        turn: {
          ...turn,
          running: false,
          endedAt: now,
          stopped,
          error: turn.error || failed,
          retry: null,
          chatWait: false,
          stream: null,
          log: log(turn, { at: now, kind: 'end' }),
        },
        last: { ...(speed || {}), durationMs: now - turn.startedAt },
      };
    }
    case 'turn_start':
      return {
        ...session,
        turn: {
          ...turn,
          running: true,
          requestAt: now,
          firstTokenAt: 0,
          prefill: null,
          prefillAt: 0,
          stream: null,
          deltaChars: 0,
          deltaStartAt: 0,
          log: log(turn, { at: now, kind: 'turn' }),
        },
      };
    case 'turn_end':
      if (!event.error) return session;
      return {
        ...session,
        turn: { ...turn, error: event.error, log: log(turn, { at: now, kind: 'error', text: event.error }) },
        notes: note(session, 'error', event.error, now),
      };
    case 'prompt_progress':
      return {
        ...session,
        turn: {
          ...turn,
          prefill: event.progress,
          prefillAt: turn.prefillAt || now,
          log: turn.prefill ? turn.log : log(turn, { at: now, kind: 'prefill' }),
        },
      };
    case 'message_start': {
      const { message } = event;
      if (message.role === 'assistant') {
        return {
          ...session,
          live: message,
          turn: onStreamUpdate({ ...turn, deltaChars: 0, deltaStartAt: 0, stream: null }, event.assistantMessageEvent, now),
        };
      }
      const pending = message.role === 'user' ? reconcilePending(session.pending, message) : session.pending;
      return { ...session, messages: [...session.messages, message], openIndex: session.messages.length, pending };
    }
    case 'message_update':
      return { ...session, live: event.message, turn: onStreamUpdate(turn, event.assistantMessageEvent, now) };
    case 'message_end': {
      const { message } = event;
      if (message.role === 'assistant') {
        return {
          ...session,
          live: null,
          messages: [...session.messages, message],
          turn: { ...turn, stream: null },
          last: { ...messageSpeed(message), durationMs: null },
        };
      }
      const messages = session.messages.slice();
      if (session.openIndex >= 0 && session.openIndex < messages.length && messages[session.openIndex].role === message.role) {
        messages[session.openIndex] = message;
      } else {
        messages.push(message);
      }
      const pending = message.role === 'user' ? reconcilePending(session.pending, message) : session.pending;
      const next = { ...session, messages, openIndex: -1, pending };
      next.title = sessionTitle(next);
      return next;
    }
    case 'tool_execution_start':
      return {
        ...session,
        tools: {
          ...session.tools,
          [event.toolCallId]: {
            id: event.toolCallId,
            name: event.toolName,
            args: event.args,
            status: 'running',
            partial: null,
            result: null,
            isError: false,
            startedAt: now,
            endedAt: 0,
            updatedAt: now,
          },
        },
        turn: { ...turn, stream: null, log: log(turn, { at: now, kind: 'tool', id: event.toolCallId, name: event.toolName }) },
      };
    case 'tool_execution_update': {
      const tool = session.tools[event.toolCallId] || {
        id: event.toolCallId, name: event.toolName, args: event.args, status: 'running', result: null, isError: false, startedAt: now, endedAt: 0,
      };
      return { ...session, tools: { ...session.tools, [event.toolCallId]: { ...tool, partial: event.partialResult, updatedAt: now } } };
    }
    case 'tool_execution_end': {
      const tool = session.tools[event.toolCallId] || { id: event.toolCallId, name: event.toolName, args: null, partial: null, startedAt: now };
      return {
        ...session,
        tools: {
          ...session.tools,
          [event.toolCallId]: { ...tool, status: event.isError ? 'failed' : 'done', result: event.result, isError: event.isError, endedAt: now, updatedAt: now },
        },
        turn: { ...turn, log: log(turn, { at: now, kind: 'toolEnd', id: event.toolCallId, name: event.toolName, failed: event.isError }) },
      };
    }
    case 'auto_retry_start':
      return {
        ...session,
        turn: {
          ...turn,
          retry: {
            attempt: event.attempt,
            maxAttempts: event.maxAttempts ?? null,
            delayMs: event.delayMs,
            errorMessage: event.errorMessage,
            backupModel: event.backupModel || null,
            at: now,
          },
          log: log(turn, { at: now, kind: 'retry', attempt: event.attempt, text: event.errorMessage }),
        },
      };
    case 'auto_retry_end':
      return {
        ...session,
        turn: {
          ...turn,
          retry: null,
          error: event.success ? turn.error : event.finalError || 'Retries ran out.',
          log: log(turn, { at: now, kind: 'retryEnd', success: event.success }),
        },
        notes: event.success
          ? session.notes
          : note(session, 'error', `Retries ran out: ${event.finalError || 'the request kept failing.'}`, now),
      };
    case 'compaction_start':
      return {
        ...session,
        turn: {
          ...turn,
          compacting: { reason: event.reason, at: now, summary: '' },
          log: log(turn, { at: now, kind: 'compaction', reason: event.reason }),
        },
      };
    case 'compaction_summary_delta':
      if (!turn.compacting) return session;
      return { ...session, turn: { ...turn, compacting: { ...turn.compacting, summary: turn.compacting.summary + event.delta } } };
    case 'compaction_end': {
      let text;
      let kind = 'note';
      if (event.aborted) text = 'Compaction cancelled.';
      else if (event.errorMessage) {
        text = `Compaction failed: ${event.errorMessage}`;
        kind = 'error';
      } else text = 'Earlier messages compacted.';
      return {
        ...session,
        turn: { ...turn, compacting: null, log: log(turn, { at: now, kind: 'compactionEnd', aborted: event.aborted }) },
        notes: note(session, kind, text, now, { summary: event.result ? event.result.summary : null }),
      };
    }
    case 'session_info_changed': {
      const next = { ...session, state: { ...session.state, sessionName: event.name ?? null } };
      next.title = sessionTitle(next);
      return next;
    }
    case 'service_tier_changed':
      return { ...session, serviceTier: event.serviceTier, state: { ...session.state, serviceTier: event.serviceTier } };
    case 'session_action_update':
      return { ...session, queue: event.actions };
    case 'goal_update':
      return { ...session, goal: event.goal };
    case 'chat_turn_wait':
      return {
        ...session,
        turn: { ...turn, chatWait: event.waiting, log: event.waiting ? log(turn, { at: now, kind: 'wait' }) : turn.log },
      };
    case 'memory_update':
      return { ...session, memory: { stamp: session.memory.stamp + 1, last: event.update } };
    case 'agent_relay':
      return { ...session, notes: note(session, 'relay', `${event.from} → ${event.to}: ${event.text}`, now) };
    case 'bash_start':
      return { ...session, bash: { command: event.command, output: '', startedAt: now } };
    case 'bash_output': {
      if (!session.bash) return session;
      const output = (session.bash.output + event.chunk).slice(-BASH_TAIL_CHARS);
      return { ...session, bash: { ...session.bash, output } };
    }
    case 'bash_end':
      return {
        ...session,
        bash: null,
        notes: event.errorMessage ? note(session, 'error', `Shell command failed: ${event.errorMessage}`, now) : session.notes,
      };
    case 'refine_complete':
      return { ...session, notes: note(session, 'note', 'Refinement applied.', now) };
    case 'refine_failed':
      return { ...session, notes: note(session, 'error', `Refinement failed: ${event.error}`, now) };
    case 'ipython_sent_agent_message':
      return { ...session, notes: note(session, 'note', 'The Python kernel sent the agent a message.', now) };
    default:
      return session;
  }
}

const EFFECT_WORDS = { read: 'Reads files', write: 'Changes files', exec: 'Runs a program', net: 'Uses the network' };

/** A shell effect as words. */
export function effectWords(effect) {
  return EFFECT_WORDS[effect] || 'Runs a command';
}

/** One line naming what a tool call acts on (`cargo test`, `src/main.rs`). */
export function toolTarget(args) {
  if (!args || typeof args !== 'object') return typeof args === 'string' ? args : '';
  for (const key of ['command', 'cmd', 'path', 'file_path', 'filePath', 'pattern', 'query', 'url', 'code', 'description']) {
    if (typeof args[key] === 'string' && args[key]) return args[key].split('\n')[0];
  }
  const values = Object.values(args);
  if (values.length === 1 && typeof values[0] === 'string') return values[0].split('\n')[0];
  const json = JSON.stringify(args);
  return json === '{}' ? '' : json;
}

function modelName(model) {
  if (!model) return '';
  if (typeof model === 'string') return model;
  return model.name || model.id || '';
}

function basename(path) {
  if (!path) return '';
  const parts = String(path).split('/').filter(Boolean);
  return parts.length ? parts[parts.length - 1] : '/';
}

function contextPercent(session) {
  const usage = session.state && session.state.contextUsage;
  if (!usage) return null;
  if (Number.isFinite(usage.percent)) return usage.percent;
  if (usage.tokens && usage.contextWindow) return (usage.tokens / usage.contextWindow) * 100;
  return null;
}

function phase(kind, label, extra = {}) {
  return { phase: kind, label, detail: '', metrics: [], urgent: false, since: 0, progress: null, ...extra };
}

/**
 * The one status. `fmt` is format.js (injected to keep this module pure).
 * Returns `{ phase, label, detail, metrics: string[], since, progress, urgent, announce }`.
 */
export function derivePhase(state, now, fmt) {
  const { link, session, approvals } = state;
  const pendingApprovals = (approvals || []).filter((item) => item.status !== 'elsewhere');
  if (pendingApprovals.length) {
    const first = pendingApprovals[0];
    return phase('approval', 'Needs approval', {
      detail: first.command,
      metrics: [effectWords(first.effect)],
      urgent: true,
      announce: `Needs approval: ${first.command}`,
    });
  }
  if (link.status === 'unavailable') return phase('unavailable', 'Daemon unreachable', { detail: link.error || '', announce: 'Daemon unreachable' });
  if (link.status === 'offline') {
    const seconds = Math.max(0, Math.ceil((link.retryAt - now) / 1000));
    return phase('offline', 'Offline', { detail: seconds ? `retrying in ${fmt.num(seconds)}\u00a0s` : 'retrying…', announce: 'Offline' });
  }
  if (link.status === 'connecting') return phase('connecting', 'Connecting…');
  if (link.catchingUp) return phase('catchingUp', 'Catching up…');
  if (!session) return phase('opening', 'Opening…');
  const { turn, summary } = session;
  const elapsed = turn.running ? [`turn ${fmt.duration(now - turn.startedAt)}`] : [];
  if (turn.retry) {
    const left = Math.max(0, turn.retry.at + turn.retry.delayMs - now);
    const of = turn.retry.maxAttempts ? `${turn.retry.attempt}/${turn.retry.maxAttempts}` : `${turn.retry.attempt}`;
    return phase('retrying', `Retrying ${of}`, {
      detail: turn.retry.errorMessage,
      metrics: [left > 0 ? `in ${fmt.duration(left)}` : 'now'],
      since: turn.retry.at,
      announce: `Retrying, attempt ${turn.retry.attempt}`,
    });
  }
  if (turn.compacting) {
    return phase('compacting', 'Compacting context', { metrics: [fmt.duration(now - turn.compacting.at)], since: turn.compacting.at, announce: 'Compacting context' });
  }
  if (session.bash) {
    return phase('bash', `$ ${session.bash.command.split('\n')[0]}`, { metrics: [fmt.duration(now - session.bash.startedAt)], since: session.bash.startedAt });
  }
  const running = Object.values(session.tools).filter((tool) => tool.status === 'running');
  if (turn.running && running.length === 1) {
    const [tool] = running;
    return phase('tool', tool.name, {
      detail: toolTarget(tool.args),
      metrics: [fmt.duration(now - tool.startedAt), ...elapsed],
      since: tool.startedAt,
      announce: `Running ${tool.name}`,
    });
  }
  if (turn.running && running.length > 1) {
    const names = [...new Set(running.map((tool) => tool.name))].join(', ');
    const since = Math.min(...running.map((tool) => tool.startedAt));
    return phase('tools', `${running.length} tools running`, { detail: names, metrics: [fmt.duration(now - since), ...elapsed], since, announce: `Running ${running.length} tools` });
  }
  if (turn.running && turn.chatWait) return phase('chatWait', 'Waiting for the chat turn', { metrics: elapsed });
  if (turn.running && turn.stream) {
    const estimate = liveRate(turn, now);
    const metrics = [];
    if (estimate) metrics.push(`≈${fmt.rate(estimate)}`);
    if (turn.stream === 'writing' && turn.deltaChars) metrics.push(fmt.tokens(Math.round(turn.deltaChars / CHARS_PER_TOKEN)));
    metrics.push(...elapsed);
    return phase(turn.stream, turn.stream === 'thinking' ? 'Thinking' : 'Writing', {
      metrics,
      since: turn.deltaStartAt,
      announce: turn.stream === 'thinking' ? 'Thinking' : 'Writing',
    });
  }
  if (turn.running && turn.prefill && !turn.firstTokenAt) {
    const progress = turn.prefill.total ? turn.prefill.processed / turn.prefill.total : 0;
    const { rate, etaMs } = prefillRate(turn.prefill);
    const metrics = [`${fmt.num(turn.prefill.processed)} / ${fmt.tokens(turn.prefill.total)}`];
    if (rate) metrics.push(fmt.rate(rate));
    if (etaMs !== null && Number.isFinite(etaMs)) metrics.push(`~${fmt.duration(etaMs)}`);
    return phase('prefill', `Prefill ${fmt.percent(progress)}`, { metrics, progress, since: turn.prefillAt, announce: 'Reading the prompt' });
  }
  if (turn.running && summary && summary.admission === 'queued' && !turn.firstTokenAt && !turn.requestAt) {
    return phase('admission', 'Waiting for a provider slot', { metrics: [fmt.duration(now - turn.startedAt)], since: turn.startedAt });
  }
  if (turn.running) {
    const since = turn.requestAt || turn.startedAt;
    return phase('waiting', 'Waiting for first token', { metrics: [fmt.duration(now - since), ...elapsed.slice(turn.requestAt ? 0 : 1)], since, announce: 'Turn started' });
  }
  const sending = session.pending.find((item) => item.status === 'sending');
  if (sending) return phase('sending', 'Sending…');
  if (summary && summary.isQuotaParked) return phase('parked', 'Paused', { detail: 'usage limit', announce: 'Paused at the usage limit' });
  if (summary && summary.hasRunningSubagents && !turn.endedAt) return phase('subagents', 'Subagents still running');
  if (turn.error) {
    return phase('failed', 'Failed', { detail: turn.error, urgent: true, announce: `Failed: ${turn.error}` });
  }
  if (turn.stopped) {
    return phase('stopped', turn.endedAt ? `Stopped after ${fmt.duration(turn.endedAt - turn.startedAt)}` : 'Stopped', { announce: 'Stopped' });
  }
  const context = contextPercent(session);
  if (!session.messages.length) {
    const parts = [modelName(session.state.model), basename(session.state.cwd)].filter(Boolean);
    return phase('idleNew', 'Ready', { metrics: parts });
  }
  const metrics = [];
  const { last } = session;
  if (last && last.rate) metrics.push(fmt.rate(last.rate));
  if (last && Number.isFinite(last.ttftMs)) metrics.push(`TTFT ${fmt.duration(last.ttftMs)}`);
  if (context !== null) metrics.push(`ctx ${fmt.percent(context, { of100: true })}`);
  const label = last && last.durationMs ? `Done in ${fmt.duration(last.durationMs)}` : 'Idle';
  return phase('idle', label, { metrics, announce: label });
}

/**
 * A minimal session for a list row that is not the bound one, so the
 * Inbox can call `derivePhase` on it too (`row.summary` when the bridge
 * sends one).
 */
export function rowSession(row, now) {
  const summary = row.summary || null;
  const turn = freshTurn(now);
  if (summary && summary.isStreaming) {
    turn.running = true;
    turn.startedAt = summary.lastActivityAt ? Date.parse(summary.lastActivityAt) : now;
  }
  if (summary && summary.isCompacting) turn.compacting = { reason: 'threshold', at: now, summary: '' };
  return {
    id: row.id,
    path: row.path,
    state: { cwd: row.cwd },
    summary,
    messages: summary && summary.messageCount ? [{ role: 'user', content: '' }] : [{ role: 'user', content: row.title || '' }],
    live: null,
    tools: {},
    turn,
    last: null,
    bash: null,
    pending: [],
    notes: [],
    queue: (summary && summary.sessionActions) || EMPTY_QUEUE,
  };
}
