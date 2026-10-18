// The Chat page: the transcript grouped into turns, folds for settled
// thinking and tools, live tool rows, the streaming message (only its last
// markdown block re-renders), and the Dock.

import { definePage } from './pages.js';
import { el, button, skeleton, empty } from './ui.js';
import { createRenderer, markdown } from './markdown.js';
import { contentText, withoutSignalRules, toolTarget, messageSpeed } from './turn.js';
import { createDock } from './dock.js';
import { fmt } from './format.js';
import { href } from './router.js';

const STICK_PX = 48;
const TAIL_LINES = 3;
const USER_CLAMP_LINES = 12;
const BASH_LINES = 6;
const SUGGESTIONS = [
  'Explain how this repository is laid out',
  'Find the failing test and fix it',
  'Review my uncommitted changes',
];

// Thinking time per streamed block, measured live (history has none).
const thinkingMs = new Map();

function blockKey(message, index) {
  return `${message.timestamp}:${index}`;
}

function imageNodes(content) {
  if (!Array.isArray(content)) return [];
  return content
    .filter((block) => block && block.type === 'image' && block.data && block.mimeType)
    .map((block) => el('img', {
      class: 'msg-image',
      src: `data:${block.mimeType};base64,${block.data}`,
      alt: 'Attached image',
      loading: 'lazy',
      decoding: 'async',
      width: block.width || null,
      height: block.height || null,
    }));
}

function userBubble(text, { origin = null, images = [], state = null, actions = null } = {}) {
  const bubble = el('div', { class: 'msg-user' });
  if (origin) bubble.append(el('span', { class: 'msg-origin', text: origin }));
  if (images.length) bubble.append(el('div', { class: 'msg-user-images' }, images));
  const body = el('span', { class: 'msg-user-text', text });
  bubble.append(body);
  if (text.split('\n').length > USER_CLAMP_LINES) {
    bubble.dataset.clamped = 'true';
    const more = button({ label: 'Show more', onClick: () => {
      const clamped = bubble.dataset.clamped === 'true';
      bubble.dataset.clamped = clamped ? 'false' : 'true';
      more.querySelector('.btn-label').textContent = clamped ? 'Show less' : 'Show more';
    } });
    bubble.append(more);
  }
  const wrap = el('div', { class: 'msg-wrap' }, bubble);
  if (state) wrap.append(el('span', { class: 'msg-state', text: state }));
  if (actions) wrap.append(el('div', { class: 'msg-pending-actions' }, actions));
  return wrap;
}

function outputText(output) {
  if (!output) return '';
  if (typeof output === 'string') return output;
  return contentText(output.content || output);
}

function lastLines(text, count) {
  const lines = text.replace(/\s+$/, '').split('\n');
  return lines.slice(-count);
}

/** Status word of a tool call: running 0:42 / 12 s / failed / waiting. */
function toolState(tool, now) {
  switch (tool.status) {
    case 'running':
      return `running ${fmt.duration(now - tool.startedAt)}`;
    case 'failed':
      return 'failed';
    case 'stopped':
      return 'stopped';
    case 'done':
      return tool.startedAt && tool.endedAt ? fmt.duration(tool.endedAt - tool.startedAt) : 'done';
    case 'waiting':
      return 'waiting';
    case 'missing':
      return 'no result';
    default:
      return '';
  }
}

/** One tool row, patchable in place: `{ node, patch(tool, now) }`. */
function toolRow(sessionId, tool) {
  const state = el('span', { class: 'tool-state' });
  const link = el('a', { class: 'tool-row', href: href('tool', { sessionId, rest: [tool.id] }) },
    el('span', { class: 'tool-name', translate: 'no', text: tool.name }),
    el('span', { class: 'tool-target', translate: 'no', text: toolTarget(tool.args) }),
    state);
  const tail = el('div', { class: 'tool-tail', 'aria-hidden': 'true' });
  const images = el('div', { class: 'tool-images' });
  const node = el('div', { class: 'tool', 'data-status': tool.status }, link);
  let lastTail = null;
  const patch = (next, now) => {
    node.dataset.status = next.status;
    const word = toolState(next, now);
    if (state.textContent !== word) state.textContent = word;
    const live = next.status === 'running' && next.partial ? outputText(next.partial) : '';
    if (live !== lastTail) {
      lastTail = live;
      if (live) {
        tail.replaceChildren(...lastLines(live, TAIL_LINES).map((line) => el('span', { text: line || '\u00a0' })));
        if (!tail.isConnected) node.append(tail);
      } else tail.remove();
    }
    const result = next.result && Array.isArray(next.result.content) ? next.result.content : [];
    if (result.length && !images.isConnected) {
      const shown = imageNodes(result);
      if (shown.length) {
        images.replaceChildren(...shown);
        node.append(images);
      }
    }
  };
  return { node, patch };
}

function errorRow(text, onRetry) {
  return el('div', { class: 'msg-error', role: 'alert' },
    el('span', { class: 'msg-error-label', text: 'Failed' }),
    el('span', { class: 'msg-error-text', text }),
    onRetry ? button({ label: 'Retry', kind: 'primary', onClick: onRetry }) : null);
}

function metaLine(message) {
  const speed = messageSpeed(message);
  const parts = [fmt.time(message.timestamp)];
  if (speed && speed.rate) parts.push(fmt.rate(speed.rate));
  if (speed && speed.outputTokens) parts.push(fmt.tokens(speed.outputTokens));
  if (speed && Number.isFinite(speed.ttftMs)) parts.push(`TTFT ${fmt.duration(speed.ttftMs)}`);
  return el('div', { class: 'msg-meta', text: parts.join(' · ') });
}

/** The stream of an assistant message's blocks, with tool status resolved. */
function assistantItems(message, view) {
  const items = [];
  const blocks = Array.isArray(message.content) ? message.content : [{ type: 'text', text: String(message.content || '') }];
  blocks.forEach((block, index) => {
    if (block.type === 'text' && block.text && block.text.trim()) items.push({ kind: 'text', text: block.text });
    else if (block.type === 'thinking' && (block.thinking || '').trim()) items.push({ kind: 'thinking', text: block.thinking, key: blockKey(message, index) });
    else if (block.type === 'toolCall') {
      const tool = view.resolveTool(block);
      if (!tool.startedAt && tool.endedAt) tool.startedAt = message.timestamp + ((message.timing && message.timing.lastTokenMs) || 0);
      items.push({ kind: 'tool', tool });
    }
  });
  return items;
}

function thinkingFold(text, key, open) {
  const known = thinkingMs.get(key);
  const label = known ? `Thought for ${fmt.duration(known)}` : 'Thought';
  const fold = el('details', { class: 'fold' }, el('summary', { text: label }), el('div', { class: 'fold-body' }, el('div', { class: 'thinking-body', text })));
  if (open) fold.open = true;
  return fold;
}

function toolGroup(tools, rows) {
  const failed = tools.filter((tool) => tool.status === 'failed').length;
  const starts = tools.map((tool) => tool.startedAt).filter(Boolean);
  const ends = tools.map((tool) => tool.endedAt).filter(Boolean);
  const spent = starts.length && ends.length ? Math.max(...ends) - Math.min(...starts) : 0;
  const parts = [`Used ${fmt.num(tools.length)} tools`];
  if (spent > 0) parts.push(fmt.duration(spent));
  if (failed) parts.push(`${fmt.num(failed)} failed`);
  return el('details', { class: 'fold' }, el('summary', { text: parts.join(' · ') }), el('div', { class: 'fold-body' }, rows));
}

/**
 * Append the items of one turn's assistant side. Settled consecutive tool
 * calls (two or more) fold into "Used N tools"; a running one never does.
 */
function appendItems(target, items, view, now) {
  let run = [];
  const flush = () => {
    if (!run.length) return;
    const rows = run.map((tool) => view.toolNode(tool, now));
    const settled = run.every((tool) => tool.status !== 'running' && tool.status !== 'waiting');
    if (run.length >= 2 && settled) target.append(toolGroup(run, rows));
    else target.append(...rows);
    run = [];
  };
  for (const item of items) {
    if (item.kind === 'tool') {
      run.push(item.tool);
      continue;
    }
    flush();
    if (item.kind === 'text') target.append(markdown(item.text));
    else target.append(thinkingFold(item.text, item.key, false));
  }
  flush();
}

function renderMessage(target, message, view, now, items) {
  switch (message.role) {
    case 'user': {
      const text = withoutSignalRules(contentText(message.content));
      const images = imageNodes(message.content);
      if (text.trim() || images.length) target.append(userBubble(text, { images }));
      return items;
    }
    case 'custom': {
      if (message.display === false) return items;
      const text = contentText(message.content);
      if (!text.trim()) return items;
      if (message.customType === 'signal') target.append(userBubble(text, { origin: 'from Signal' }));
      else {
        // `eukhe.settings_error` → "Settings error".
        const words = String(message.customType || 'note').split('.').pop().replace(/[_-]+/g, ' ').trim() || 'Note';
        const label = words.charAt(0).toUpperCase() + words.slice(1);
        const body = markdown(text);
        body.classList.add('custom-body');
        target.append(el('div', { class: 'custom-note', role: 'note' }, el('span', { class: 'custom-label', text: label }), body));
      }
      return items;
    }
    case 'assistant':
      return [...items, ...assistantItems(message, view), { kind: 'end', message }];
    case 'toolResult':
      return items;
    case 'bashExecution': {
      const lines = lastLines(message.output || '', BASH_LINES);
      const total = (message.output || '').split('\n').length;
      const tool = el('div', { class: 'tool' },
        el('div', { class: 'tool-row' },
          el('span', { class: 'tool-name', translate: 'no', text: '$' }),
          el('span', { class: 'tool-target', translate: 'no', text: message.command }),
          el('span', { class: 'tool-state', text: message.cancelled ? 'cancelled' : Number.isFinite(message.exitCode) && message.exitCode !== 0 ? `exit ${message.exitCode}` : 'done' })));
      if (lines.join('').trim()) tool.append(el('pre', { class: 'terminal bash-out', translate: 'no', text: lines.join('\n') }));
      if (total > BASH_LINES) tool.append(el('span', { class: 'small', text: `${fmt.num(total - BASH_LINES)} earlier lines not shown` }));
      target.append(tool);
      return items;
    }
    case 'compactionSummary':
    case 'branchSummary': {
      const label = message.role === 'compactionSummary' ? 'Earlier messages compacted' : 'Branch summary';
      target.append(el('div', { class: 'note' },
        el('details', { class: 'fold' }, el('summary', { text: `${label} · Show summary` }), el('div', { class: 'fold-body compaction-summary', text: message.summary || '' }))));
      return items;
    }
    default:
      return items;
  }
}

function flushAssistant(target, items, view, now) {
  const content = items.filter((item) => item.kind !== 'end');
  if (content.length) appendItems(target, content, view, now);
  const ends = items.filter((item) => item.kind === 'end');
  const last = ends.length ? ends[ends.length - 1].message : null;
  for (const { message } of ends) {
    if (message.stopReason === 'error') target.append(errorRow(message.errorMessage || 'The model request failed.', view.retry));
    else if (message.stopReason === 'aborted') target.append(el('div', { class: 'msg-stopped', text: 'Stopped.' }));
  }
  if (last && last.stopReason !== 'error') target.append(metaLine(last));
}

function renderNotes(target, notes) {
  for (const item of notes) {
    const node = el('div', { class: 'note', 'data-kind': item.kind }, el('span', { text: item.text }));
    if (item.summary) node.append(el('details', { class: 'fold' }, el('summary', { text: 'Show summary' }), el('div', { class: 'fold-body compaction-summary', text: item.summary })));
    target.append(node);
  }
}

function groupTurns(messages) {
  const turns = [];
  let current = null;
  messages.forEach((message, index) => {
    const starts = message.role === 'user'
      || message.role === 'bashExecution'
      || (message.role === 'custom' && message.customType === 'signal' && message.display !== false);
    if (starts || !current) {
      current = { start: index, end: index, messages: [] };
      turns.push(current);
    }
    current.messages.push(message);
    current.end = index;
  });
  return turns;
}

/** The live (streaming) assistant message: parts patched in place. */
function createLive(view) {
  const node = el('div', { class: 'live streaming' });
  let parts = [];
  let timestamp = null;
  return {
    node,
    update(message, now) {
      if (message.timestamp !== timestamp) {
        timestamp = message.timestamp;
        parts = [];
        node.replaceChildren();
      }
      const blocks = Array.isArray(message.content) ? message.content : [];
      blocks.forEach((block, index) => {
        let part = parts[index];
        const last = index === blocks.length - 1;
        if (!part || part.type !== block.type) {
          if (part) part.node.remove();
          part = { type: block.type };
          if (block.type === 'text') {
            part.node = el('div', { class: 'md' });
            part.renderer = createRenderer(part.node);
          } else if (block.type === 'thinking') {
            part.preview = el('div', { class: 'thinking-preview' });
            part.body = el('div', { class: 'thinking-body' });
            part.summary = el('summary', { text: 'Thinking…' });
            part.node = el('details', { class: 'fold' }, part.summary, el('div', { class: 'fold-body' }, part.body));
            part.wrap = el('div', null, part.node, part.preview);
            part.started = now;
          } else if (block.type === 'toolCall') {
            part.node = el('div');
          } else {
            part.node = el('div');
          }
          node.append(part.wrap || part.node);
          if (part.wrap) part.node = part.wrap;
          parts[index] = part;
        }
        if (block.type === 'text') part.renderer.update(block.text || '');
        else if (block.type === 'thinking') {
          const text = block.thinking || '';
          part.body.textContent = text;
          const key = blockKey(message, index);
          if (last) {
            part.preview.textContent = text.trim().split('\n').pop() || '';
            part.summary.textContent = 'Thinking…';
          } else {
            if (!thinkingMs.has(key)) thinkingMs.set(key, now - part.started);
            part.preview.textContent = '';
            part.summary.textContent = `Thought for ${fmt.duration(thinkingMs.get(key))}`;
          }
        } else if (block.type === 'toolCall') {
          const tool = view.resolveTool(block);
          if (!part.row || part.id !== block.id) {
            part.id = block.id;
            part.row = view.toolNode(tool, now);
            part.node.replaceChildren(part.row);
          }
        }
      });
      for (const stale of parts.slice(blocks.length)) stale.node.remove();
      parts = parts.slice(0, blocks.length);
    },
    finish(message, now) {
      const blocks = Array.isArray(message.content) ? message.content : [];
      blocks.forEach((block, index) => {
        const key = blockKey(message, index);
        const part = parts[index];
        if (block.type === 'thinking' && part && !thinkingMs.has(key)) thinkingMs.set(key, now - part.started);
      });
    },
  };
}

function render(root, ctx) {
  const list = el('ol', { class: 'transcript', 'aria-label': 'Conversation' });
  const scroller = el('div', { class: 'chat-scroll', tabindex: '-1' }, list);
  const latest = el('button', { type: 'button', class: 'latest', 'aria-label': 'Scroll to the latest message', text: '↓ Latest' });
  const dock = createDock(ctx);
  root.append(scroller, latest, dock.node);

  const view = {
    ctx,
    list,
    scroller,
    latest,
    dock,
    pinned: true,
    turnNodes: new Map(),
    toolRows: new Map(),
    results: new Map(),
    live: null,
    liveTimestamp: null,
    sessionId: null,
    tail: null,
    loadingTimer: 0,
    state: 'idle',
    resolveTool: null,
    toolNode: null,
    retry: null,
    unsubs: [],
  };

  view.resolveTool = (call) => {
    const session = view.ctx.state.session;
    const live = session && session.tools[call.id];
    const result = view.results.get(call.id);
    const tool = { id: call.id, name: call.name, args: call.arguments, status: 'waiting', startedAt: 0, endedAt: 0, partial: null, result: null };
    if (live) Object.assign(tool, live, { args: live.args || call.arguments, name: live.name || call.name });
    if (result) {
      tool.status = result.isError ? 'failed' : 'done';
      tool.result = { content: result.content, details: result.details };
      if (!tool.endedAt) tool.endedAt = result.timestamp;
    }
    if (tool.status === 'waiting' && !(session && session.turn.running)) tool.status = 'missing';
    return tool;
  };
  view.toolNode = (tool, now) => {
    const row = toolRow(view.sessionId, tool);
    row.patch(tool, now);
    view.toolRows.set(tool.id, row);
    return row.node;
  };
  view.retry = () => view.dock.retryLast();

  let viewportHeight = 0;
  const onScroll = () => {
    // A keyboard or Dock resize is not the reader scrolling away.
    if (scroller.clientHeight !== viewportHeight) {
      viewportHeight = scroller.clientHeight;
      if (view.pinned) {
        scroller.scrollTop = scroller.scrollHeight;
        return;
      }
    }
    const distance = scroller.scrollHeight - scroller.scrollTop - scroller.clientHeight;
    view.pinned = distance <= STICK_PX;
    latest.dataset.shown = view.pinned ? 'false' : 'true';
  };
  scroller.addEventListener('scroll', onScroll, { passive: true });
  latest.addEventListener('click', () => {
    const smooth = !matchMedia('(prefers-reduced-motion: reduce)').matches;
    scroller.scrollTo({ top: scroller.scrollHeight, behavior: smooth ? 'smooth' : 'instant' });
  });
  const follow = new ResizeObserver(() => {
    if (view.pinned) scroller.scrollTop = scroller.scrollHeight;
  });
  follow.observe(list);
  follow.observe(scroller);
  view.unsubs.push(() => follow.disconnect());

  const onKey = (event) => {
    if (!event.altKey || (event.key !== 'ArrowUp' && event.key !== 'ArrowDown')) return;
    const turns = [...list.querySelectorAll('.turn')];
    if (!turns.length) return;
    event.preventDefault();
    const top = scroller.getBoundingClientRect().top;
    const offsets = turns.map((turn) => turn.getBoundingClientRect().top - top);
    const target = event.key === 'ArrowUp'
      ? [...turns].reverse().find((_, index) => offsets[turns.length - 1 - index] < -4)
      : turns.find((_, index) => offsets[index] > 4);
    if (target) target.scrollIntoView({ block: 'start' });
  };
  document.addEventListener('keydown', onKey);
  view.unsubs.push(() => document.removeEventListener('keydown', onKey));

  root.chatView = view;
  update(root, ctx);
}

function showLoading(view) {
  if (view.state === 'loading') return;
  view.state = 'loading';
  view.turnNodes.clear();
  view.list.replaceChildren();
  clearTimeout(view.loadingTimer);
  view.loadingTimer = setTimeout(() => {
    if (view.state !== 'loading') return;
    const turn = el('li', { class: 'turn', 'aria-hidden': 'true' });
    turn.append(el('div', { class: 'msg-wrap' }, el('div', { class: 'msg-user', text: '\u00a0'.repeat(24) })), skeleton(4));
    view.list.replaceChildren(turn, el('li', { class: 'turn', 'aria-hidden': 'true' }, skeleton(3)));
  }, 150);
}

function turnSignature(turn, session, isLast, notes) {
  if (!isLast) return `${turn.messages.length}|${notes.length}`;
  const tools = [];
  for (const message of turn.messages) {
    if (message.role !== 'assistant' || !Array.isArray(message.content)) continue;
    for (const block of message.content) {
      if (block.type === 'toolCall') {
        const live = session.tools[block.id];
        tools.push(`${block.id}:${live ? live.status : '-'}`);
      }
    }
  }
  return `${turn.messages.length}|${notes.length}|${session.turn.running}|${tools.join(',')}|${session.live ? 1 : 0}`;
}

function update(root, ctx) {
  const view = root.chatView;
  if (!view) return;
  view.ctx = ctx;
  const { state } = ctx;
  const now = Date.now();
  const wanted = ctx.route.sessionId;
  const session = state.session && (!wanted || state.session.id === wanted) ? state.session : null;
  view.dock.update(ctx, session);

  if (!session) {
    if (state.opening && state.opening.error && (!wanted || state.opening.id === wanted)) {
      view.state = 'error';
      clearTimeout(view.loadingTimer);
      view.list.replaceChildren(el('li', null, empty({
        title: 'This session did not open.',
        body: state.opening.error,
        action: { label: 'Try again', onClick: () => window.dispatchEvent(new CustomEvent('eukhe:reopen')) },
      })));
      return;
    }
    showLoading(view);
    return;
  }
  clearTimeout(view.loadingTimer);
  if (view.sessionId !== session.id) {
    view.sessionId = session.id;
    view.turnNodes.clear();
    view.list.replaceChildren();
    view.live = null;
    view.pinned = true;
  }
  view.state = 'ready';
  const linkDown = state.link.status !== 'open' || state.link.catchingUp;
  view.list.dataset.dim = linkDown ? 'true' : 'false';

  view.results.clear();
  for (const message of session.messages) if (message.role === 'toolResult') view.results.set(message.toolCallId, message);

  const turns = groupTurns(session.messages);
  if (!turns.length && !session.live && !session.pending.length) {
    if (!view.list.querySelector('.chat-empty')) {
      view.turnNodes.clear();
      const suggestions = el('div', { class: 'suggestions' }, SUGGESTIONS.map((text) => button({ label: text, onClick: () => view.dock.fill(text) })));
      view.list.replaceChildren(el('li', { class: 'chat-empty' },
        el('h1', { class: 'chat-empty-title', text: 'What should eukhe do?' }),
        el('p', { class: 'chat-empty-body', text: 'No messages yet. Ask something below ↓' }),
        suggestions));
    }
    return;
  }
  view.list.querySelector('.chat-empty')?.remove();

  const notesByTurn = new Map();
  for (const item of session.notes) {
    const owner = turns.findLast((turn) => turn.start < Math.max(item.index, 1)) || turns[turns.length - 1];
    const key = owner ? owner.start : -1;
    if (!notesByTurn.has(key)) notesByTurn.set(key, []);
    notesByTurn.get(key).push(item);
  }

  const seen = new Set();
  let previous = null;
  turns.forEach((turn, index) => {
    const isLast = index === turns.length - 1;
    const notes = notesByTurn.get(turn.start) || [];
    const sig = turnSignature(turn, session, isLast, notes);
    let cached = view.turnNodes.get(turn.start);
    if (!cached || cached.sig !== sig) {
      const node = el('li', { class: `turn${isLast ? '' : ' settled'}`, 'data-start': String(turn.start) });
      let items = [];
      for (const message of turn.messages) {
        // Anything shown between assistant messages closes their run.
        if (message.role !== 'assistant' && message.role !== 'toolResult' && items.length) {
          flushAssistant(node, items, view, now);
          items = [];
        }
        items = renderMessage(node, message, view, now, items);
      }
      flushAssistant(node, items, view, now);
      renderNotes(node, notes);
      if (cached) cached.node.replaceWith(node);
      else if (previous) previous.after(node);
      else view.list.prepend(node);
      cached = { sig, node };
      view.turnNodes.set(turn.start, cached);
      if (isLast && view.live) node.append(view.live.node);
    }
    seen.add(turn.start);
    previous = cached.node;
  });
  for (const [key, cached] of view.turnNodes) {
    if (key !== 'pending' && !seen.has(key)) {
      cached.node.remove();
      view.turnNodes.delete(key);
    }
  }

  // The streaming message lives at the end of the last turn.
  const lastTurn = previous;
  if (session.live) {
    if (!view.live) view.live = createLive(view);
    if (view.live.node.parentNode !== lastTurn) lastTurn.append(view.live.node);
    view.live.update(session.live, now);
  } else if (view.live) {
    const settled = session.messages[session.messages.length - 1];
    if (settled) view.live.finish(settled, now);
    view.live.node.remove();
    view.live = null;
  }

  // Optimistic sends while idle: a user row tagged Sending… / Not sent.
  const idlePending = session.pending.filter((item) => item.mode === 'followUp' && !item.queued);
  const pendingSig = idlePending.map((item) => `${item.admissionId}:${item.status}`).join(',');
  let pendingRow = view.turnNodes.get('pending');
  if (!pendingRow || pendingRow.sig !== pendingSig) {
    const node = el('li', { class: 'turn pending-turn' });
    for (const item of idlePending) {
      node.append(userBubble(item.text, {
        state: item.status === 'failed' ? `Not sent · ${item.error || 'the daemon refused it'}` : 'Sending…',
        actions: item.status === 'failed' ? [button({ label: 'Retry', kind: 'primary', onClick: () => view.dock.resend(item) }), button({ label: 'Edit', onClick: () => view.dock.edit(item) })] : null,
      }));
    }
    if (pendingRow) pendingRow.node.remove();
    pendingRow = { sig: pendingSig, node };
    view.turnNodes.set('pending', pendingRow);
  }
  if (idlePending.length) view.list.append(pendingRow.node);
  else pendingRow.node.remove();

  // Running tools: elapsed words and live tails, in place.
  for (const [id, row] of view.toolRows) {
    if (!row.node.isConnected) {
      view.toolRows.delete(id);
      continue;
    }
    const tool = session.tools[id];
    if (tool) row.patch(view.resolveTool({ id, name: tool.name, arguments: tool.args }), now);
  }
  if (view.pinned) view.scroller.scrollTop = view.scroller.scrollHeight;
}

function dispose(root) {
  const view = root.chatView;
  if (!view) return;
  clearTimeout(view.loadingTimer);
  for (const off of view.unsubs) off();
  view.dock.dispose();
  root.chatView = null;
}

export default definePage({
  id: 'chat',
  title: () => '',
  render,
  update,
  dispose,
});
