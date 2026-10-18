// The conversation: turns (user bubble, then the assistant's thinking,
// tools and text in order, then a meta row), the streaming message (only
// its last markdown block re-renders), the one activity line, the
// approval block, pending and queued messages, and the "Latest ↓" button.
// Settled turns are cached by their start index and rebuilt only when
// their signature changes; running tool rows are patched in place.

import { el, icon, textButton, copyButton, button } from './ui.js';
import { createRenderer, markdown } from './markdown.js';
import { contentText, withoutSignalRules, toolTarget, messageSpeed, derivePhase, effectWords, basename } from './turn.js';
import { answerApproval } from './approvals.js';
import { run } from './link.js';
import { fmt } from './format.js';

const STICK_PX = 48;
const TAIL_LINES = 3;

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
      class: 'bubble-image',
      src: `data:${block.mimeType};base64,${block.data}`,
      alt: 'Attached image',
      loading: 'lazy',
      decoding: 'async',
    }));
}

function outputText(output) {
  if (!output) return '';
  if (typeof output === 'string') return output;
  return contentText(output.content || output);
}

function argsText(args) {
  if (args === null || args === undefined) return '';
  if (typeof args === 'string') return args;
  if (typeof args === 'object') {
    const keys = Object.keys(args);
    if (keys.length === 1 && typeof args[keys[0]] === 'string') return args[keys[0]];
  }
  return JSON.stringify(args, null, 2);
}

/** A user bubble (right-aligned); `label` and `actions` sit under it. */
function bubble(text, { images = [], origin = null, pending = false, label = null, actions = [] } = {}) {
  const body = el('div', { class: 'bubble', 'data-pending': pending ? 'true' : null });
  if (origin) body.append(el('span', { class: 'bubble-origin', text: origin }));
  if (images.length) body.append(el('div', { class: 'bubble-images' }, images));
  if (text) body.append(el('p', { class: 'bubble-text', text }));
  const node = el('div', { class: 'bubble-row' }, body);
  if (label || actions.length) {
    const meta = el('div', { class: 'bubble-meta' });
    if (label) meta.append(el('span', { text: label }));
    for (const action of actions) meta.append(action);
    node.append(meta);
  }
  return node;
}

function mono(title, getText) {
  const pre = el('pre', { class: 'mono-text', tabindex: '0', translate: 'no' });
  const node = el('div', { class: 'mono-block' },
    el('div', { class: 'mono-head' }, el('span', { text: title }), copyButton(() => pre.textContent)),
    pre);
  node.setText = (text) => {
    if (pre.textContent !== text) pre.textContent = text;
  };
  node.setText(getText());
  return node;
}

/** Status text of a tool row: `0.4 s`, `Failed`, or elapsed while running. */
function toolState(tool, now) {
  switch (tool.status) {
    case 'running':
      return fmt.clock(now - tool.startedAt);
    case 'failed':
      return 'Failed';
    case 'stopped':
      return 'Stopped';
    case 'done':
      return tool.startedAt && tool.endedAt && tool.endedAt >= tool.startedAt ? fmt.duration(tool.endedAt - tool.startedAt) : '';
    case 'waiting':
      return 'Waiting';
    default:
      return '';
  }
}

export function createConversation(app) {
  const transcript = el('div', { class: 'transcript', role: 'log', 'aria-label': 'Conversation', 'aria-live': 'off' });
  const tailArea = el('div', { class: 'tail-area' });
  const activityWord = el('span', { class: 'activity-word shimmer' });
  const activityCancel = textButton('Cancel', () => cancelActivity());
  const activity = el('div', { class: 'activity', role: 'status' }, activityWord, activityCancel);
  const approvalHost = el('div', { class: 'approval-host' });
  const pendingHost = el('div', { class: 'pending-host' });
  const noticeText = el('span');
  const notice = el('p', { class: 'notice', role: 'alert' }, noticeText, textButton('Dismiss', () => {
    notice.hidden = true;
  }));
  notice.hidden = true;
  tailArea.append(activity, approvalHost, pendingHost, notice);
  const stateHost = el('div', { class: 'conversation-state' });
  const column = el('div', { class: 'column' }, transcript, tailArea);
  const scroller = el('div', { class: 'scroller', tabindex: '-1' }, stateHost, column);
  const latest = el('button', { type: 'button', class: 'latest', 'aria-label': 'Scroll to the latest message' }, 'Latest ↓');
  latest.hidden = true;
  const node = el('div', { class: 'stage' }, scroller, latest);

  const view = {
    sessionId: null,
    pinned: true,
    turns: new Map(),
    toolRows: new Map(),
    expanded: new Set(),
    open: new Set(),
    results: new Map(),
    live: null,
    phaseKey: '',
    approvalSig: '',
    pendingSig: '',
    stateKey: '',
    state: null,
    lastPhase: null,
  };

  function cancelActivity() {
    const phase = view.lastPhase;
    if (!phase) return;
    const command = phase.action === 'cancelRetry' ? { type: 'abort_retry' } : phase.action === 'cancelCompaction' ? { type: 'abort_compaction' } : null;
    if (command) run(command).catch((error) => app.notice(error.message));
  }

  // ------------------------------------------------------------ scroll --
  const toBottom = () => {
    scroller.scrollTop = scroller.scrollHeight;
  };
  scroller.addEventListener('scroll', () => {
    const distance = scroller.scrollHeight - scroller.scrollTop - scroller.clientHeight;
    view.pinned = distance <= STICK_PX;
    latest.hidden = view.pinned || !view.sessionId;
  }, { passive: true });
  latest.addEventListener('click', () => {
    const smooth = !matchMedia('(prefers-reduced-motion: reduce)').matches;
    view.pinned = true;
    scroller.scrollTo({ top: scroller.scrollHeight, behavior: smooth ? 'smooth' : 'instant' });
  });
  const follow = new ResizeObserver(() => {
    if (view.pinned) toBottom();
  });
  follow.observe(column);
  follow.observe(scroller);

  // ------------------------------------------------------------- tools --
  function resolveTool(call) {
    const session = view.state.session;
    const live = session && session.tools[call.id];
    const result = view.results.get(call.id);
    const tool = { id: call.id, name: call.name, args: call.arguments, status: 'waiting', startedAt: 0, endedAt: 0, partial: null, result: null };
    if (live) Object.assign(tool, live, { args: live.args || call.arguments, name: live.name || call.name });
    if (result) {
      tool.status = result.isError ? 'failed' : 'done';
      tool.result = { content: result.content, details: result.details };
      if (!tool.endedAt) tool.endedAt = result.timestamp;
      if (Number.isFinite(result.durationMs)) {
        tool.startedAt = tool.startedAt || 0;
        tool.durationMs = result.durationMs;
      }
    }
    if (tool.status === 'waiting' && !(session && session.turn.running)) tool.status = 'stopped';
    return tool;
  }

  /** One tool row with its details (args, output) and live tail, patchable. */
  function toolRow(tool) {
    const state = el('span', { class: 'tool-state' });
    const head = el('button', { type: 'button', class: 'tool-row', 'aria-expanded': 'false' },
      el('span', { class: 'tool-name', translate: 'no', text: tool.name }),
      el('span', { class: 'tool-target', translate: 'no', text: toolTarget(tool.args) }),
      state);
    const tail = el('pre', { class: 'tool-tail', 'aria-hidden': 'true', translate: 'no' });
    const details = el('div', { class: 'tool-details' });
    const node = el('div', { class: 'tool', 'data-status': tool.status }, head);
    let current = tool;
    let argsBlock = null;
    let outBlock = null;
    const paintDetails = () => {
      if (!argsBlock) {
        argsBlock = mono('Arguments', () => argsText(current.args));
        outBlock = mono('Output', () => '');
        details.append(argsBlock, outBlock);
      }
      argsBlock.setText(argsText(current.args));
      const output = current.result ? outputText(current.result) : current.partial ? outputText(current.partial) : '';
      outBlock.setText(output || (current.status === 'running' ? '' : 'No output.'));
    };
    const setOpen = (open) => {
      head.setAttribute('aria-expanded', open ? 'true' : 'false');
      if (open) {
        paintDetails();
        node.append(details);
        view.expanded.add(current.id);
      } else {
        details.remove();
        view.expanded.delete(current.id);
      }
      patch(current, Date.now());
    };
    head.addEventListener('click', () => setOpen(head.getAttribute('aria-expanded') !== 'true'));
    let lastTail = null;
    const patch = (next, now) => {
      current = next;
      node.dataset.status = next.status;
      const word = next.durationMs && next.status === 'done' ? fmt.duration(next.durationMs) : toolState(next, now);
      if (state.textContent !== word) state.textContent = word;
      const open = head.getAttribute('aria-expanded') === 'true';
      if (open) paintDetails();
      const live = !open && next.status === 'running' && next.partial ? outputText(next.partial) : '';
      if (live !== lastTail) {
        lastTail = live;
        if (live) {
          tail.textContent = live.replace(/\s+$/, '').split('\n').slice(-TAIL_LINES).join('\n');
          if (!tail.isConnected) node.append(tail);
        } else tail.remove();
      }
    };
    patch(tool, Date.now());
    if (view.expanded.has(tool.id)) setOpen(true);
    view.toolRows.set(tool.id, { node, patch });
    return node;
  }

  function disclosure(key, summaryParts, body, { className = '' } = {}) {
    const summary = el('summary', { class: 'disclosure-summary' });
    for (const part of summaryParts) summary.append(part);
    summary.append(icon('chevron'));
    const details = el('details', { class: `disclosure${className ? ` ${className}` : ''}` }, summary, body);
    if (view.open.has(key)) details.open = true;
    details.addEventListener('toggle', () => {
      if (details.open) view.open.add(key);
      else view.open.delete(key);
    });
    return details;
  }

  function thinkingNode(text, key, live = false) {
    const known = thinkingMs.get(key);
    const label = live ? 'Thinking' : known ? `Thought for ${fmt.duration(known)}` : 'Thoughts';
    const body = el('div', { class: 'thinking-text', text });
    const node = disclosure(`think:${key}`, [el('span', { class: 'disclosure-label', text: label })], body, { className: 'thinking' });
    node.setLabel = (next) => {
      const span = node.querySelector('.disclosure-label');
      if (span.textContent !== next) span.textContent = next;
    };
    node.setText = (next) => {
      if (body.textContent !== next) body.textContent = next;
    };
    return node;
  }

  function toolGroup(tools, key) {
    const failed = tools.filter((tool) => tool.status === 'failed').length;
    const parts = [el('span', { class: 'disclosure-label', text: `Used ${fmt.num(tools.length)} ${tools.length === 1 ? 'tool' : 'tools'}` })];
    if (failed) parts.push(el('span', { class: 'disclosure-extra', text: `${fmt.num(failed)} failed` }));
    const rows = el('div', { class: 'tool-list' }, tools.map((tool) => toolRow(tool)));
    return disclosure(`tools:${key}`, parts, rows, { className: 'tools' });
  }

  /** Assistant items in order; consecutive settled tool calls fold into one disclosure. */
  function appendItems(target, items, settled) {
    let runTools = [];
    let runKey = '';
    const flush = () => {
      if (!runTools.length) return;
      const allSettled = settled && runTools.every((tool) => tool.status !== 'running' && tool.status !== 'waiting');
      if (allSettled) target.append(toolGroup(runTools, runKey));
      else target.append(el('div', { class: 'tool-list' }, runTools.map((tool) => toolRow(tool))));
      runTools = [];
    };
    for (const item of items) {
      if (item.kind === 'tool') {
        if (!runTools.length) runKey = item.tool.id;
        runTools.push(item.tool);
        continue;
      }
      flush();
      if (item.kind === 'text') target.append(markdown(item.text));
      else if (item.kind === 'thinking') target.append(thinkingNode(item.text, item.key));
    }
    flush();
  }

  function assistantItems(message) {
    const items = [];
    const blocks = Array.isArray(message.content) ? message.content : [{ type: 'text', text: String(message.content || '') }];
    blocks.forEach((block, index) => {
      if (block.type === 'text' && block.text && block.text.trim()) items.push({ kind: 'text', text: block.text });
      else if (block.type === 'thinking' && (block.thinking || '').trim()) items.push({ kind: 'thinking', text: block.thinking, key: blockKey(message, index) });
      else if (block.type === 'toolCall') items.push({ kind: 'tool', tool: resolveTool(block) });
    });
    return items;
  }

  function groupTurns(messages) {
    const turns = [];
    let turn = null;
    messages.forEach((message, index) => {
      const starts = message.role === 'user'
        || message.role === 'bashExecution'
        || (message.role === 'custom' && message.customType === 'signal' && message.display !== false);
      if (starts || !turn) {
        turn = { start: index, messages: [] };
        turns.push(turn);
      }
      turn.messages.push(message);
    });
    return turns;
  }

  function turnText(turn) {
    return turn.messages
      .filter((message) => message.role === 'assistant')
      .map((message) => contentText(message.content))
      .filter(Boolean)
      .join('\n\n');
  }

  function metaRow(turn, isLast, failed) {
    const last = [...turn.messages].reverse().find((message) => message.role === 'assistant');
    if (!last) return null;
    const left = el('div', { class: 'meta-left' });
    const text = turnText(turn);
    if (text) left.append(copyButton(() => text));
    if (isLast && failed) left.append(textButton('Retry', () => app.retryLast()));
    const right = el('div', { class: 'meta-right' });
    const speed = messageSpeed(last);
    if (speed && speed.rate) right.append(el('span', { class: 'fig', text: fmt.rate(speed.rate) }));
    if (last.timestamp) right.append(el('span', { class: 'fig', text: fmt.time(last.timestamp) }));
    return el('div', { class: 'meta' }, left, right);
  }

  function noteNode(item) {
    const node = el('p', { class: 'turn-note', 'data-kind': item.kind, text: item.text });
    return node;
  }

  /** Build one turn's node. */
  function buildTurn(turn, isLast, notes, session) {
    const node = el('article', { class: `turn${isLast ? ' last' : ''}` });
    const answer = el('div', { class: 'answer' });
    let items = [];
    let lastAssistant = null;
    const flush = () => {
      if (items.length) appendItems(answer, items, !(isLast && session.turn.running));
      items = [];
    };
    // Consecutive identical notes (the same settings error twice) show once.
    let lastNote = null;
    for (const message of turn.messages) {
      if (message.role !== 'custom' && message.role !== 'toolResult') lastNote = null;
      switch (message.role) {
        case 'user': {
          flush();
          const text = withoutSignalRules(contentText(message.content));
          const images = imageNodes(message.content);
          if (text.trim() || images.length) node.append(bubble(text, { images }));
          break;
        }
        case 'custom': {
          if (message.display === false) break;
          const text = contentText(message.content);
          if (!text.trim()) break;
          flush();
          if (message.customType === 'signal') node.append(bubble(text, { origin: 'From Signal' }));
          else {
            const noteKey = `${message.customType}\n${text}`;
            if (noteKey === lastNote) break;
            lastNote = noteKey;
            const words = String(message.customType || 'note').split('.').pop().replace(/[_-]+/g, ' ').trim() || 'Note';
            const body = markdown(text);
            answer.append(disclosure(`custom:${message.timestamp}`, [el('span', { class: 'disclosure-label', text: words.charAt(0).toUpperCase() + words.slice(1) })], body, { className: 'custom' }));
          }
          break;
        }
        case 'assistant':
          items.push(...assistantItems(message));
          lastAssistant = message;
          break;
        case 'bashExecution': {
          flush();
          const tool = {
            id: `bash:${message.timestamp}`,
            name: 'shell',
            args: { command: message.command },
            status: message.cancelled ? 'stopped' : Number.isFinite(message.exitCode) && message.exitCode !== 0 ? 'failed' : 'done',
            result: { content: [{ type: 'text', text: message.output || '' }] },
            startedAt: 0,
            endedAt: 0,
          };
          node.append(el('div', { class: 'tool-list' }, toolRow(tool)));
          break;
        }
        case 'compactionSummary':
        case 'branchSummary': {
          flush();
          const label = message.role === 'compactionSummary' ? 'Earlier messages compacted' : 'Branch summary';
          answer.append(disclosure(`summary:${message.timestamp}`, [el('span', { class: 'disclosure-label', text: label })], el('div', { class: 'thinking-text', text: message.summary || '' }), { className: 'custom' }));
          break;
        }
        default:
          break;
      }
    }
    flush();
    node.append(answer);
    if (isLast && session.live) answer.append(liveNode().node);
    const runningHere = isLast && session.turn.running;
    let failed = false;
    if (lastAssistant && !runningHere) {
      if (lastAssistant.stopReason === 'error') {
        failed = true;
        answer.append(el('div', { class: 'turn-error', role: 'alert' },
          el('p', { text: `Something went wrong. ${lastAssistant.errorMessage || 'The model request failed.'}` }),
          isLast ? textButton('Retry', () => app.retryLast(), { kind: 'primary' }) : null));
      } else if (lastAssistant.stopReason === 'aborted') {
        answer.append(el('p', { class: 'turn-stopped', text: 'Stopped' }));
      }
    }
    if (isLast && !runningHere && session.turn.error && !failed) {
      failed = true;
      answer.append(el('div', { class: 'turn-error', role: 'alert' },
        el('p', { text: `Something went wrong. ${session.turn.error}` }),
        textButton('Retry', () => app.retryLast(), { kind: 'primary' })));
    }
    for (const item of notes) answer.append(noteNode(item));
    if (!runningHere) {
      const meta = metaRow(turn, isLast, failed);
      if (meta) answer.append(meta);
    }
    if (!answer.childElementCount) answer.remove();
    return node;
  }

  // --------------------------------------------------- live message --
  function liveNode() {
    if (view.live) return view.live;
    const node = el('div', { class: 'live' });
    let parts = [];
    let timestamp = null;
    view.live = {
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
            part = { type: block.type, started: now };
            if (block.type === 'text') {
              part.node = el('div', { class: 'md' });
              part.renderer = createRenderer(part.node);
            } else if (block.type === 'thinking') {
              part.node = thinkingNode('', blockKey(message, index), true);
            } else if (block.type === 'toolCall') {
              part.node = el('div', { class: 'tool-list' });
            } else part.node = el('div');
            node.append(part.node);
            parts[index] = part;
          }
          if (block.type === 'text') part.renderer.update(block.text || '');
          else if (block.type === 'thinking') {
            const key = blockKey(message, index);
            part.node.setText(block.thinking || '');
            if (!last && !thinkingMs.has(key)) thinkingMs.set(key, now - part.started);
            part.node.setLabel(last ? 'Thinking' : `Thought for ${fmt.duration(thinkingMs.get(key))}`);
          } else if (block.type === 'toolCall' && block.id && part.id !== block.id) {
            part.id = block.id;
            part.node.replaceChildren(toolRow(resolveTool(block)));
          }
        });
        for (const stale of parts.slice(blocks.length)) stale.node.remove();
        parts = parts.slice(0, blocks.length);
      },
      finish(message, now) {
        const blocks = Array.isArray(message.content) ? message.content : [];
        blocks.forEach((block, index) => {
          const key = blockKey(message, index);
          if (block.type === 'thinking' && parts[index] && !thinkingMs.has(key)) thinkingMs.set(key, now - parts[index].started);
        });
      },
    };
    return view.live;
  }

  function turnSignature(turn, session, isLast, notes) {
    if (!isLast) return `${turn.messages.length}|${notes.length}`;
    const tools = [];
    for (const message of turn.messages) {
      if (message.role !== 'assistant' || !Array.isArray(message.content)) continue;
      for (const block of message.content) {
        if (block.type === 'toolCall') {
          const live = session.tools[block.id];
          tools.push(`${block.id}:${live ? live.status : '-'}:${view.results.has(block.id) ? 1 : 0}`);
        }
      }
    }
    return `${turn.messages.length}|${notes.length}|${session.turn.running}|${session.turn.error || ''}|${tools.join(',')}|${session.live ? 1 : 0}`;
  }

  // ------------------------------------------------------- the tail --
  function paintActivity(phase) {
    view.lastPhase = phase;
    const key = phase.running ? `${phase.label}|${phase.action}` : '';
    if (key === view.phaseKey) return;
    view.phaseKey = key;
    activity.hidden = !key;
    activityWord.textContent = key ? phase.label : '';
    activityCancel.hidden = !phase.action;
  }

  function paintApprovals(state) {
    const sig = state.approvals.map((item) => `${item.requestId}:${item.status}`).join(',');
    if (sig === view.approvalSig) return;
    view.approvalSig = sig;
    const nodes = [];
    for (const item of state.approvals) {
      if (item.status === 'elsewhere') {
        nodes.push(el('p', { class: 'turn-note', text: 'Answered in another window' }));
        continue;
      }
      const busy = item.status === 'answering';
      const deny = button('Deny', () => answerApproval(item.requestId, 'deny'), { className: 'approval-deny' });
      const approve = button('Approve', () => answerApproval(item.requestId, 'approve'), { className: 'approval-approve' });
      deny.disabled = busy;
      approve.disabled = busy;
      const block = el('div', { class: 'approval', role: 'group', tabindex: '-1', 'aria-label': 'Approve this command?', 'aria-keyshortcuts': 'A D' },
        el('p', { class: 'approval-title', text: 'Approve this command?' }),
        el('pre', { class: 'approval-command', translate: 'no', text: item.command }),
        el('p', { class: 'approval-effect', text: effectWords(item.effect) }),
        el('div', { class: 'approval-actions' }, deny, approve));
      block.addEventListener('keydown', (event) => {
        if (event.target instanceof HTMLButtonElement && event.key === 'Enter') return;
        const key = event.key.toLowerCase();
        if (key === 'a') approve.click();
        else if (key === 'd') deny.click();
      });
      nodes.push(block);
    }
    approvalHost.replaceChildren(...nodes);
  }

  function paintPending(session) {
    const queue = session.queue || { steering: [], followUps: [] };
    const steering = queue.steering || [];
    const followUps = queue.followUps || [];
    const sig = JSON.stringify([session.pending.map((item) => [item.admissionId, item.status, item.text]), steering.map((item) => item.text), followUps.map((item) => item.text)]);
    if (sig === view.pendingSig) return;
    view.pendingSig = sig;
    const nodes = [];
    for (const item of session.pending) {
      if (item.status === 'failed') {
        nodes.push(bubble(item.text, {
          pending: true,
          label: 'Not sent',
          actions: [textButton('Retry', () => app.resend(item), { kind: 'primary' }), textButton('Edit', () => app.editPending(item))],
        }));
      } else {
        nodes.push(bubble(item.text, { pending: true, label: item.status === 'held' ? 'Sends when eukhe is back' : 'Sending' }));
      }
    }
    steering.forEach((item, index) => nodes.push(bubble(item.text, {
      pending: true,
      label: 'Steering, sends at the next step',
      actions: [textButton('Edit', () => app.editQueued('steering', index, item.text)), textButton('Remove', () => app.removeQueued('steering', index, item.text))],
    })));
    followUps.forEach((item, index) => nodes.push(bubble(item.text, {
      pending: true,
      label: 'Queued, sends after this reply',
      actions: [textButton('Edit', () => app.editQueued('followUp', index, item.text)), textButton('Remove', () => app.removeQueued('followUp', index, item.text))],
    })));
    pendingHost.replaceChildren(...nodes);
  }

  // ------------------------------------------------------ the states --
  function showState(key, build) {
    if (view.stateKey === key) return;
    view.stateKey = key;
    stateHost.replaceChildren(...(build ? [build()] : []));
    stateHost.hidden = !build;
    node.dataset.state = key || 'chat';
  }

  function reset(sessionId) {
    view.sessionId = sessionId;
    view.turns.clear();
    view.toolRows.clear();
    view.expanded.clear();
    view.open.clear();
    view.live = null;
    view.pinned = true;
    view.phaseKey = '';
    view.approvalSig = '';
    view.pendingSig = '';
    transcript.replaceChildren();
    pendingHost.replaceChildren();
    approvalHost.replaceChildren();
    activity.hidden = true;
    latest.hidden = true;
  }

  function update(state) {
    view.state = state;
    const now = Date.now();
    const { session } = state;
    const wanted = app.routeSessionId();
    const shown = session && (!wanted || session.id === wanted) ? session : null;

    if (!shown) {
      if (view.sessionId) reset(null);
      if (state.opening && state.opening.error) {
        showState(`error:${state.opening.error}`, () => el('div', { class: 'center-state' },
          el('p', { class: 'center-title', text: 'This chat did not open.' }),
          el('p', { class: 'center-body', text: state.opening.error }),
          textButton('Try again', () => app.reopen(), { kind: 'primary' })));
      } else if (!state.link.everOpen && state.link.status !== 'open' && state.link.status !== 'connecting') {
        showState('offline', () => el('div', { class: 'center-state' },
          el('p', { class: 'center-title', text: 'eukhe is not reachable' }),
          el('p', { class: 'center-body', text: 'This page connects on its own once it is.' })));
      } else {
        showState('loading', null);
      }
      return;
    }
    if (view.sessionId !== shown.id) reset(shown.id);

    view.results.clear();
    for (const message of shown.messages) if (message.role === 'toolResult') view.results.set(message.toolCallId, message);
    const turns = groupTurns(shown.messages);
    const empty = !turns.length && !shown.live && !shown.pending.length && !(shown.queue && shown.queue.queuedCount);
    if (empty) {
      const folder = basename(shown.state && shown.state.cwd);
      showState(`empty:${folder}`, () => el('div', { class: 'center-state empty-chat' },
        el('h1', { class: 'center-title', text: 'What should eukhe do?' }),
        folder ? el('p', { class: 'center-body', text: `in ${folder}` }) : null));
    } else showState('', null);
    node.dataset.linkDown = state.link.status === 'open' ? 'false' : 'true';

    const notesByTurn = new Map();
    for (const item of shown.notes) {
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
      const sig = turnSignature(turn, shown, isLast, notes);
      let cached = view.turns.get(turn.start);
      if (!cached || cached.sig !== sig) {
        const built = buildTurn(turn, isLast, notes, shown);
        if (cached) cached.node.replaceWith(built);
        else if (previous) previous.after(built);
        else transcript.prepend(built);
        cached = { sig, node: built };
        view.turns.set(turn.start, cached);
      }
      cached.node.classList.toggle('last', isLast);
      seen.add(turn.start);
      previous = cached.node;
    });
    for (const [key, cached] of view.turns) {
      if (!seen.has(key)) {
        cached.node.remove();
        view.turns.delete(key);
      }
    }

    if (shown.live) {
      const live = liveNode();
      const answer = previous && previous.querySelector('.answer');
      const host = answer || previous;
      if (host && live.node.parentNode !== host) host.append(live.node);
      live.update(shown.live, now);
    } else if (view.live) {
      const settled = shown.messages[shown.messages.length - 1];
      if (settled) view.live.finish(settled, now);
      view.live.node.remove();
      view.live = null;
    }

    for (const [id, row] of view.toolRows) {
      if (!row.node.isConnected) {
        view.toolRows.delete(id);
        continue;
      }
      const tool = shown.tools[id];
      if (tool) row.patch(resolveTool({ id, name: tool.name, arguments: tool.args }), now);
    }

    paintActivity(derivePhase(state, now, fmt));
    paintApprovals(state);
    paintPending(shown);
    if (view.pinned) toBottom();
  }

  return {
    node,
    update,
    notice(text) {
      noticeText.textContent = text;
      notice.hidden = false;
      if (view.pinned) toBottom();
    },
    scrollToEnd() {
      view.pinned = true;
      toBottom();
    },
  };
}
