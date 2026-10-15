// eukhe dashboard: the CLI's root session and its chat memory in a
// browser tab. Plain JS, no build step. One WebSocket to the dashboard
// server bridges the tab to the eukhe daemon (see src/protocol.rs).
'use strict';

const $ = (id) => document.getElementById(id);

/** A new element with an optional class and text. */
function el(tag, className, text) {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text !== undefined && text !== null) node.textContent = text;
  return node;
}

const SESSION_KEY = 'eukhe.dashboard.session';
const SIGNAL_RULES = '[Signal reply rules:';

// ---------------------------------------------------------------- link --

/** The tab's socket: numbered requests, pushed frames, reconnects. */
class Link {
  constructor(onFrame, onState) {
    this.onFrame = onFrame;
    this.onState = onState;
    this.nextId = 1;
    this.pending = new Map();
    this.delay = 500;
    this.socket = null;
  }

  connect() {
    const url = new URL('api/ws', location.href);
    url.protocol = location.protocol === 'https:' ? 'wss:' : 'ws:';
    url.hash = '';
    url.search = '';
    const socket = new WebSocket(url);
    this.socket = socket;
    this.onState('connecting');
    socket.addEventListener('open', () => {
      this.delay = 500;
      this.onState('open');
    });
    socket.addEventListener('message', (event) => this.receive(event.data));
    socket.addEventListener('close', () => {
      if (this.socket !== socket) return;
      this.socket = null;
      for (const { reject } of this.pending.values()) reject(new Error('disconnected'));
      this.pending.clear();
      this.onState('offline');
      setTimeout(() => this.connect(), this.delay);
      this.delay = Math.min(this.delay * 2, 5000);
    });
  }

  receive(text) {
    let frame;
    try {
      frame = JSON.parse(text);
    } catch {
      return;
    }
    if (frame.type === 'reply' || frame.type === 'failure') {
      const waiter = this.pending.get(frame.id);
      if (!waiter) return;
      this.pending.delete(frame.id);
      if (frame.type === 'reply') waiter.resolve(frame.data);
      else waiter.reject(new Error(frame.error));
      return;
    }
    this.onFrame(frame);
  }

  request(op, fields = {}) {
    const socket = this.socket;
    if (!socket || socket.readyState !== WebSocket.OPEN) {
      return Promise.reject(new Error('not connected'));
    }
    const id = this.nextId++;
    return new Promise((resolve, reject) => {
      this.pending.set(id, { resolve, reject });
      socket.send(JSON.stringify({ id, op, ...fields }));
    });
  }
}

// --------------------------------------------------------------- text --

/** Plain text of a message content (a string, or blocks). */
function contentText(content) {
  if (typeof content === 'string') return content;
  if (!Array.isArray(content)) return '';
  return content
    .map((block) => (block && block.type === 'text' ? block.text : block && block.type === 'image' ? '[image]' : ''))
    .filter(Boolean)
    .join('\n\n');
}

/** A tool output's text (`{ content: [...] }`, a string, or JSON). */
function outputText(output) {
  if (output === null || output === undefined) return '';
  if (typeof output === 'string') return output;
  if (Array.isArray(output.content)) return contentText(output.content);
  if (Array.isArray(output)) return contentText(output);
  return JSON.stringify(output, null, 2);
}

/** A user prompt without the Signal gateway's reply rules. */
function withoutSignalRules(text) {
  if (!text.startsWith(SIGNAL_RULES)) return text;
  const end = text.indexOf(']');
  return end < 0 ? text : text.slice(end + 1).trimStart();
}

/** Inline markdown (code, bold, links) as DOM nodes; text stays text. */
function inline(text, parent) {
  const pattern = /(`[^`\n]+`)|(\*\*[^*\n]+\*\*)|(https?:\/\/[^\s<>()]+[^\s<>().,;:!?'"])/g;
  let last = 0;
  for (const match of text.matchAll(pattern)) {
    if (match.index > last) parent.append(text.slice(last, match.index));
    const [token] = match;
    if (match[1]) parent.append(el('code', null, token.slice(1, -1)));
    else if (match[2]) parent.append(el('strong', null, token.slice(2, -2)));
    else {
      const link = el('a', null, token);
      link.href = token;
      link.target = '_blank';
      link.rel = 'noopener noreferrer';
      parent.append(link);
    }
    last = match.index + token.length;
  }
  if (last < text.length) parent.append(text.slice(last));
}

/** A small, safe markdown subset: fences, headings, lists, paragraphs. */
function markdown(text) {
  const root = el('div', 'text');
  const lines = text.replace(/\r\n?/g, '\n').split('\n');
  let paragraph = [];
  let list = null;
  const flushParagraph = () => {
    if (paragraph.length) {
      const p = el('p');
      paragraph.forEach((line, index) => {
        if (index) p.append(el('br'));
        inline(line, p);
      });
      root.append(p);
      paragraph = [];
    }
  };
  const flushList = () => {
    list = null;
  };
  for (let index = 0; index < lines.length; index++) {
    const line = lines[index];
    const fence = line.match(/^\s*(```|~~~)/);
    if (fence) {
      flushParagraph();
      flushList();
      const body = [];
      index++;
      while (index < lines.length && !lines[index].trimStart().startsWith(fence[1])) {
        body.push(lines[index]);
        index++;
      }
      const pre = el('pre');
      pre.append(el('code', null, body.join('\n')));
      root.append(pre);
      continue;
    }
    const heading = line.match(/^(#{1,4})\s+(.*)$/);
    if (heading) {
      flushParagraph();
      flushList();
      const h = el(`h${heading[1].length}`);
      inline(heading[2], h);
      root.append(h);
      continue;
    }
    const item = line.match(/^\s*([-*+]|\d+[.)])\s+(.*)$/);
    if (item) {
      flushParagraph();
      const ordered = /\d/.test(item[1]);
      if (!list || list.ordered !== ordered) {
        list = { ordered, node: el(ordered ? 'ol' : 'ul') };
        root.append(list.node);
      }
      const li = el('li');
      inline(item[2], li);
      list.node.append(li);
      continue;
    }
    if (!line.trim()) {
      flushParagraph();
      flushList();
      continue;
    }
    flushList();
    paragraph.push(line);
  }
  flushParagraph();
  return root;
}

/** One line of a JSON value, for a tool call's compact row. */
function argsLine(args) {
  if (args === undefined || args === null) return '';
  if (typeof args !== 'object') return String(args);
  const entries = Object.entries(args);
  if (entries.length === 1 && typeof entries[0][1] === 'string') return entries[0][1].split('\n')[0];
  return JSON.stringify(args);
}

// -------------------------------------------------------------- dates --

/** `2026-10-03T08:00:00.000+02:00` as `{ day: "2026-10-03", time: "08:00" }`. */
function dateParts(iso) {
  const match = /^(\d{4}-\d{2}-\d{2})(?:[T ](\d{2}:\d{2}))?/.exec(iso || '');
  return match ? { day: match[1], time: match[2] || '' } : null;
}

/** A node's time span, compact: one day shows its day once. */
function dateSpan(first, last) {
  const a = dateParts(first);
  const b = dateParts(last);
  if (!a) return '';
  const start = `${a.day}${a.time ? ` ${a.time}` : ''}`;
  if (!b || (a.day === b.day && a.time === b.time)) return start;
  if (a.day === b.day) return `${start}–${b.time}`;
  const end = a.day.slice(0, 4) === b.day.slice(0, 4) ? b.day.slice(5) : b.day;
  return `${start} → ${end}${b.time ? ` ${b.time}` : ''}`;
}

function kilobytes(bytes) {
  return `${(bytes / 1000).toFixed(1)} KB`;
}

function age(iso) {
  const then = Date.parse(iso);
  if (Number.isNaN(then)) return '';
  const minutes = Math.round((Date.now() - then) / 60000);
  if (minutes < 1) return 'now';
  if (minutes < 60) return `${minutes} min ago`;
  const hours = Math.round(minutes / 60);
  if (hours < 48) return `${hours} h ago`;
  return `${Math.round(hours / 24)} d ago`;
}

function basename(path) {
  if (!path) return '';
  const parts = path.split('/').filter(Boolean);
  return parts.length ? parts[parts.length - 1] : '/';
}

// ---------------------------------------------------------------- chat --

const chat = {
  session: null,
  state: null,
  messages: [],
  nodes: [],
  live: null,
  busy: false,
  mode: 'followUp',
  tools: new Map(),
  results: new Map(),
  running: new Set(),
};

function nearBottom(list) {
  return list.scrollHeight - list.scrollTop - list.clientHeight < 80;
}

function scrollToBottom(list) {
  list.scrollTop = list.scrollHeight;
}

/** The transcript row of one message, or null when it shows none. */
function renderMessage(message, streaming) {
  switch (message.role) {
    case 'user': {
      const text = withoutSignalRules(contentText(message.content));
      return text.trim() ? el('li', 'msg user', text) : null;
    }
    case 'custom': {
      if (message.display === false) return null;
      const text = contentText(message.content);
      if (!text.trim()) return null;
      const row = el('li', message.customType === 'signal' ? 'msg user' : 'msg note');
      row.append(el('span', 'origin', message.customType === 'signal' ? 'from Signal' : message.customType));
      row.append(text);
      return row;
    }
    case 'assistant':
      return renderAssistant(message, streaming);
    case 'toolResult':
      chat.results.set(message.toolCallId, { text: contentText(message.content), error: Boolean(message.isError) });
      updateTool(message.toolCallId);
      return null;
    case 'bashExecution': {
      const row = el('li', 'msg assistant');
      const details = el('details', 'tool');
      const summary = el('summary');
      summary.append(el('span', 'tool-name', '$'), el('span', 'tool-args', message.command));
      details.append(summary, el('pre', null, message.output || ''));
      row.append(details);
      return row;
    }
    case 'compactionSummary':
    case 'branchSummary':
      return el('li', 'msg note', message.role === 'compactionSummary' ? 'Earlier messages compacted' : 'Branch summary');
    default:
      return null;
  }
}

function renderAssistant(message, streaming) {
  const row = el('li', `msg assistant${streaming ? ' streaming' : ''}`);
  const blocks = Array.isArray(message.content)
    ? message.content
    : [{ type: 'text', text: String(message.content || '') }];
  for (const block of blocks) {
    if (block.type === 'text' && block.text) row.append(markdown(block.text));
    else if (block.type === 'thinking' && (block.thinking || '').trim()) {
      const details = el('details', 'thinking');
      details.append(el('summary', null, streaming && block === blocks[blocks.length - 1] ? 'Thinking…' : 'Thinking'));
      details.append(el('div', 'body', block.thinking));
      row.append(details);
    } else if (block.type === 'toolCall') {
      row.append(toolElement(block));
    }
  }
  if (message.stopReason === 'error') {
    row.append(el('div', 'msg error', `Error: ${message.errorMessage || 'the model request failed'}`));
  } else if (message.stopReason === 'aborted') {
    row.append(el('div', 'msg note', 'Stopped.'));
  }
  return row.childNodes.length ? row : null;
}

function toolElement(call) {
  const details = el('details', 'tool');
  details.dataset.call = call.id;
  const summary = el('summary');
  summary.append(el('span', 'tool-name', call.name), el('span', 'tool-args', argsLine(call.arguments)), el('span', 'tool-state'));
  details.append(summary);
  const args = el('pre', 'tool-input', JSON.stringify(call.arguments ?? {}, null, 2));
  details.append(args);
  chat.tools.set(call.id, details);
  fillTool(details, call.id);
  return details;
}

function fillTool(details, id) {
  const state = details.querySelector('.tool-state');
  const result = chat.results.get(id);
  let output = details.querySelector('.tool-output');
  if (result) {
    state.textContent = result.error ? 'failed' : 'done';
    state.className = `tool-state${result.error ? ' failed' : ''}`;
    if (!output) {
      output = el('pre', 'tool-output');
      details.append(output);
    }
    output.textContent = result.text;
  } else if (chat.running.has(id)) {
    state.textContent = 'running';
    state.className = 'tool-state running';
  } else {
    state.textContent = '';
  }
}

function updateTool(id) {
  const details = chat.tools.get(id);
  if (details && details.isConnected) fillTool(details, id);
}

/** Replace (or append) the row of message `index`. */
function paint(index, streaming) {
  const list = $('transcript');
  const stick = nearBottom(list);
  list.querySelector('.empty')?.remove();
  const old = chat.nodes[index];
  const next = renderMessage(chat.messages[index], streaming);
  if (old && next) old.replaceWith(next);
  else if (old) old.remove();
  else if (next) {
    const after = chat.nodes.slice(index + 1).find(Boolean);
    if (after) after.before(next);
    else list.append(next);
  }
  chat.nodes[index] = next;
  if (stick) scrollToBottom(list);
}

function renderTranscript() {
  const list = $('transcript');
  list.replaceChildren();
  chat.nodes = [];
  chat.tools.clear();
  chat.results.clear();
  // Results first, so their calls render complete.
  for (const message of chat.messages) {
    if (message.role === 'toolResult') {
      chat.results.set(message.toolCallId, { text: contentText(message.content), error: Boolean(message.isError) });
    }
  }
  chat.messages.forEach((message, index) => {
    const row = renderMessage(message, false);
    chat.nodes[index] = row;
    if (row) list.append(row);
  });
  if (!chat.messages.length) list.append(el('li', 'msg note empty', 'No messages yet. Say something.'));
  scrollToBottom(list);
}

function setBusy(busy) {
  chat.busy = busy;
  $('stop').hidden = !busy;
  $('mode').hidden = !busy;
  $('send').textContent = busy ? (chat.mode === 'steer' ? 'Steer' : 'Queue') : 'Send';
  updateLink();
}

function renderQueue(actions) {
  const queue = $('queue');
  const items = [
    ...((actions && actions.steering) || []).map((item) => `steer: ${item.text}`),
    ...((actions && actions.followUps) || []).map((item) => `queued: ${item.text}`),
  ];
  queue.replaceChildren(...items.map((text) => el('div', null, text)));
  queue.hidden = items.length === 0;
}

function sessionTitle() {
  const state = chat.state || {};
  if (state.sessionName) return state.sessionName;
  const first = chat.messages.find((message) => message.role === 'user');
  const text = first ? withoutSignalRules(contentText(first.content)).trim() : '';
  return text ? text.split('\n')[0].slice(0, 80) : 'New session';
}

function renderHeader() {
  const state = chat.state || {};
  $('session-title').textContent = chat.session ? sessionTitle() : 'eukhe';
  const model = typeof state.model === 'string' ? state.model : state.model && (state.model.name || state.model.id);
  const parts = [basename(state.cwd), model, localStorage.getItem(SESSION_KEY) ? 'pinned' : 'newest session'];
  $('session-sub').textContent = parts.filter(Boolean).join(' · ');
}

function note(text, className = 'msg note') {
  const list = $('transcript');
  list.append(el('li', className, text));
  scrollToBottom(list);
}

function applyEvent(event) {
  switch (event.type) {
    case 'agent_start':
      setBusy(true);
      break;
    case 'agent_end':
      chat.live = null;
      chat.running.clear();
      setBusy(false);
      break;
    case 'message_start': {
      chat.messages.push(event.message);
      const index = chat.messages.length - 1;
      chat.live = index;
      paint(index, event.message.role === 'assistant');
      break;
    }
    case 'message_update': {
      if (chat.live === null) {
        chat.messages.push(event.message);
        chat.live = chat.messages.length - 1;
      } else {
        chat.messages[chat.live] = event.message;
      }
      paint(chat.live, true);
      break;
    }
    case 'message_end': {
      if (chat.live === null) {
        chat.messages.push(event.message);
        paint(chat.messages.length - 1, false);
      } else {
        chat.messages[chat.live] = event.message;
        paint(chat.live, false);
      }
      chat.live = null;
      if (event.message.role === 'user' && !chat.state?.sessionName) renderHeader();
      break;
    }
    case 'tool_execution_start':
      chat.running.add(event.toolCallId);
      updateTool(event.toolCallId);
      break;
    case 'tool_execution_end':
      chat.running.delete(event.toolCallId);
      chat.results.set(event.toolCallId, { text: outputText(event.result), error: Boolean(event.isError) });
      updateTool(event.toolCallId);
      break;
    case 'session_action_update':
      renderQueue(event.actions);
      break;
    case 'session_info_changed':
      if (chat.state && event.name !== undefined) chat.state.sessionName = event.name;
      renderHeader();
      break;
    case 'auto_retry_start':
      note(`Retrying (attempt ${event.attempt}): ${event.errorMessage}`);
      break;
    case 'memory_update':
      memory.stale = true;
      renderMemoryStatus();
      break;
    default:
      break;
  }
}

// -------------------------------------------------------------- memory --

const memory = { loaded: false, stale: false, status: null, error: null };

function renderMemoryStatus() {
  const box = $('memory-status');
  box.replaceChildren();
  if (memory.error) {
    box.append(el('span', 'error', memory.error));
    return;
  }
  const status = memory.status;
  if (!status) {
    box.textContent = memory.loaded ? 'This session keeps no chat memory.' : 'Loading the memory…';
    return;
  }
  const strong = (text) => el('strong', null, text);
  box.append(
    strong(`${status.messages} messages`), ' · view ', strong(kilobytes(status.viewBytes)), ` / 128 KB · ${status.lines} lines`,
    status.unsummarized ? ` · ${status.unsummarized} unsummarized` : '',
    status.running ? ` · ${status.running} compacting` : '',
    status.model ? ` · ${status.model}` : '',
  );
  if (status.lastError) box.append(el('div', 'error', `Compactor: ${status.lastError}`));
  if (memory.stale) box.append(el('div', null, 'The memory changed. Refresh to see it.'));
}

function kindChips(kinds) {
  const box = el('span', 'node-kinds');
  for (const { kind, count } of kinds || []) {
    const chip = el('span', 'kind', count > 1 ? `${kind} ${count}` : kind);
    chip.dataset.kind = kind;
    box.append(chip);
  }
  return box;
}

/** One node of the tree: its row and, once expanded, its children. */
function memoryNode(node) {
  const item = el('li');
  item.setAttribute('role', 'treeitem');
  item.setAttribute('aria-expanded', 'false');
  item.dataset.node = `${node.id}+${node.count}`;
  const row = el('div', 'node-row');
  const toggle = el('button', 'node-toggle', '▸');
  toggle.type = 'button';
  toggle.setAttribute('aria-label', `Open ${node.id}+${node.count}`);
  const main = el('div', 'node-main');
  const meta = el('div', 'node-meta');
  meta.append(el('span', 'node-id', `${node.id}+${node.count}`), el('span', 'node-date', dateSpan(node.firstDate, node.lastDate)), kindChips(node.kinds));
  const summary = node.summary === null || node.summary === undefined
    ? el('div', 'node-summary pending', 'not summarized yet')
    : el('div', 'node-summary', node.summary);
  main.append(meta, summary);
  main.addEventListener('click', () => row.classList.toggle('full'));
  row.append(toggle, main);
  item.append(row);
  let children = null;
  toggle.addEventListener('click', async () => {
    const open = item.getAttribute('aria-expanded') === 'true';
    if (open) {
      item.setAttribute('aria-expanded', 'false');
      toggle.textContent = '▸';
      if (children) children.hidden = true;
      return;
    }
    item.setAttribute('aria-expanded', 'true');
    toggle.textContent = '▾';
    if (children) {
      children.hidden = false;
      return;
    }
    children = el('ul');
    children.setAttribute('role', 'group');
    children.append(el('li', 'info', 'Opening…'));
    item.append(children);
    try {
      const reply = await link.request('memory', { node: { id: node.id, count: node.count } });
      children.replaceChildren(...memoryLevel(reply));
    } catch (error) {
      children.replaceChildren(el('li', 'info error', error.message));
      children = null;
      item.lastChild.remove();
      item.setAttribute('aria-expanded', 'false');
      toggle.textContent = '▸';
    }
  });
  return item;
}

/** The rows of one `get_memory_tree` answer's level. */
function memoryLevel(reply) {
  const tree = reply && reply.tree;
  if (!tree) return [el('li', 'info', 'This session keeps no chat memory.')];
  const level = tree.level;
  switch (level.kind) {
    case 'lines':
      return level.nodes.length ? level.nodes.map(memoryNode) : [el('li', 'info', 'The chat is empty.')];
    case 'message': {
      const message = level.message;
      const item = el('li', 'node-message');
      item.setAttribute('role', 'treeitem');
      const meta = el('div', 'node-meta');
      meta.append(el('span', 'node-id', `message ${message.id}`), el('span', 'node-date', dateSpan(message.date, message.date)), kindChips([{ kind: message.kind, count: 1 }]));
      item.append(meta, el('div', 'body', message.text));
      return [item];
    }
    case 'no_line':
      return [el('li', 'info', 'Nothing under this line.')];
    default:
      return [el('li', 'info error', `Unknown level ${level.kind}`)];
  }
}

async function loadMemory() {
  memory.error = null;
  memory.stale = false;
  renderMemoryStatus();
  try {
    const reply = await link.request('memory', { node: null });
    memory.loaded = true;
    memory.status = reply && reply.tree ? reply.tree.status : null;
    $('memory-tree').replaceChildren(...memoryLevel(reply));
  } catch (error) {
    memory.error = `Could not read the memory: ${error.message}`;
  }
  renderMemoryStatus();
}

// ------------------------------------------------------------ sessions --
async function openSession(path) {
  showOpened(await link.request('open', { path }));
}

/** Show a session the server just bound the tab to. */
function showOpened(data) {
  chat.session = data.session;
  chat.state = data.state || {};
  chat.messages = Array.isArray(data.messages) ? data.messages : [];
  chat.live = null;
  chat.running.clear();
  renderTranscript();
  renderHeader();
  renderQueue(chat.state.sessionActions);
  setBusy(Boolean(chat.state.isStreaming));
  memory.loaded = false;
  if (!$('memory').hidden) loadMemory();
}

async function showSessions() {
  const dialog = $('sessions');
  const list = $('session-list');
  list.replaceChildren(el('li', 'info', 'Loading…'));
  if (!dialog.open) dialog.showModal();
  try {
    const sessions = await link.request('sessions');
    list.replaceChildren(...sessions.map((session) => {
      const item = el('li');
      const button = el('button');
      button.type = 'button';
      if (chat.session && chat.session.path === session.path) button.setAttribute('aria-current', 'true');
      button.append(el('span', null, withoutSignalRules(session.title || '(no title)').split('\n')[0].slice(0, 90)));
      button.append(el('span', 'sub', [basename(session.cwd), age(session.modified)].filter(Boolean).join(' · ')));
      button.addEventListener('click', () => {
        localStorage.setItem(SESSION_KEY, session.path);
        dialog.close();
        openSession(session.path).catch((error) => note(error.message, 'msg note error'));
      });
      item.append(button);
      return item;
    }));
    if (!sessions.length) list.replaceChildren(el('li', 'info', 'No saved sessions yet.'));
  } catch (error) {
    list.replaceChildren(el('li', 'info error', error.message));
  }
}

// ------------------------------------------------------------- wiring --

function updateLink() {
  const dot = $('link');
  const state = link && link.socket && link.socket.readyState === WebSocket.OPEN
    ? (chat.busy ? 'busy' : 'idle')
    : (dot.dataset.state === 'offline' ? 'offline' : 'connecting');
  dot.dataset.state = state;
  dot.title = state;
}

const link = new Link(
  (frame) => {
    switch (frame.type) {
      case 'event':
        applyEvent(frame.event);
        break;
      case 'resync':
        note(`${frame.reason}; reopening.`);
        openSession(localStorage.getItem(SESSION_KEY)).catch((error) => note(error.message, 'msg note error'));
        break;
      case 'unavailable':
        $('session-sub').textContent = `daemon unavailable: ${frame.error}`;
        break;
      default:
        break;
    }
  },
  (state) => {
    const dot = $('link');
    if (state === 'offline') {
      dot.dataset.state = 'offline';
      dot.title = 'offline';
      $('session-sub').textContent = 'reconnecting…';
      return;
    }
    if (state === 'connecting') {
      updateLink();
      return;
    }
    updateLink();
    openSession(localStorage.getItem(SESSION_KEY)).catch((error) => {
      if (localStorage.getItem(SESSION_KEY)) {
        // The pinned session is gone: follow the newest one.
        localStorage.removeItem(SESSION_KEY);
        openSession(null).catch((again) => note(again.message, 'msg note error'));
      } else {
        note(error.message, 'msg note error');
      }
    });
  },
);

function selectTab(name) {
  const memoryTab = name === 'memory';
  $('tab-chat').setAttribute('aria-selected', String(!memoryTab));
  $('tab-memory').setAttribute('aria-selected', String(memoryTab));
  $('chat').hidden = memoryTab;
  $('memory').hidden = !memoryTab;
  if (memoryTab && (!memory.loaded || memory.stale) && chat.session) loadMemory();
  if (!memoryTab) scrollToBottom($('transcript'));
}

function autosize() {
  const input = $('input');
  input.style.height = 'auto';
  input.style.height = `${Math.min(input.scrollHeight, window.innerHeight * 0.4)}px`;
}

async function send() {
  const input = $('input');
  const text = input.value;
  if (!text.trim()) return;
  input.value = '';
  autosize();
  try {
    await link.request('prompt', { text, mode: chat.busy ? chat.mode : 'followUp' });
  } catch (error) {
    input.value = text;
    autosize();
    note(`Not sent: ${error.message}`, 'msg note error');
  }
}

function init() {
  $('tab-chat').addEventListener('click', () => selectTab('chat'));
  $('tab-memory').addEventListener('click', () => selectTab('memory'));
  $('memory-refresh').addEventListener('click', () => loadMemory());
  $('session-button').addEventListener('click', () => showSessions());
  $('session-latest').addEventListener('click', () => {
    localStorage.removeItem(SESSION_KEY);
    $('sessions').close();
    openSession(null).catch((error) => note(error.message, 'msg note error'));
  });
  $('session-new').addEventListener('click', async () => {
    $('sessions').close();
    try {
      const data = await link.request('new');
      localStorage.setItem(SESSION_KEY, data.session.path);
      showOpened(data);
    } catch (error) {
      note(error.message, 'msg note error');
    }
  });
  $('composer').addEventListener('submit', (event) => {
    event.preventDefault();
    send();
  });
  const input = $('input');
  input.addEventListener('input', autosize);
  input.addEventListener('keydown', (event) => {
    // On touch keyboards Enter is a newline; Send sends.
    const touchOnly = window.matchMedia('(pointer: coarse)').matches;
    if (event.key === 'Enter' && !event.shiftKey && !event.isComposing && !touchOnly) {
      event.preventDefault();
      send();
    }
  });
  $('stop').addEventListener('click', () => {
    link.request('abort').catch((error) => note(`Stop failed: ${error.message}`, 'msg note error'));
  });
  for (const button of $('mode').querySelectorAll('button')) {
    button.addEventListener('click', () => {
      chat.mode = button.dataset.mode;
      for (const other of $('mode').querySelectorAll('button')) {
        other.setAttribute('aria-checked', String(other === button));
      }
      setBusy(chat.busy);
    });
  }
  link.connect();
}

init();
