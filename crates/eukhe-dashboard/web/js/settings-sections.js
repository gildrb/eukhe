// The Settings sections. Each `create(app)` returns `{ node, update(state) }`;
// controls render from the daemon's values (`session.state`, cvars) and
// re-read them after every change, so a reload shows the same thing.

import { store } from './store.js';
import { request, run, linkState } from './link.js';
import { el, icon, segmented, select, input, labelled, statusLine, button, textButton, copyButton } from './ui.js';
import { setPref, notificationsSupported } from './prefs.js';
import { setAndReload, reloadState, compactChat, listModels, modelKey } from './actions.js';
import { modelControls } from './models.js';
import { messageSpeed, modelName } from './turn.js';
import { fmt } from './format.js';

const MODES = [
  { value: 'one-at-a-time', label: 'One at a time' },
  { value: 'all', label: 'All at once' },
];
const OFF_ON = [{ value: 'off', label: 'Off' }, { value: 'on', label: 'On' }];
/** `MEMORY_VIEW_CEILING` (eukhe-types/src/daemon/memory.rs): the view's ceiling in bytes. */
const VIEW_CEILING = 128_000;
const EVENTS_SHOWN = 200;

function noSession() {
  return el('p', { class: 'section-note', text: 'Open a chat to see this.' });
}

/** A gildrb figures grid: label (tertiary) above value, two columns; `{ mono: true }` for ids and paths. */
function figures(pairs) {
  const grid = el('dl', { class: 'figures' });
  for (const [label, value, options = {}] of pairs) {
    const empty = value === null || value === undefined || value === '';
    grid.append(el('div', { class: 'figure' }, el('dt', { text: label }), el('dd', { class: options.mono && !empty ? 'mono' : 'fig', translate: options.mono ? 'no' : null, text: empty ? '–' : value })));
  }
  return grid;
}

/** A 2px bar with words above it. */
function bar(fraction, words, label) {
  const clamped = Number.isFinite(fraction) ? Math.min(1, Math.max(0, fraction)) : 0;
  const fill = el('span', { class: 'bar-fill' });
  fill.style.transform = `scaleX(${clamped})`;
  return el('div', { class: 'bar-block' },
    el('p', { class: 'bar-words fig', text: words }),
    el('div', { class: 'bar', role: 'meter', 'aria-label': label, 'aria-valuemin': '0', 'aria-valuemax': '100', 'aria-valuenow': String(Math.round(clamped * 100)) }, fill));
}

/** Re-render `host` with `build()` whenever `signature(state)` changes. */
function reactive(build, signature) {
  const host = el('div', { class: 'section-body' });
  let last = null;
  return {
    node: host,
    update(state) {
      const sig = signature(state);
      if (sig === last) return;
      last = sig;
      host.replaceChildren(...[build(state)].flat().filter(Boolean));
    },
  };
}

// ---------------------------------------------------------------- general --
function general() {
  return reactive((state) => {
    const status = statusLine();
    const theme = segmented({
      label: 'Theme',
      options: [{ value: 'system', label: 'System' }, { value: 'light', label: 'Light' }, { value: 'dark', label: 'Dark' }],
      value: state.prefs.theme,
      onPick: (value) => setPref('theme', value),
    });
    const enter = segmented({
      label: 'Enter key on touch',
      options: [{ value: 'newline', label: 'New line' }, { value: 'send', label: 'Send' }],
      value: state.prefs.enterSendsOnTouch ? 'send' : 'newline',
      onPick: (value) => setPref('enterSendsOnTouch', value === 'send'),
    });
    const nodes = [
      labelled('Theme', theme),
      labelled('Enter key on touch', enter, 'On a phone or tablet, Enter either starts a new line or sends. ⌘ or Ctrl with Enter always sends.'),
    ];
    if (notificationsSupported()) {
      const notify = segmented({
        label: 'Notifications',
        options: OFF_ON,
        value: state.prefs.notify ? 'on' : 'off',
        onPick: async (value) => {
          const ok = await setPref('notify', value === 'on');
          if (!ok) throw new Error('The browser did not allow notifications.');
        },
        onError: (error) => status.say(error.message, { error: true }),
      });
      nodes.push(labelled('Notifications', notify, 'While this tab is in the background, eukhe tells you when a reply finishes, fails or needs your approval.'));
    } else {
      nodes.push(el('div', { class: 'control' }, el('span', { class: 'control-label', text: 'Notifications' }),
        el('p', { class: 'control-note', text: 'This browser cannot show notifications for this page. They need HTTPS, for example through tailscale serve.' })));
    }
    nodes.push(status);
    return nodes;
  }, (state) => `${state.prefs.theme}|${state.prefs.enterSendsOnTouch}|${state.prefs.notify}`);
}

// ------------------------------------------------------------------ model --
function scopedModels(session) {
  const status = statusLine();
  const host = el('div', { class: 'check-list', role: 'group', 'aria-label': 'Scoped models' });
  const entries = session.state.scopedModels || [];
  const scoped = new Set(entries.map((entry) => modelKey(entry && entry.model)));
  listModels().then((models) => {
    host.replaceChildren(...models.map((model) => {
      const key = modelKey(model);
      const on = scoped.has(key);
      const row = el('button', { type: 'button', class: 'check-row', role: 'checkbox', 'aria-checked': on ? 'true' : 'false' },
        el('span', { class: 'check-box' }, icon('check')),
        el('span', { class: 'check-label', text: model.name || model.id }),
        el('span', { class: 'check-trail', translate: 'no', text: model.provider }));
      row.addEventListener('click', async () => {
        const next = on
          ? entries.filter((entry) => modelKey(entry && entry.model) !== key)
          : [...entries, { model: { provider: model.provider, id: model.id } }];
        row.setAttribute('aria-checked', on ? 'false' : 'true');
        try {
          await setAndReload({ type: 'set_scoped_models', scopedModels: next });
        } catch (error) {
          row.setAttribute('aria-checked', on ? 'true' : 'false');
          status.say(`Not changed. ${error.message}`, { error: true });
        }
      });
      return row;
    }));
  }, (error) => status.say(`Models did not load. ${error.message}`, { error: true }));
  return el('div', { class: 'control' },
    el('span', { class: 'control-label', text: 'Scoped models' }),
    el('p', { class: 'control-note', text: 'The models eukhe cycles through. None means all of them.' }),
    host, status);
}

function model() {
  return reactive((state) => {
    if (!state.session) return noSession();
    return [modelControls(), scopedModels(state.session)];
  }, (state) => {
    const session = state.session;
    if (!session) return 'none';
    const s = session.state;
    return JSON.stringify([session.id, modelKey(s.model), s.thinkingLevel, session.serviceTier || s.serviceTier, s.scopedModels]);
  });
}

// --------------------------------------------------------------- behavior --
function behavior() {
  let retry;
  let instructions = '';
  // Read once the link is up and a chat is bound (Settings can open before either).
  let retryFor = null;
  const readRetry = () => {
    const session = store.get().session;
    retryFor = session ? session.id : null;
    return run({ type: 'cvar', line: '' }).then((data) => {
      const found = (data && data.values || []).find((entry) => entry.id === 'retry.enabled');
      retry = found ? found.value === true : undefined;
      inner.update(store.get());
    }, () => {
      retryFor = null;
    });
  };
  const build = (state) => {
    if (!state.session) return noSession();
    const s = state.session.state;
    const status = statusLine();
    const fail = (error) => status.say(`Not changed. ${error.message}`, { error: true });
    const steering = segmented({ label: 'Steering messages', options: MODES, value: s.steeringMode, onPick: (mode) => setAndReload({ type: 'set_steering_mode', mode }), onError: fail });
    const followUp = segmented({ label: 'Follow-up messages', options: MODES, value: s.followUpMode, onPick: (mode) => setAndReload({ type: 'set_follow_up_mode', mode }), onError: fail });
    const compact = segmented({ label: 'Compact automatically', options: OFF_ON, value: s.autoCompactionEnabled ? 'on' : 'off', onPick: (value) => setAndReload({ type: 'set_auto_compaction', enabled: value === 'on' }), onError: fail });
    const retryControl = retry === undefined
      ? el('p', { class: 'control-note', text: 'Reading' })
      : segmented({
        label: 'Retry failed requests',
        options: OFF_ON,
        value: retry ? 'on' : 'off',
        onPick: async (value) => {
          await run({ type: 'set_auto_retry', enabled: value === 'on' });
          retry = value === 'on';
          await readRetry();
        },
        onError: fail,
      });
    const field = input({ value: instructions, placeholder: 'Optional instructions', name: 'compact-instructions', label: 'Compaction instructions' });
    field.addEventListener('input', () => {
      instructions = field.value;
    });
    const compactStatus = statusLine();
    const compactNow = button('Compact now', async () => {
      compactNow.disabled = true;
      compactStatus.say('Compacting');
      try {
        compactStatus.say(await compactChat(instructions));
        instructions = '';
        field.value = '';
      } catch (error) {
        compactStatus.say(`Not compacted. ${error.message}`, { error: true });
      } finally {
        compactNow.disabled = false;
      }
    });
    return [
      labelled('Steering messages', steering, 'Messages you steer with while eukhe works: deliver them one at a time, or all at once.'),
      labelled('Follow-up messages', followUp, 'Messages you queue for after the reply.'),
      labelled('Compact automatically', compact, 'Summarize earlier messages when the context gets full.'),
      el('div', { class: 'control' }, el('span', { class: 'control-label', text: 'Retry failed requests' }), retryControl),
      status,
      el('div', { class: 'control' }, el('label', { class: 'control-label', for: field.id || '', text: 'Compact now' }),
        el('div', { class: 'inline-form' }, field, compactNow), compactStatus),
    ];
  };
  const inner = reactive(build, (state) => {
    if (!state.session) return 'none';
    const s = state.session.state;
    return JSON.stringify([state.session.id, s.steeringMode, s.followUpMode, s.autoCompactionEnabled, retry]);
  });
  return {
    node: inner.node,
    update(state) {
      if (state.session && state.link.status === 'open' && retryFor !== state.session.id) readRetry();
      inner.update(state);
    },
  };
}

// ----------------------------------------------------------------- memory --
function dateSpan(first, last) {
  const start = new Date(first);
  const end = new Date(last);
  if (Number.isNaN(start.getTime())) return '';
  if (Number.isNaN(end.getTime()) || start.toDateString() === end.toDateString()) return fmt.date(start);
  return `${fmt.date(start)} – ${fmt.date(end)}`;
}

function memory() {
  const host = el('div', { class: 'section-body' });
  const path = [];
  let stamp = -1;
  let boundTo = null;
  let token = 0;
  const load = async () => {
    const mine = ++token;
    const node = path.length ? path[path.length - 1] : null;
    let data;
    try {
      data = await request('memory', node ? { node: { id: node.id, count: node.count } } : {});
    } catch (error) {
      if (mine === token) host.replaceChildren(el('p', { class: 'status-line', 'data-error': 'true', text: `Memory did not load. ${error.message}` }), textButton('Try again', load, { kind: 'primary' }));
      return;
    }
    if (mine !== token) return;
    paint(data);
  };
  const paint = (data) => {
    const nodes = [];
    if (!data || !data.tree) {
      host.replaceChildren(el('p', { class: 'section-note', text: 'This chat keeps no memory yet.' }));
      return;
    }
    const { status, level } = data.tree;
    if (status) {
      nodes.push(figures([
        ['Messages', fmt.num(status.messages)],
        ['Lines', fmt.num(status.lines)],
        ['View', `${fmt.bytes(status.viewBytes)} of ${fmt.bytes(VIEW_CEILING)}`],
        ['Not summarized', fmt.num(status.unsummarized || 0)],
        ['Compacting', fmt.num(status.running || 0)],
        ['Compactor', status.model || 'Default'],
      ]));
      if (status.lastError) nodes.push(el('p', { class: 'status-line', 'data-error': 'true', text: `The compactor failed. ${status.lastError}` }));
    }
    if (path.length) {
      nodes.push(el('div', { class: 'crumbs' }, textButton('← Back', () => {
        path.pop();
        load();
      }), el('span', { class: 'crumb-here fig', text: `Lines ${path[path.length - 1].id} to ${path[path.length - 1].id + path[path.length - 1].count - 1}` })));
    }
    if (level.kind === 'message') {
      const message = level.message;
      nodes.push(el('article', { class: 'memory-message' },
        el('p', { class: 'memory-message-head fig', text: `Message ${fmt.num(message.id)}, ${dateSpan(message.date, message.date)}` }),
        el('p', { class: 'memory-message-text', text: message.text }),
        copyButton(() => message.text)));
    } else if (level.kind === 'lines' && level.nodes.length) {
      const list = el('ul', { class: 'drill-list' });
      for (const child of level.nodes) {
        const row = el('button', { type: 'button', class: 'drill-row' },
          el('span', { class: 'drill-head' },
            el('span', { class: 'drill-range fig', text: child.count === 1 ? `Line ${child.id}` : `Lines ${child.id} to ${child.id + child.count - 1}` }),
            el('span', { class: 'drill-dates fig', text: dateSpan(child.firstDate, child.lastDate) })),
          el('span', { class: 'drill-summary', text: child.summary === null || child.summary === undefined ? 'Not summarized yet.' : child.summary }),
          el('span', { class: 'drill-arrow', 'aria-hidden': 'true', text: '→' }));
        row.addEventListener('click', () => {
          path.push(child);
          load();
        });
        list.append(el('li', null, row));
      }
      nodes.push(list);
    } else {
      nodes.push(el('p', { class: 'section-note', text: 'Nothing under this line.' }));
    }
    host.replaceChildren(...nodes);
  };
  return {
    node: host,
    update(state) {
      if (!state.session) {
        host.replaceChildren(noSession());
        boundTo = null;
        return;
      }
      if (boundTo !== state.session.id) {
        boundTo = state.session.id;
        path.length = 0;
        stamp = state.session.memory.stamp;
        load();
      } else if (state.session.memory.stamp !== stamp) {
        stamp = state.session.memory.stamp;
        load();
      }
    },
  };
}

// ------------------------------------------------------------------ usage --
function usage() {
  const host = el('div', { class: 'section-body' });
  let boundTo = null;
  let running = false;
  const load = async (session) => {
    let stats;
    try {
      stats = await run({ type: 'get_session_stats' });
    } catch (error) {
      host.replaceChildren(el('p', { class: 'status-line', 'data-error': 'true', text: `Usage did not load. ${error.message}` }));
      return;
    }
    const { tokens } = stats;
    const context = stats.contextUsage || session.state.contextUsage;
    const nodes = [figures([
      ['Cost', fmt.cost(stats.cost)],
      ['Messages', fmt.num(stats.totalMessages)],
      ['Input', fmt.tokens(tokens.input)],
      ['Output', fmt.tokens(tokens.output)],
      ['Cache read', fmt.tokens(tokens.cacheRead)],
      ['Cache write', fmt.tokens(tokens.cacheWrite)],
    ])];
    if (context && context.contextWindow) {
      const fraction = Number.isFinite(context.percent) ? context.percent / 100 : context.tokens / context.contextWindow;
      nodes.push(bar(fraction, `Context ${fmt.tokens(context.tokens, { unit: false })} of ${fmt.tokens(context.contextWindow)}, ${fmt.percent(fraction)} used`, 'Context used'));
    }
    const calls = session.messages.filter((message) => message.role === 'assistant' && message.usage).reverse();
    if (calls.length) {
      const table = el('div', { class: 'calls', role: 'table', 'aria-label': 'Model calls, newest first' },
        el('div', { class: 'calls-row calls-head', role: 'row' }, ['Time', 'Model', 'In', 'Out', 'First token', 'Speed'].map((label) => el('span', { role: 'columnheader', text: label }))));
      for (const message of calls.slice(0, 200)) {
        const speed = messageSpeed(message);
        table.append(el('div', { class: 'calls-row', role: 'row' },
          el('span', { class: 'fig', role: 'cell', text: fmt.time(message.timestamp) }),
          el('span', { class: 'calls-model', role: 'cell', translate: 'no', text: message.responseModel || message.model || '–' }),
          el('span', { class: 'fig', role: 'cell', text: fmt.tokens(message.usage.input, { unit: false }) }),
          el('span', { class: 'fig', role: 'cell', text: fmt.tokens(message.usage.output, { unit: false }) }),
          el('span', { class: 'fig', role: 'cell', text: speed && Number.isFinite(speed.ttftMs) ? fmt.duration(speed.ttftMs) : '–' }),
          el('span', { class: 'fig', role: 'cell', text: speed && speed.rate ? fmt.rate(speed.rate) : '–' })));
      }
      nodes.push(el('h3', { class: 'subhead', text: 'Model calls' }), el('div', { class: 'calls-frame' }, table));
    } else {
      nodes.push(el('p', { class: 'section-note', text: 'No model calls yet.' }));
    }
    host.replaceChildren(...nodes);
  };
  return {
    node: host,
    update(state) {
      const session = state.session;
      if (!session) {
        host.replaceChildren(noSession());
        boundTo = null;
        return;
      }
      if (boundTo !== session.id || (running && !session.turn.running)) {
        boundTo = session.id;
        load(session);
      }
      running = session.turn.running;
    },
  };
}

// --------------------------------------------------------------- advanced --
function eventSummary(frame) {
  const data = frame.data || {};
  if (frame.type === 'event' && data.event) {
    const event = data.event;
    if (event.toolName) return event.toolName;
    if (event.assistantMessageEvent) return event.assistantMessageEvent.type;
    if (event.message && event.message.role) return event.message.role;
    return '';
  }
  if (frame.type === 'reply' || frame.type === 'failure') return `request ${data.id}${data.error ? ` ${data.error}` : ''}`;
  if (frame.dir === 'out') return data.op === 'run' && data.command ? data.command.type : '';
  return data.reason || data.error || '';
}

function advanced() {
  const host = el('div', { class: 'section-body' });
  // Console: every cvar with its value (an empty line reads them all), searchable;
  // tapping one puts `set <id> <value>` in the field; `set` and `toggle` lines write.
  const line = input({ placeholder: 'set retry.enabled false', name: 'cvar-line', label: 'Console line', mono: true });
  line.id = 'console-line';
  let global = 'session';
  const scope = segmented({ label: 'Applies to', options: [{ value: 'session', label: 'This chat' }, { value: 'global', label: 'Global' }], value: global, onPick: (value) => {
    global = value;
  } });
  const consoleStatus = statusLine();
  const filter = input({ placeholder: 'Filter values', name: 'cvar-filter', label: 'Filter values', type: 'search' });
  const valueList = el('ul', { class: 'cvar-list', 'aria-label': 'Values' });
  let values = [];
  const valueText = (value) => (typeof value === 'string' ? value : JSON.stringify(value));
  const paintValues = () => {
    const query = filter.value.trim().toLowerCase();
    const shown = values.filter((entry) => !query || entry.id.toLowerCase().includes(query) || valueText(entry.value).toLowerCase().includes(query));
    valueList.replaceChildren(...shown.map((entry) => {
      const row = el('button', { type: 'button', class: 'cvar-row', title: `Put a set line for ${entry.id} in the field` },
        el('span', { class: 'cvar-id', translate: 'no', text: entry.id }),
        el('span', { class: 'cvar-value', translate: 'no', text: valueText(entry.value) }));
      row.addEventListener('click', () => {
        line.value = `set ${entry.id} ${valueText(entry.value)}`;
        line.focus();
        line.setSelectionRange(line.value.length, line.value.length);
      });
      return el('li', null, row);
    }));
    if (!shown.length) valueList.append(el('li', { class: 'section-note', text: values.length ? 'No values match.' : 'Reading' }));
  };
  filter.addEventListener('input', paintValues);
  const adopt = (data) => {
    if (data && Array.isArray(data.values)) {
      values = [...data.values].sort((a, b) => a.id.localeCompare(b.id));
      paintValues();
    }
  };
  // Read once the link is up and a chat is bound (Settings can open before either).
  let readFor = null;
  const readValues = (sessionId) => {
    readFor = sessionId;
    run({ type: 'cvar', line: '' }).then(adopt, (error) => {
      readFor = null;
      consoleStatus.say(`Values did not load. ${error.message}`, { error: true });
    });
  };
  const runLine = async () => {
    const text = line.value.trim();
    if (!text) return;
    consoleStatus.say('Running');
    try {
      adopt(await run({ type: 'cvar', line: text, global: global === 'global' }));
      consoleStatus.say(global === 'global' ? 'Applied and written to the global config.' : 'Applied to this chat.');
      line.value = '';
      reloadState().catch(() => {});
    } catch (error) {
      consoleStatus.say(error.message, { error: true });
    }
  };
  line.addEventListener('keydown', (event) => {
    if (event.key === 'Enter' && !event.isComposing) {
      event.preventDefault();
      runLine();
    }
  });
  const save = button('Save to agent', async () => {
    consoleStatus.say('Saving');
    try {
      await run({ type: 'cvar_save' });
      consoleStatus.say('Saved this chat’s values to its agent config.');
    } catch (error) {
      consoleStatus.say(error.message, { error: true });
    }
  });
  const consoleBlock = el('div', { class: 'control' },
    el('label', { class: 'control-label', for: line.id, text: 'Console' }),
    el('div', { class: 'inline-form' }, line, button('Run', runLine, { kind: 'primary' })),
    el('p', { class: 'control-note', text: 'Write with set <name> <value> or toggle <name>. Tap a value below to start a set line.' }),
    labelled('Applies to', scope),
    consoleStatus,
    el('div', { class: 'button-row' }, save),
    el('span', { class: 'control-label', text: 'Values' }),
    filter,
    valueList);
  paintValues();

  // Events
  const events = el('ul', { class: 'event-list', 'aria-label': 'Events, newest first' });
  let seenSeq = -1;
  const openSeq = new Set();
  const paintEvents = (state) => {
    if (state.framesSeq === seenSeq) return;
    seenSeq = state.framesSeq;
    const frames = state.frames.slice(-EVENTS_SHOWN).reverse();
    events.replaceChildren(...frames.map((frame) => {
      const type = frame.type === 'event' && frame.data.event ? frame.data.event.type : `${frame.dir === 'out' ? 'sent ' : ''}${frame.type}`;
      const row = el('button', { type: 'button', class: 'event-row', 'aria-expanded': openSeq.has(frame.seq) ? 'true' : 'false' },
        el('span', { class: 'fig', text: fmt.time(frame.at) }),
        el('span', { class: 'event-type', translate: 'no', text: type }),
        el('span', { class: 'event-summary', translate: 'no', text: eventSummary(frame) }));
      const item = el('li', null, row);
      if (openSeq.has(frame.seq)) item.append(el('pre', { class: 'event-json', tabindex: '0', translate: 'no', text: JSON.stringify(frame.data, null, 2).slice(0, 20000) }));
      row.addEventListener('click', () => {
        if (openSeq.has(frame.seq)) openSeq.delete(frame.seq);
        else openSeq.add(frame.seq);
        seenSeq = -1;
        paintEvents(store.get());
      });
      return item;
    }));
  };
  host.append(consoleBlock, el('h3', { class: 'subhead', text: 'Events' }), el('p', { class: 'control-note', text: 'Every frame between this page and eukhe, newest first. Tap one to see it whole.' }), events);
  return {
    node: host,
    update(state) {
      if (state.session && state.link.status === 'open' && readFor !== state.session.id) readValues(state.session.id);
      paintEvents(state);
    },
  };
}

// ------------------------------------------------------------------ about --
function about() {
  return reactive((state) => {
    const hello = state.link.hello;
    const words = { open: 'Connected', connecting: 'Connecting', offline: 'Offline', unavailable: 'eukhe is not running' };
    const session = state.session;
    return figures([
      ['Build', hello && hello.build ? hello.build : 'Unknown', { mono: true }],
      ['Link to eukhe', words[state.link.status] || state.link.status],
      ['Protocol', hello ? String(hello.protocol) : '1'],
      ['Chat', session ? session.id : null, { mono: true }],
      ['Folder', session && session.state.cwd ? session.state.cwd : null, { mono: true }],
      ['Model', session ? modelName(session.state.model) : null],
    ]);
  }, (state) => JSON.stringify([state.link.status, state.link.hello, state.session && state.session.id, state.session && modelName(state.session.state.model), linkState()]));
}

export const SECTIONS = [
  { id: 'general', title: 'General', create: general },
  { id: 'model', title: 'Model', create: model },
  { id: 'behavior', title: 'Behavior', create: behavior },
  { id: 'memory', title: 'Memory', create: memory },
  { id: 'usage', title: 'Usage', create: usage },
  { id: 'advanced', title: 'Advanced', create: advanced },
  { id: 'about', title: 'About', create: about },
];
