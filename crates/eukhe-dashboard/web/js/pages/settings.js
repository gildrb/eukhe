// Settings (`#/settings[/<section>]?q=`): the bound session's behavior
// (steering and follow-up modes, auto-compaction, auto-retry, Compact
// now), the cvar console (Cvar / CvarSave) with a searchable list of the
// session's replicated values, and this dashboard's preferences.

import { definePage } from '../pages.js';
import { store } from '../store.js';
import { setPref, notificationsSupported } from '../prefs.js';
import { actionButton, failed, frame, keyed, place, reloadState, replaceSoon, segmented } from './kit.js';

const MODES = [
  { value: 'one-at-a-time', label: 'One at a time' },
  { value: 'all', label: 'All at once' },
];
const THEMES = [
  { value: 'system', label: 'System' },
  { value: 'light', label: 'Light' },
  { value: 'dark', label: 'Dark' },
];
const SECTIONS = ['behavior', 'cvars', 'dashboard'];
const LOG_LIMIT = 50;

const views = new WeakMap();

/** Read the session's replicated cvars: an empty line runs nothing and answers them all. */
function readCvars(ctx, view) {
  view.cvars = ctx.run({ type: 'cvar', line: '' }).then((data) => {
    view.values = data && Array.isArray(data.values) ? data.values : [];
    view.version += 1;
    view.repaint();
    return view.values;
  }, (error) => {
    view.cvarError = error;
    view.version += 1;
    view.repaint();
    throw error;
  });
  view.cvars.catch(() => {});
}

function cvarValue(view, id) {
  const found = (view.values || []).find((entry) => entry.id === id);
  return found ? found.value : undefined;
}

function behaviorSection(ctx, view, session) {
  const { ui } = ctx;
  if (!session) {
    return ui.section('Behavior', ui.el('p', { class: 'pg-line small', text: 'Open a session to change how it behaves.' }));
  }
  const { state } = session;
  const retry = cvarValue(view, 'retry.enabled');
  const switchThen = (command) => async () => {
    try {
      await ctx.run(command);
      await reloadState(ctx);
    } catch (error) {
      failed(error, 'Not changed');
      view.version += 1;
      view.repaint();
    }
  };
  return ui.section('Behavior',
    segmented({
      label: 'Steering messages',
      options: MODES,
      value: state.steeringMode,
      onPick: (mode) => switchThen({ type: 'set_steering_mode', mode })(),
    }),
    segmented({
      label: 'Queued follow-ups',
      options: MODES,
      value: state.followUpMode,
      onPick: (mode) => switchThen({ type: 'set_follow_up_mode', mode })(),
    }),
    ui.toggle({
      label: 'Compact the context automatically',
      checked: Boolean(state.autoCompactionEnabled),
      onChange: (enabled) => switchThen({ type: 'set_auto_compaction', enabled })(),
    }),
    retry === undefined
      ? ui.el('p', { class: 'pg-line small', text: view.cvars ? 'Reading auto-retry…' : 'Auto-retry state unknown.' })
      : ui.toggle({
        label: 'Retry failed model requests',
        checked: retry === true,
        onChange: async (enabled) => {
          try {
            await ctx.run({ type: 'set_auto_retry', enabled });
          } catch (error) {
            failed(error, 'Not changed');
          }
          readCvars(ctx, view);
        },
      }),
    ui.el('div', { class: 'pg-stack' },
      ui.field({
        label: 'Compaction instructions (optional)',
        name: 'compact-instructions',
        value: view.instructions,
        placeholder: 'Keep the test plan…',
        onInput: (value) => {
          view.instructions = value;
        },
      }),
      ui.el('div', { class: 'pg-actions' }, actionButton({
        label: 'Compact now',
        busyLabel: 'Compacting',
        work: async () => {
          const instructions = view.instructions.trim();
          const result = await ctx.run(instructions ? { type: 'compact', customInstructions: instructions } : { type: 'compact' });
          ui.toast({ text: result && Number.isFinite(result.tokensBefore) ? `Compacted ${ctx.fmt.tokens(result.tokensBefore)} of context.` : 'Compacted.' });
        },
        onError: (error) => failed(error, 'Not compacted'),
      }))));
}

function runLine(ctx, view, line, global) {
  const entry = { line, global, at: Date.now(), status: 'running', text: '' };
  view.log = [entry, ...view.log].slice(0, LOG_LIMIT);
  view.version += 1;
  view.repaint();
  return ctx.run({ type: 'cvar', line, global }).then((data) => {
    entry.status = 'ok';
    view.values = data && Array.isArray(data.values) ? data.values : view.values;
    entry.text = global ? 'Written to the global config.' : 'Applied.';
  }, (error) => {
    entry.status = 'error';
    entry.text = error.message;
  }).finally(() => {
    view.version += 1;
    view.repaint();
  });
}

function consoleBlock(ctx, view) {
  const { ui } = ctx;
  const input = ui.el('input', {
    class: 'field-input mono pg-console-input',
    name: 'cvar-line',
    type: 'text',
    autocomplete: 'off',
    autocapitalize: 'off',
    spellcheck: 'false',
    enterkeyhint: 'go',
    placeholder: 'set retry.maxRetries 5…',
    'aria-label': 'Cvar command',
    translate: 'no',
  });
  input.value = view.draft;
  input.addEventListener('input', () => {
    view.draft = input.value;
  });
  let global = false;
  const submit = () => {
    const line = input.value.trim();
    if (!line) {
      input.focus();
      return;
    }
    view.draft = '';
    input.value = '';
    runLine(ctx, view, line, global);
  };
  input.addEventListener('keydown', (event) => {
    if (event.key === 'Enter' && !event.isComposing) {
      event.preventDefault();
      submit();
    }
  });
  view.consoleInput = input;
  return ui.el('div', { class: 'pg-console' },
    ui.el('label', { class: 'field' }, ui.el('span', { class: 'field-label', text: 'Command' }), input),
    ui.el('div', { class: 'pg-actions' },
      ui.toggle({ label: 'Global config', checked: false, onChange: (next) => {
        global = next;
      } }),
      ui.button({ label: 'Run', kind: 'primary', onClick: submit }),
      actionButton({
        label: 'Save to agent',
        busyLabel: 'Saving',
        work: async () => {
          await ctx.run({ type: 'cvar_save' });
          ui.toast({ text: 'Saved this session’s cvars to its agent config.' });
        },
        onError: (error) => failed(error, 'Not saved'),
      })),
    ui.el('p', { class: 'pg-line small', text: '`set <id> <value>`, `toggle <id>`, `alias`, `bind` and `action` lines, `;` between commands. Global accepts set and toggle only.' }));
}

function logBlock(ctx, view) {
  const { ui, fmt } = ctx;
  if (!view.log.length) return null;
  return ui.el('ol', { class: 'pg-console-log', 'aria-live': 'polite' }, ...view.log.map((entry) => ui.el('li', { 'data-status': entry.status },
    ui.el('span', { class: 'pg-console-line mono', translate: 'no', text: `${entry.global ? 'global ' : ''}${entry.line}` }),
    ui.el('span', { class: 'pg-console-result', text: entry.status === 'running' ? 'Running…' : entry.status === 'error' ? `Failed · ${entry.text}` : entry.text }),
    ui.el('span', { class: 'pg-console-at fig', text: fmt.time(entry.at) }))));
}

function valuesBlock(ctx, view) {
  const { ui, fmt } = ctx;
  if (view.cvarError && !view.values) {
    return ui.empty({ title: 'The cvars did not load.', body: view.cvarError.message, action: { label: 'Try again', onClick: () => {
      view.cvarError = null;
      readCvars(ctx, view);
    } } });
  }
  if (!view.values) return ui.skeleton(8);
  const query = (ctx.route.params.get('q') || '').trim().toLowerCase();
  const shown = view.values.filter((entry) => !query || entry.id.toLowerCase().includes(query) || JSON.stringify(entry.value).toLowerCase().includes(query));
  const list = ui.el('ol', { class: 'pg-cvars' }, ...shown.map((entry) => {
    const value = typeof entry.value === 'string' ? entry.value : JSON.stringify(entry.value);
    return ui.el('li', {}, ui.el('button', {
      type: 'button',
      class: 'pg-cvar',
      title: 'Put a set line for this cvar in the console',
      onClick: () => {
        const quoted = typeof entry.value === 'string' && /[\s;"]/.test(entry.value) ? `"${entry.value.replace(/[\\"]/g, '\\$&')}"` : value;
        view.draft = `set ${entry.id} ${quoted}`;
        if (view.consoleInput) {
          view.consoleInput.value = view.draft;
          view.consoleInput.focus();
        }
      },
    }, ui.el('span', { class: 'pg-cvar-id mono', translate: 'no', text: entry.id }), ui.el('span', { class: 'pg-cvar-value mono', translate: 'no', text: value })));
  }));
  const count = ui.el('p', { class: 'pg-line small fig', text: query ? `${fmt.num(shown.length)} of ${fmt.num(view.values.length)} values` : `${fmt.num(view.values.length)} values the session shares` });
  return ui.el('div', { class: 'pg-stack' }, count, shown.length ? list : ui.empty({ title: `No cvar matches “${query}”.` }));
}

function searchField(ctx, view) {
  return ctx.ui.field({
    label: 'Search cvars',
    value: ctx.route.params.get('q') || '',
    type: 'search',
    placeholder: 'retry, compaction…',
    name: 'cvar-search',
    onInput: (value) => {
      const live = view.ctx;
      replaceSoon(live, live.href('settings', { rest: live.route.rest, params: value.trim() ? { q: value } : null, aside: live.route.aside }));
    },
  });
}

function dashboardSection(ctx, state) {
  const { ui } = ctx;
  const notify = notificationsSupported()
    ? ui.toggle({
      label: 'Notify when a turn ends or needs approval (tab in background)',
      checked: Boolean(state.prefs.notify),
      onChange: async (value) => {
        const took = await setPref('notify', value);
        if (!took) ui.toast({ text: 'Notifications are blocked for this site in the browser.', error: true });
      },
    })
    : ui.el('p', { class: 'pg-line small', text: 'Notifications need a secure page: localhost, or HTTPS through tailscale serve.' });
  return ui.section('Dashboard',
    segmented({ label: 'Theme', options: THEMES, value: state.prefs.theme, onPick: (theme) => setPref('theme', theme) }),
    ui.toggle({
      label: 'Enter sends on touch screens',
      checked: Boolean(state.prefs.enterSendsOnTouch),
      onChange: (value) => setPref('enterSendsOnTouch', value),
    }),
    notify,
    ui.el('p', { class: 'pg-line small' }, 'Debugging: ', ui.el('a', { class: 'link target', href: ctx.href('events'), text: 'Events →' })));
}

function render(root, ctx) {
  const parts = frame(root, ctx, { title: 'Settings', back: ctx.state.session ? { label: 'Chat', href: ctx.href('chat', { sessionId: ctx.state.session.id }) } : null });
  const view = {
    parts,
    ctx,
    cache: new Map(),
    version: 0,
    values: null,
    cvars: null,
    cvarError: null,
    log: [],
    draft: '',
    instructions: '',
    consoleInput: null,
    boundTo: null,
    scrolledTo: null,
  };
  view.repaint = () => update(root, { ...view.ctx, state: store.get() });
  views.set(root, view);
  update(root, ctx);
}

function update(root, ctx) {
  const view = views.get(root);
  if (!view) return;
  view.ctx = ctx;
  const { ui, state } = ctx;
  const session = state.session;
  if (session && view.boundTo !== session.id && state.link.status === 'open') {
    view.boundTo = session.id;
    view.values = null;
    readCvars(ctx, view);
  }
  const behaviorNode = keyed(view.cache, 'behavior', [session && session.state, view.version], () => behaviorSection(ctx, view, session));
  const consoleNode = keyed(view.cache, 'console', [session ? session.id : null], () => (session ? consoleBlock(ctx, view) : null));
  const logNode = keyed(view.cache, 'log', [view.version], () => logBlock(ctx, view));
  const searchNode = keyed(view.cache, 'search', [], () => searchField(ctx, view));
  const valuesNode = keyed(view.cache, 'values', [view.version, ctx.route.params.get('q')], () => valuesBlock(ctx, view));
  const cvarsNode = keyed(view.cache, 'cvars', [consoleNode, logNode, valuesNode], () => ui.section('Cvars',
    session ? ui.el('div', { class: 'pg-stack' }, consoleNode, logNode, searchNode, valuesNode) : ui.el('p', { class: 'pg-line small', text: 'Open a session to use its cvar console.' })));
  const dashboardNode = keyed(view.cache, 'dashboard', [state.prefs], () => dashboardSection(ctx, state));
  behaviorNode.id = 'settings-behavior';
  cvarsNode.id = 'settings-cvars';
  dashboardNode.id = 'settings-dashboard';
  place(view.parts.body, [behaviorNode, cvarsNode, dashboardNode]);
  const section = ctx.route.rest[0];
  if (SECTIONS.includes(section) && view.scrolledTo !== section) {
    view.scrolledTo = section;
    requestAnimationFrame(() => document.getElementById(`settings-${section}`)?.scrollIntoView({ block: 'start' }));
  }
}

export default definePage({
  id: 'settings',
  title: () => 'Settings',
  render,
  update,
  dispose(root) {
    views.delete(root);
  },
});
