// The sidebar: wordmark, New chat, Search chats, chats grouped by last
// activity (real links; the open chat highlighted, a status word when it
// is not idle), Settings and the theme toggle. A persistent column from
// 1024px; below that a drawer from the left (scrim tap, Esc, Back or
// choosing a chat closes it).

import { el, icon, iconButton, pushLayer, trapFocus, openMenu, menuItem, input, button, statusLine } from './ui.js';
import { confirmDelete, renameChat } from './actions.js';
import { chatHref, current } from './router.js';
import { effectiveTheme, setPref } from './prefs.js';
import { derivePhase } from './turn.js';
import { fmt } from './format.js';

const desktop = matchMedia('(min-width: 1024px)');
const MAC = /Mac|iPhone|iPad/.test(navigator.platform || navigator.userAgent);
const locales = navigator.languages && navigator.languages.length ? [...navigator.languages] : undefined;
const monthYear = new Intl.DateTimeFormat(locales, { month: 'long', year: 'numeric' });
const DAY_MS = 86_400_000;

function startOfDay(time) {
  const day = new Date(time);
  day.setHours(0, 0, 0, 0);
  return day.getTime();
}

/** The group label of a chat last active at `time`. */
function groupOf(time, today) {
  if (!Number.isFinite(time)) return 'Older';
  if (time >= today) return 'Today';
  if (time >= today - DAY_MS) return 'Yesterday';
  if (time >= today - 7 * DAY_MS) return 'Previous 7 days';
  if (time >= today - 30 * DAY_MS) return 'Previous 30 days';
  return monthYear.format(new Date(time));
}

/** A row's title; a chat without messages (the daemon says "(no messages)") reads "New chat". */
function rowTitle(row) {
  return !row.title || row.title === '(no messages)' ? 'New chat' : row.title;
}

function statusWord(phase) {
  if (phase.phase === 'approval') return { text: 'Needs you', urgent: true };
  if (phase.phase === 'failed') return { text: 'Failed', urgent: false };
  if (phase.running) return { text: 'Running', urgent: false };
  return null;
}

/** The gildrb sun/moon toggle (dark shows the sun: "switch to light"). */
function themeToggle() {
  const node = el('button', { type: 'button', class: 'icon-button theme-toggle' }, icon('sun', 'sun'), icon('moon', 'moon'));
  const label = () => {
    const other = effectiveTheme() === 'dark' ? 'light' : 'dark';
    node.setAttribute('aria-label', `Switch to ${other} mode`);
    node.title = `Switch to ${other} mode`;
  };
  label();
  node.addEventListener('click', (event) => {
    setPref('theme', effectiveTheme() === 'dark' ? 'light' : 'dark');
    label();
    if (event.pointerType === 'mouse' || event.pointerType === 'pen') {
      node.blur();
      node.classList.add('no-hover');
      node.addEventListener('pointerleave', () => node.classList.remove('no-hover'), { once: true });
    }
  });
  node.relabel = label;
  return node;
}

/**
 * `createSidebar(root, app)` → `{ update(state), open(), close(), focusSearch() }`.
 * `app` gives `newChat()` and `openSettings()`.
 */
export function createSidebar(root, app) {
  const scrim = document.getElementById('scrim');
  const mainPane = document.getElementById('main');
  const close = iconButton('Close chats', 'close', () => api.close(), { className: 'sidebar-close' });
  const head = el('div', { class: 'sidebar-head' }, el('span', { class: 'wordmark', text: 'eukhe' }), close);

  const shortcut = el('kbd', { class: 'shortcut', 'aria-hidden': 'true', text: MAC ? '⌘⇧O' : 'Ctrl+Shift+O' });
  const newRow = el('button', { type: 'button', class: 'side-row', 'aria-keyshortcuts': MAC ? 'Meta+Shift+O' : 'Control+Shift+O' },
    icon('newChat'), el('span', { class: 'side-row-label', text: 'New chat' }), shortcut);
  newRow.addEventListener('click', () => {
    api.close();
    app.newChat();
  });

  const search = el('input', {
    class: 'search-input',
    type: 'search',
    name: 'search-chats',
    placeholder: 'Search chats',
    autocomplete: 'off',
    spellcheck: 'false',
    'aria-label': 'Search chats',
    enterkeyhint: 'search',
  });
  const searchBox = el('label', { class: 'search' }, icon('search'), search);
  let query = '';
  search.addEventListener('input', () => {
    query = search.value.trim().toLowerCase();
    paint(lastState, true);
  });
  search.addEventListener('keydown', (event) => {
    if (event.key === 'Escape' && search.value) {
      event.preventDefault();
      event.stopPropagation();
      search.value = '';
      query = '';
      paint(lastState, true);
    }
  });

  const list = el('div', { class: 'chat-list' });
  const scroller = el('div', { class: 'sidebar-scroll' }, list);

  const settingsRow = el('button', { type: 'button', class: 'side-row' }, icon('settings'), el('span', { class: 'side-row-label', text: 'Settings' }));
  settingsRow.addEventListener('click', () => {
    api.close();
    app.openSettings();
  });
  const toggle = themeToggle();
  const foot = el('div', { class: 'sidebar-foot' }, settingsRow, el('div', { class: 'sidebar-theme' }, toggle));

  root.append(head, el('div', { class: 'sidebar-top' }, newRow, searchBox), scroller, foot);
  trapFocus(root);

  let layer = null;
  let lastState = null;
  let lastSig = '';

  function rowNode(row, isCurrent, status) {
    const link = el('a', {
      class: 'chat-row',
      href: chatHref(row.id),
      'aria-current': isCurrent ? 'page' : null,
    }, el('span', { class: 'chat-row-title', text: rowTitle(row) }));
    if (status) link.append(el('span', { class: 'chat-row-status', 'data-urgent': status.urgent ? 'true' : 'false', text: status.text }));
    link.addEventListener('click', (event) => {
      if (event.metaKey || event.ctrlKey || event.shiftKey || event.button !== 0) return;
      if (layer) {
        event.preventDefault();
        layer.close({ replaceWith: chatHref(row.id) });
      }
    });
    return link;
  }

  /** The row's options: Rename… (inline field) and Delete… (confirm dialog). */
  function openRowMenu(anchor, row, isCurrent) {
    openMenu({
      anchor,
      label: `Options for ${rowTitle(row)}`,
      align: 'end',
      build: (panel, close) => {
        const items = el('div', { class: 'menu-items', role: 'menu' },
          menuItem('Rename…', () => {
            const field = input({ value: row.title && row.title !== '(no messages)' ? row.title : '', name: 'row-name', label: 'Chat name' });
            field.id = 'row-name-field';
            const note = statusLine();
            const save = async () => {
              try {
                await renameChat(row.id, field.value);
                close();
              } catch (error) {
                note.say(error.message, { error: true });
              }
            };
            field.addEventListener('keydown', (event) => {
              if (event.key === 'Enter' && !event.isComposing) {
                event.preventDefault();
                save();
              }
            });
            items.replaceWith(el('div', { class: 'menu-rename' },
              el('label', { class: 'control-label', for: field.id, text: 'Name' }),
              field, note,
              el('div', { class: 'menu-actions' }, button('Cancel', () => close()), button('Save', save, { kind: 'primary' }))));
            panel.place();
            requestAnimationFrame(() => {
              field.focus();
              field.select();
            });
          }),
          menuItem('Delete…', async () => {
            await close();
            // Deleting the current chat navigates; the drawer's history entry must go first.
            if (layer && isCurrent) await layer.close();
            await confirmDelete({ id: row.id, title: rowTitle(row) });
          }, { kind: 'danger' }));
        panel.append(items);
      },
    });
  }

  function paint(state, force = false) {
    if (!state) return;
    const route = current();
    const currentId = route.sessionId || (state.session && state.session.id);
    const phase = derivePhase(state, Date.now(), fmt);
    const status = state.session && state.session.id === currentId ? statusWord(phase) : null;
    const title = state.session ? state.session.title : '';
    const { rows, loaded } = state.sessions;
    const linkUp = state.link.status === 'open';
    const sig = [rows, loaded, linkUp, currentId, status && status.text, title, query].map(String).join('|') + rows.length;
    if (!force && sig === lastSig && state.sessions === lastState?.sessions) return;
    lastSig = sig;
    const shown = rows
      .map((row) => (state.session && row.id === state.session.id && title ? { ...row, title } : row))
      .filter((row) => !query || rowTitle(row).toLowerCase().includes(query));
    const nodes = [];
    if (!loaded && !linkUp) {
      nodes.push(el('p', { class: 'chat-list-note', text: 'Chats appear when eukhe is reachable.' }));
    } else if (loaded && !rows.length) {
      nodes.push(el('p', { class: 'chat-list-note', text: 'No chats yet.' }));
    } else if (query && !shown.length) {
      nodes.push(el('p', { class: 'chat-list-note', text: 'No chats match.' }));
    } else {
      const today = startOfDay(Date.now());
      const sorted = shown.slice().sort((a, b) => (Date.parse(b.modified) || 0) - (Date.parse(a.modified) || 0));
      let group = null;
      let groupList = null;
      for (const row of sorted) {
        const label = groupOf(Date.parse(row.modified), today);
        if (label !== group) {
          group = label;
          const id = `group-${nodes.length}`;
          groupList = el('ul', { class: 'chat-group-list', 'aria-labelledby': id });
          nodes.push(el('section', { class: 'chat-group' }, el('h2', { class: 'chat-group-label', id, text: label }), groupList));
        }
        const isCurrent = row.id === currentId;
        const more = el('button', { type: 'button', class: 'icon-button chat-row-more', 'aria-label': `Options for ${rowTitle(row)}`, 'aria-haspopup': 'dialog', 'aria-expanded': 'false' }, icon('chevron'));
        more.addEventListener('click', () => openRowMenu(more, row, isCurrent));
        groupList.append(el('li', { class: 'chat-item', 'data-current': isCurrent ? 'true' : null }, rowNode(row, isCurrent, isCurrent ? status : null), more));
      }
    }
    list.replaceChildren(...nodes);
  }

  function setOpen(open) {
    root.classList.toggle('open', open);
    scrim.hidden = !open;
    requestAnimationFrame(() => scrim.classList.toggle('shown', open));
    mainPane.inert = open;
    document.body.classList.toggle('drawer-open', open);
  }

  scrim.addEventListener('click', () => api.close());
  desktop.addEventListener('change', () => {
    if (desktop.matches && layer) {
      const open = layer;
      layer = null;
      open.close();
    }
  });

  const api = {
    update(state) {
      lastState = state;
      paint(state);
      toggle.relabel();
    },
    open() {
      if (desktop.matches || layer) return;
      setOpen(true);
      layer = pushLayer({
        history: true,
        dismiss: () => {
          layer = null;
          setOpen(false);
        },
      });
      requestAnimationFrame(() => {
        const active = root.querySelector('.chat-row[aria-current="page"]') || newRow;
        active.focus({ preventScroll: true });
        if (active.scrollIntoView) active.scrollIntoView({ block: 'nearest' });
      });
    },
    close() {
      return layer ? layer.close() : Promise.resolve();
    },
    focusSearch() {
      if (!desktop.matches) api.open();
      requestAnimationFrame(() => search.focus());
    },
    isOpen() {
      return Boolean(layer);
    },
  };
  return api;
}
