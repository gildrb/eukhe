// The Inbox column (tablet and desktop): sessions grouped Needs you →
// Running → Recent, each row's status from derivePhase; filter, theme
// toggle and New session pinned at the bottom (thumb zone).

import { el, button, skeleton, toast } from './ui.js';
import { derivePhase, rowSession, withoutSignalRules } from './turn.js';
import { href, navigate } from './router.js';
import { fmt } from './format.js';
import { setPref, effectiveTheme } from './prefs.js';
import { createSession } from './binding.js';
import { refreshSessions } from './sessions.js';

const SVG = 'http://www.w3.org/2000/svg';
const SUN = 'M10 2a.75.75 0 0 1 .75.75v1.5a.75.75 0 0 1-1.5 0v-1.5A.75.75 0 0 1 10 2ZM10 15a.75.75 0 0 1 .75.75v1.5a.75.75 0 0 1-1.5 0v-1.5A.75.75 0 0 1 10 15ZM10 7a3 3 0 1 0 0 6 3 3 0 0 0 0-6ZM15.657 5.404a.75.75 0 1 0-1.06-1.06l-1.061 1.06a.75.75 0 0 0 1.06 1.06l1.06-1.06ZM6.464 14.596a.75.75 0 1 0-1.06-1.06l-1.06 1.06a.75.75 0 0 0 1.06 1.06l1.06-1.06ZM18 10a.75.75 0 0 1-.75.75h-1.5a.75.75 0 0 1 0-1.5h1.5A.75.75 0 0 1 18 10ZM5 10a.75.75 0 0 1-.75.75h-1.5a.75.75 0 0 1 0-1.5h1.5A.75.75 0 0 1 5 10ZM14.596 15.657a.75.75 0 0 0 1.06-1.06l-1.06-1.061a.75.75 0 1 0-1.06 1.06l1.06 1.06ZM5.404 6.464a.75.75 0 0 0 1.06-1.06l-1.06-1.06a.75.75 0 0 0-1.061 1.06l1.06 1.06Z';
const MOON = 'M7.455 2.004a.75.75 0 0 1 .26.77 7 7 0 0 0 9.958 7.967.75.75 0 0 1 1.067.853A8.5 8.5 0 1 1 6.647 1.921a.75.75 0 0 1 .808.083Z';

function icon(className, d) {
  const svg = document.createElementNS(SVG, 'svg');
  svg.setAttribute('viewBox', '0 0 20 20');
  svg.setAttribute('aria-hidden', 'true');
  svg.setAttribute('class', className);
  const path = document.createElementNS(SVG, 'path');
  path.setAttribute('d', d);
  if (className === 'moon') {
    path.setAttribute('fill-rule', 'evenodd');
    path.setAttribute('clip-rule', 'evenodd');
  }
  svg.append(path);
  return svg;
}

/** The gildrb sun/moon toggle (dark shows the sun: "switch to light"). */
export function themeToggle() {
  const node = el('button', { type: 'button', class: 'theme-toggle target' }, icon('sun', SUN), icon('moon', MOON));
  const label = () => {
    const other = effectiveTheme() === 'dark' ? 'light' : 'dark';
    node.setAttribute('aria-label', `Switch to ${other} mode`);
    node.title = `Switch to ${other} mode`;
  };
  label();
  node.addEventListener('click', (event) => {
    const next = effectiveTheme() === 'dark' ? 'light' : 'dark';
    setPref('theme', next);
    label();
    toast({ text: `Switched to ${next} mode.` });
    if (event.pointerType === 'mouse' || event.pointerType === 'pen') {
      node.blur();
      node.classList.add('no-hover');
      node.addEventListener('pointerleave', () => node.classList.remove('no-hover'), { once: true });
    }
  });
  return node;
}

function basename(path) {
  const parts = String(path || '').split('/').filter(Boolean);
  return parts.length ? parts[parts.length - 1] : '';
}

function seenKey(id) {
  return `eukhe.seen.${id}`;
}

/** Mount the Inbox into `root`; returns `{ update(state, route), focusFilter() }`. */
export function createInbox(root) {
  const list = el('div', { class: 'inbox-list', role: 'list' });
  const filter = el('input', {
    class: 'field-input',
    type: 'search',
    name: 'filter',
    placeholder: 'Filter…',
    autocomplete: 'off',
    spellcheck: 'false',
    'aria-label': 'Filter sessions',
    enterkeyhint: 'search',
  });
  let creating = false;
  const newButton = button({ label: 'New session', kind: 'primary', hint: '', onClick: async () => {
    if (creating) return;
    creating = true;
    newButton.querySelector('.btn-label').textContent = 'Creating…';
    try {
      const session = await createSession();
      navigate(href('chat', { sessionId: session.id }));
    } catch (error) {
      toast({ text: `Could not start a session: ${error.message}`, error: true });
    } finally {
      creating = false;
      newButton.querySelector('.btn-label').textContent = 'New session';
    }
  } });
  const foot = el('div', { class: 'inbox-foot' }, filter, el('div', { class: 'inbox-actions' }, themeToggle(), newButton));
  root.append(list, foot);

  let lastSig = '';
  let query = '';
  filter.addEventListener('input', () => {
    query = filter.value.trim().toLowerCase();
    lastSig = '';
    api.update(api.state, api.route);
  });
  filter.addEventListener('keydown', (event) => {
    if (event.key === 'ArrowDown') {
      const first = list.querySelector('.inbox-row');
      if (first) {
        event.preventDefault();
        first.focus();
      }
    }
  });
  list.addEventListener('keydown', (event) => {
    if (event.key !== 'ArrowDown' && event.key !== 'ArrowUp') return;
    const rows = [...list.querySelectorAll('.inbox-row')];
    const at = rows.indexOf(document.activeElement);
    if (at < 0) return;
    event.preventDefault();
    const next = rows[at + (event.key === 'ArrowDown' ? 1 : -1)];
    if (next) next.focus();
    else if (event.key === 'ArrowUp') filter.focus();
  });

  const api = {
    state: null,
    route: null,
    focusFilter() {
      filter.focus();
      filter.select();
    },
    update(state, route) {
      api.state = state;
      api.route = route;
      const now = Date.now();
      const { rows, loading, error } = state.sessions;
      const bound = state.session;
      const minute = Math.floor(now / 15_000);
      const sig = [
        rows.length, state.sessions.at, loading, error, query, route.sessionId, minute,
        bound ? `${bound.id}:${bound.title}:${derivePhase(state, now, fmt).label}` : '',
        state.approvals.length, state.link.status,
      ].join('|');
      if (sig === lastSig) return;
      lastSig = sig;
      if (!rows.length) {
        if (loading || !state.sessions.at) list.replaceChildren(el('p', { class: 'inbox-brand heading', text: 'eukhe' }), skeleton(6));
        else if (error) {
          list.replaceChildren(el('p', { class: 'inbox-brand heading', text: 'eukhe' }), el('div', { class: 'inbox-empty' },
            el('p', { text: 'Could not list sessions.' }),
            button({ label: 'Retry', kind: 'primary', onClick: () => refreshSessions().catch(() => {}) })));
        } else {
          list.replaceChildren(el('p', { class: 'inbox-brand heading', text: 'eukhe' }), el('p', { class: 'inbox-empty', text: 'No sessions yet. Start one ↓' }));
        }
        return;
      }
      const groups = { needs: [], running: [], recent: [] };
      for (const row of rows) {
        const title = withoutSignalRules(row.title || '').split('\n')[0] || 'New session';
        const isBound = bound && bound.id === row.id;
        if (query && !`${title} ${row.cwd || ''}`.toLowerCase().includes(query)) continue;
        const phase = isBound
          ? derivePhase(state, now, fmt)
          : derivePhase({ link: { status: 'open' }, session: rowSession(row, now), approvals: [] }, now, fmt);
        const item = { row, title: isBound ? bound.title : title, phase };
        if (phase.urgent) groups.needs.push(item);
        else if (['tool', 'tools', 'writing', 'thinking', 'prefill', 'waiting', 'retrying', 'compacting', 'bash', 'admission', 'chatWait'].includes(phase.phase)) groups.running.push(item);
        else groups.recent.push(item);
      }
      const section = (name, items) => {
        if (!items.length) return null;
        return el('div', { class: 'inbox-group', role: 'group', 'aria-label': name },
          el('h2', { class: 'inbox-group-title', text: name }),
          items.map(({ row, title, phase }) => {
            let seen = 0;
            try {
              seen = Number(localStorage.getItem(seenKey(row.id)) || 0);
            } catch {
              seen = 0;
            }
            const modified = row.modified ? Date.parse(row.modified) : 0;
            const current = route.sessionId === row.id;
            const status = phase.phase === 'idle' || phase.phase === 'idleNew'
              ? `Idle · ${modified ? fmt.relative(modified, now) : '—'}`
              : [phase.label, phase.detail].filter(Boolean).join(' · ');
            return el('a', {
              class: 'inbox-row',
              role: 'listitem',
              href: href('chat', { sessionId: row.id }),
              'aria-current': current ? 'page' : null,
              'data-urgent': phase.urgent ? 'true' : null,
              'data-fresh': !current && modified > seen && seen > 0 ? 'true' : null,
            },
            el('span', { class: 'inbox-title', text: title }),
            el('span', { class: 'inbox-status', text: status }),
            el('span', { class: 'inbox-meta', translate: 'no', text: basename(row.cwd) }));
          }));
      };
      list.replaceChildren(
        el('p', { class: 'inbox-brand heading', text: 'eukhe' }),
        ...[section('Needs you', groups.needs), section('Running', groups.running), section('Recent', groups.recent)].filter(Boolean),
      );
      if (query && !groups.needs.length && !groups.running.length && !groups.recent.length) {
        list.append(el('p', { class: 'inbox-empty', text: `No sessions match “${filter.value}”.` }), button({ label: 'Clear filter', onClick: () => {
          filter.value = '';
          filter.dispatchEvent(new Event('input'));
        } }));
      }
      if (route.sessionId) {
        try {
          localStorage.setItem(seenKey(route.sessionId), String(now));
        } catch {
          // Unread marks are a nicety.
        }
      }
    },
  };
  return api;
}
