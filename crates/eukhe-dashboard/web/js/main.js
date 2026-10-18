// Boot: viewport, link, router → panes, store → pages/Inbox/title, frame
// handling, keyboard shortcuts, service worker. Pages register themselves
// through definePage; WebPages' modules load dynamically so a missing one
// degrades to "Nothing here" instead of breaking the shell.

import { store } from './store.js';
import { connect, onFrame, onReady, linkState, run } from './link.js';
import { current, href, navigate, onRoute, isSessionPage } from './router.js';
import { PageHost, pageFor } from './pages.js';
import { reduce, derivePhase } from './turn.js';
import { fmt } from './format.js';
import { watchViewport } from './viewport.js';
import { createInbox } from './inbox.js';
import { attend } from './notify.js';
import { bind, opening, createSession } from './binding.js';
import { addApproval, settleApprovals } from './approvals.js';
import { refreshSessions } from './sessions.js';
import { button, toast } from './ui.js';
import './chat.js';

const PAGE_MODULES = ['turn', 'tool', 'sessions', 'memory', 'queue', 'usage', 'model', 'settings', 'events'];
const TICK_MS = 250;
const SCROLL_KEY = 'eukhe.scroll.';
const LIVE_PHASES = new Set(['tool', 'tools', 'writing', 'thinking', 'prefill', 'waiting', 'retrying', 'compacting', 'bash', 'admission', 'offline', 'chatWait']);

const app = document.getElementById('app');
const mainPane = document.getElementById('main');
const asidePane = document.getElementById('aside');
const desktop = matchMedia('(min-width: 1280px)');
const mainHost = new PageHost(mainPane, 'main');
const asideBody = document.createElement('div');
asideBody.className = 'aside-body';
const asideClose = button({ label: 'Close', onClick: () => {
  const route = current();
  navigate(href(route.page, { sessionId: route.sessionId, rest: route.rest, params: route.params }));
} });
asideClose.classList.add('aside-close');
asidePane.append(asideBody, asideClose);
const asideHost = new PageHost(asideBody, 'aside');
const inbox = createInbox(document.getElementById('inbox'));

let shownMain = null;
let shownAside = null;
let lastRouteKey = null;

function routeKey(route) {
  return `${route.page}/${route.sessionId || ''}/${route.rest.join('/')}?${route.params.toString()}`;
}

function asideRoute(route) {
  if (route.aside) return { page: route.aside.page, sessionId: route.sessionId, rest: route.aside.rest, params: route.aside.params, aside: null };
  if (desktop.matches && route.sessionId && route.page !== 'turn' && pageFor('turn')) {
    return { page: 'turn', sessionId: route.sessionId, rest: [], params: new URLSearchParams(), aside: null };
  }
  return null;
}

function saveScroll() {
  if (!lastRouteKey || shownMain === 'chat') return;
  const page = mainPane.querySelector('.page');
  if (!page) return;
  try {
    sessionStorage.setItem(SCROLL_KEY + lastRouteKey, String(page.scrollTop));
  } catch {
    // Scroll restore is best effort.
  }
}

function showRoute(route) {
  if (route.page === 'chat' && !route.sessionId) {
    // `#/` (and `#/last`, the install start_url): the most recent session.
    bind(null).then((session) => navigate(href('chat', { sessionId: session.id, params: route.params }), { replace: true }), () => {});
  } else if (isSessionPage(route.page) && route.sessionId && linkState() === 'open') {
    bind(route.sessionId).catch(() => {});
  }

  saveScroll();
  const key = routeKey(route);
  const pageChanged = shownMain !== route.page;
  mainHost.show(route.page, route);
  shownMain = route.page;
  if (key !== lastRouteKey && route.page !== 'chat') {
    let top = 0;
    try {
      top = Number(sessionStorage.getItem(SCROLL_KEY + key) || 0);
    } catch {
      top = 0;
    }
    const page = mainPane.querySelector('.page');
    if (page) page.scrollTop = top;
  }
  lastRouteKey = key;

  const aside = asideRoute(route);
  if (aside) {
    asideHost.show(aside.page, aside);
    shownAside = aside.page;
    app.dataset.aside = route.aside ? 'open' : 'default';
    asideClose.hidden = !route.aside;
  } else {
    if (shownAside) asideHost.dispose();
    shownAside = null;
    app.dataset.aside = 'none';
  }

  if (pageChanged) {
    const heading = mainPane.querySelector('h1');
    if (route.page !== 'chat' && heading) {
      heading.tabIndex = -1;
      heading.focus({ preventScroll: true });
    } else if (route.page === 'chat' && matchMedia('(pointer: fine)').matches) {
      document.getElementById('composer-input')?.focus({ preventScroll: true });
    }
  }
  render(store.get());
}

function render(state) {
  const route = current();
  mainHost.refresh();
  if (shownAside) asideHost.refresh();
  inbox.update(state, route);
  app.dataset.inbox = state.ui.inbox ? 'shown' : 'hidden';
  const phase = derivePhase(state, Date.now(), fmt);
  const failed = phase.phase === 'failed' ? 1 : 0;
  attend({
    phase,
    sessionTitle: state.session ? state.session.title : '',
    pageTitle: mainHost.title(),
    needsYou: state.approvals.length + failed,
    notify: state.prefs.notify,
    hidden: state.ui.hidden,
  });
}

store.subscribe(render);
onRoute(showRoute);

// Context usage, message count and stats carry no event: re-read them when
// a turn ends, so an open tab matches a fresh one.
function refreshBoundState(sessionId) {
  run({ type: 'get_connection_state' }).then((fresh) => {
    store.set((state) => (state.session && state.session.id === sessionId && fresh
      ? { session: { ...state.session, state: { ...state.session.state, ...fresh } } }
      : null));
  }, () => {});
  if (!store.get().stats) return;
  run({ type: 'get_session_stats' }).then((stats) => {
    store.set((state) => (state.session && state.session.id === sessionId ? { stats } : null));
  }, () => {});
}

// ---------------------------------------------------------------- frames --
onFrame('event', (frame) => {
  if (opening()) return;
  const state = store.get();
  if (!state.session) return;
  const session = reduce(state.session, frame.event, Date.now());
  const next = frame.cursor ? { ...session, cursor: frame.cursor } : session;
  store.set({ session: next });
  switch (frame.event.type) {
    case 'tool_execution_start':
    case 'tool_execution_update':
    case 'tool_execution_end':
      settleApprovals();
      break;
    case 'agent_end':
      settleApprovals();
      refreshBoundState(next.id);
      break;
    case 'turn_end':
      refreshBoundState(next.id);
      break;
    case 'session_info_changed':
      refreshSessions().catch(() => {});
      break;
    default:
      break;
  }
});
onFrame('approval', addApproval);
onFrame('resync', (frame) => {
  toast({ text: `${frame.reason}. Reopening…` });
  const route = current();
  bind(route.sessionId || (store.get().session && store.get().session.id) || null, { force: true }).catch(() => {});
});
onReady(() => {
  const route = current();
  const id = route.sessionId || null;
  refreshSessions().catch(() => {});
  bind(id, { force: true }).then((session) => {
    if (!route.sessionId && route.page === 'chat') navigate(href('chat', { sessionId: session.id, params: route.params }), { replace: true });
  }, () => {});
  const { hello } = store.get().link;
  if (hello && hello.build && 'serviceWorker' in navigator && window.isSecureContext) {
    navigator.serviceWorker.register(`sw.js?v=${encodeURIComponent(hello.build)}`).catch(() => {});
  }
});
window.addEventListener('eukhe:reopen', () => {
  bind(current().sessionId, { force: true }).catch(() => {});
});

// ------------------------------------------------------------ lifecycle --
document.addEventListener('visibilitychange', () => {
  store.set((state) => ({ ui: { ...state.ui, hidden: document.hidden } }));
});
desktop.addEventListener('change', () => showRoute(current()));
setInterval(() => {
  if (document.hidden) return;
  const state = store.get();
  const phase = derivePhase(state, Date.now(), fmt);
  if (LIVE_PHASES.has(phase.phase)) store.set({ tick: Date.now() });
}, TICK_MS);

// ------------------------------------------------------------- keyboard --
function inField(target) {
  return target instanceof HTMLElement && (target.isContentEditable || ['INPUT', 'TEXTAREA', 'SELECT'].includes(target.tagName));
}

document.addEventListener('keydown', (event) => {
  const mod = event.metaKey || event.ctrlKey;
  const key = event.key.toLowerCase();
  if (mod && !event.shiftKey && key === 'k') {
    event.preventDefault();
    if (getComputedStyle(document.getElementById('inbox')).display !== 'none') inbox.focusFilter();
    else navigate(href('sessions'));
    return;
  }
  if (mod && event.shiftKey && key === 'o') {
    event.preventDefault();
    createSession().then((session) => navigate(href('chat', { sessionId: session.id })), (error) => toast({ text: error.message, error: true }));
    return;
  }
  if (mod && event.shiftKey && key === 's') {
    event.preventDefault();
    store.set((state) => ({ ui: { ...state.ui, inbox: !state.ui.inbox } }));
    return;
  }
  if (event.key === 'Escape') {
    if (document.querySelector('dialog[open]')) return;
    const composer = document.getElementById('composer-input');
    const typing = composer && document.activeElement === composer && composer.value.trim();
    const state = store.get();
    if (state.session && state.session.turn.running && !typing) {
      const dock = document.querySelector('.dock');
      if (dock && dock.dockApi) {
        event.preventDefault();
        dock.dockApi.stop();
      }
    }
    return;
  }
  if (inField(event.target) || mod || event.altKey) return;
  if (event.key === '/') {
    const composer = document.getElementById('composer-input');
    if (composer) {
      event.preventDefault();
      composer.focus();
    }
  } else if (event.key === '.') {
    const route = current();
    if (!route.sessionId) return;
    event.preventDefault();
    const open = route.aside && route.aside.page === 'turn';
    navigate(href(route.page, { sessionId: route.sessionId, rest: route.rest, params: route.params, aside: open ? null : { page: 'turn' } }));
  }
});

// ----------------------------------------------------------------- boot --
watchViewport();
showRoute(current());
connect();
Promise.allSettled(PAGE_MODULES.map((name) => import(`./pages/${name}.js`))).then(() => showRoute(current()));
