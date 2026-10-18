// Boot and wiring: the sidebar, the top bar, the conversation and the
// composer in one 100dvh column; the link (frames folded into the
// session), the route (which chat, Settings), the 4 Hz tick while a turn
// runs, the document title, and the keyboard.

import { store } from './store.js';
import { connect, onFrame, onReady, run } from './link.js';
import { current, chatHref, navigate, onRoute } from './router.js';
import { reduce, derivePhase } from './turn.js';
import { fmt } from './format.js';
import { bind, opening } from './binding.js';
import { addApproval, settleApprovals } from './approvals.js';
import { refreshSessions } from './sessions.js';
import { layerCount } from './ui.js';
import { attend } from './notify.js';
import { createSidebar } from './sidebar.js';
import { createTopbar } from './topbar.js';
import { createConversation } from './conversation.js';
import { createComposer } from './composer.js';
import { openModelMenu } from './models.js';
import { createSettings } from './settings.js';
import { newChat } from './actions.js';

const TICK_MS = 250;
const mainPane = document.getElementById('main');

let composer = null;
let conversation = null;

/** What every view module may ask of the app. */
const app = {
  newChat() {
    newChat().catch((error) => app.notice(`No new chat. ${error.message}`));
  },
  openDrawer() {
    sidebar.open();
  },
  openSettings(section = '') {
    settings.open(section);
  },
  openModelMenu(anchor) {
    openModelMenu(anchor);
  },
  title() {
    const { session } = store.get();
    return session ? session.title : '';
  },
  sessionId() {
    const { session } = store.get();
    return session ? session.id : null;
  },
  routeSessionId() {
    return current().sessionId;
  },
  notice(text) {
    conversation.notice(text);
  },
  reopen() {
    bind(current().sessionId, { force: true }).catch(() => {});
  },
  retryLast() {
    composer.retryLast();
  },
  resend(item) {
    composer.resend(item);
  },
  editPending(item) {
    composer.editPending(item);
  },
  async editQueued(lane, index, text) {
    try {
      const reply = await run({ type: 'mutate_queued_message', lane, index, expectedText: text, mutation: { type: 'delete' } });
      if (reply && reply.status === 'rejected') throw new Error('It was already sent.');
      composer.fill(text);
    } catch (error) {
      app.notice(`Not editable. ${error.message}`);
    }
  },
  async removeQueued(lane, index, text) {
    try {
      const reply = await run({ type: 'mutate_queued_message', lane, index, expectedText: text, mutation: { type: 'delete' } });
      if (reply && reply.status === 'rejected') throw new Error('It was already sent.');
    } catch (error) {
      app.notice(`Not removed. ${error.message}`);
    }
  },
  /** ↑ in an empty composer: edit the last queued message. True when there was one. */
  editLastQueued() {
    const { session } = store.get();
    if (!session || !session.queue) return false;
    const followUps = session.queue.followUps || [];
    const steering = session.queue.steering || [];
    if (followUps.length) app.editQueued('followUp', followUps.length - 1, followUps[followUps.length - 1].text);
    else if (steering.length) app.editQueued('steering', steering.length - 1, steering[steering.length - 1].text);
    else return false;
    return true;
  },
};

const sidebar = createSidebar(document.getElementById('sidebar'), app);
const topbar = createTopbar(app);
conversation = createConversation(app);
composer = createComposer(app);
const settings = createSettings(app);
mainPane.append(topbar.node, conversation.node, composer.node);

function render(state) {
  sidebar.update(state);
  topbar.update(state);
  conversation.update(state);
  composer.update(state);
  settings.update(state);
  const phase = derivePhase(state, Date.now(), fmt);
  attend({ phase, sessionTitle: state.session ? state.session.title : '', notify: state.prefs.notify, hidden: document.hidden });
}
store.subscribe(render);

// ---------------------------------------------------------------- route --
function showRoute(route) {
  const state = store.get();
  if (state.link.status === 'open') {
    if (route.sessionId) bind(route.sessionId).catch(() => {});
    else {
      bind(null).then((session) => navigate(chatHref(session.id, route.settings), { replace: true }), () => {});
    }
  }
  settings.sync(route, store.get());
  render(store.get());
}
onRoute(showRoute);

// Context usage and message counts carry no event: re-read them when a turn ends.
function refreshBoundState(sessionId) {
  run({ type: 'get_connection_state' }).then((fresh) => {
    store.set((state) => (state.session && state.session.id === sessionId && fresh
      ? { session: { ...state.session, state: { ...state.session.state, ...fresh } } }
      : null));
  }, () => {});
}

// --------------------------------------------------------------- frames --
onFrame('event', (frame) => {
  if (opening()) return;
  const state = store.get();
  if (!state.session) return;
  const session = reduce(state.session, frame.event, Date.now());
  store.set({ session: frame.cursor ? { ...session, cursor: frame.cursor } : session });
  switch (frame.event.type) {
    case 'tool_execution_end':
      settleApprovals();
      break;
    case 'agent_end':
      settleApprovals();
      refreshBoundState(session.id);
      refreshSessions().catch(() => {});
      break;
    case 'turn_end':
      refreshBoundState(session.id);
      break;
    case 'session_info_changed':
      refreshSessions().catch(() => {});
      break;
    default:
      break;
  }
});
onFrame('approval', addApproval);
onFrame('resync', () => {
  bind(current().sessionId || app.sessionId(), { force: true }).catch(() => {});
});
onReady(() => {
  const route = current();
  refreshSessions().catch(() => {});
  bind(route.sessionId || null, { force: true }).then((session) => {
    if (!route.sessionId) navigate(chatHref(session.id, route.settings), { replace: true });
  }, () => {});
});

// ------------------------------------------------------------ lifecycle --
document.addEventListener('visibilitychange', () => render(store.get()));
setInterval(() => {
  if (document.hidden) return;
  const phase = derivePhase(store.get(), Date.now(), fmt);
  if (phase.running) store.set({ tick: Date.now() });
}, TICK_MS);

// ------------------------------------------------------------- keyboard --
document.addEventListener('keydown', (event) => {
  const mod = event.metaKey || event.ctrlKey;
  const key = event.key.toLowerCase();
  if (mod && event.shiftKey && key === 'o') {
    event.preventDefault();
    app.newChat();
    return;
  }
  if (mod && !event.shiftKey && key === 'k') {
    event.preventDefault();
    sidebar.focusSearch();
    return;
  }
  if (event.key === 'Escape' && !layerCount()) {
    const field = composer.input;
    const typing = document.activeElement === field && composer.hasText();
    const { session } = store.get();
    if (session && session.turn.running && !typing) {
      event.preventDefault();
      composer.stop();
    }
  }
});

// ----------------------------------------------------------------- boot --
// Earlier builds registered a cache-first service worker; drop it.
if ('serviceWorker' in navigator) {
  navigator.serviceWorker.getRegistrations().then((registrations) => {
    for (const registration of registrations) registration.unregister();
  }, () => {});
}
if ('caches' in window) caches.keys().then((keys) => keys.forEach((key) => caches.delete(key)), () => {});
showRoute(current());
connect();
