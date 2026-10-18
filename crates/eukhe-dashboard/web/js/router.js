// Hash routes: `#/c/<sessionId>` is a chat; `#/c/<id>/settings[/<section>]`
// overlays Settings on it; `#/settings[/<section>]` overlays Settings on
// the newest chat; `#/` opens the newest chat.

import { historySettled } from './ui.js';

const listeners = new Set();

/** The current route: `{ sessionId, settings: null | '' | section }`. */
export function current() {
  const parts = location.hash.replace(/^#\/?/, '').split('/').filter(Boolean).map(decodeURIComponent);
  let sessionId = null;
  let rest = parts;
  if (parts[0] === 'c' && parts[1]) {
    sessionId = parts[1];
    rest = parts.slice(2);
  }
  const settings = rest[0] === 'settings' ? rest[1] || '' : null;
  return { sessionId, settings };
}

/** The hash for a chat (and optionally a Settings section over it). */
export function chatHref(sessionId, settings = null) {
  let hash = sessionId ? `#/c/${encodeURIComponent(sessionId)}` : '#/';
  if (settings !== null) hash = `${sessionId ? hash : '#'}/settings${settings ? `/${encodeURIComponent(settings)}` : ''}`;
  return hash;
}

/**
 * Go to `hash`; `replace` keeps the history length. Waits until closing
 * overlays have consumed their own history entries (ui.js), so the
 * navigation is never undone by their `history.back()`.
 */
export function navigate(hash, { replace = false } = {}) {
  return historySettled().then(() => {
    if (location.hash === hash) return;
    if (replace) location.replace(hash);
    else location.hash = hash.replace(/^#/, '');
  });
}

/** Hear route changes. */
export function onRoute(fn) {
  listeners.add(fn);
  return () => listeners.delete(fn);
}

window.addEventListener('hashchange', () => {
  const route = current();
  for (const fn of [...listeners]) fn(route);
});
