// Hash routes, so the app keeps working under a path prefix and every view
// is a link. Grammar:
//   #/                         the most recent session's Chat
//   #/s/<id>[/<page>[/<rest>…]] a session page (chat when <page> is absent)
//   #/<page>[/<rest>…]          a global page (sessions, settings, events)
//   ?<params>&a=<page>[/<rest>…]&a.<key>=<value>  page params, and the aside pane

const SESSION_PAGES = new Set(['chat', 'turn', 'tool', 'memory', 'queue', 'usage', 'model']);
const listeners = new Set();

function split(path) {
  return path.split('/').filter(Boolean).map((part) => decodeURIComponent(part));
}

function parse(hash) {
  const raw = hash.replace(/^#/, '');
  const queryAt = raw.indexOf('?');
  const path = queryAt < 0 ? raw : raw.slice(0, queryAt);
  const query = new URLSearchParams(queryAt < 0 ? '' : raw.slice(queryAt + 1));
  const parts = split(path);
  let page = 'chat';
  let sessionId = null;
  let rest = [];
  if (parts[0] === 's' && parts[1]) {
    sessionId = parts[1];
    page = parts[2] || 'chat';
    rest = parts.slice(3);
  } else if (parts[0] && parts[0] !== 'last') {
    page = parts[0];
    rest = parts.slice(1);
  }
  const params = new URLSearchParams();
  const asideParams = new URLSearchParams();
  let aside = null;
  for (const [key, value] of query) {
    if (key === 'a') {
      const [asidePage, ...asideRest] = split(value);
      if (asidePage) aside = { page: asidePage, rest: asideRest, params: asideParams };
    } else if (key.startsWith('a.')) {
      asideParams.append(key.slice(2), value);
    } else {
      params.append(key, value);
    }
  }
  return { page, sessionId, params, rest, aside };
}

/** The route the address bar shows now. */
export function current() {
  return parse(location.hash);
}

function encodePath(parts) {
  return parts.map((part) => encodeURIComponent(part)).join('/');
}

/** The hash for a page. Session pages need `sessionId`. */
export function href(page, { sessionId = null, rest = [], params = null, aside = null } = {}) {
  let path;
  if (SESSION_PAGES.has(page)) {
    if (!sessionId) return '#/';
    path = page === 'chat' ? `/s/${encodeURIComponent(sessionId)}` : `/s/${encodeURIComponent(sessionId)}/${page}`;
  } else {
    path = `/${encodeURIComponent(page)}`;
  }
  if (rest.length) path += `/${encodePath(rest)}`;
  const query = new URLSearchParams(params || undefined);
  if (aside && aside.page) {
    query.set('a', [aside.page, ...(aside.rest || [])].map((part) => encodeURIComponent(part)).join('/'));
    for (const [key, value] of new URLSearchParams(aside.params || undefined)) query.append(`a.${key}`, value);
  }
  const search = query.toString();
  return `#${path}${search ? `?${search}` : ''}`;
}

function notify() {
  const route = current();
  for (const listener of [...listeners]) listener(route);
}

/** Go to `hrefString` (a `#/…` hash). `replace` keeps history flat. */
export function navigate(hrefString, { replace = false } = {}) {
  const target = hrefString.startsWith('#') ? hrefString : `#${hrefString}`;
  if (target === location.hash) return;
  if (replace) {
    history.replaceState(history.state, '', target);
    notify();
  } else {
    location.hash = target;
  }
}

/** Hear every route change (Back/Forward included). */
export function onRoute(fn) {
  listeners.add(fn);
  return () => listeners.delete(fn);
}

/** True for pages scoped to one session. */
export function isSessionPage(page) {
  return SESSION_PAGES.has(page);
}

window.addEventListener('hashchange', notify);
