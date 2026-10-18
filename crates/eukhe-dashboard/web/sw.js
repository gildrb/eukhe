// App-shell service worker: cache-first for the shell (HTML, CSS, JS,
// fonts, icons), never the socket or any API. The cache is named after the
// build (`sw.js?v=<hello.build>`), so a new build replaces the shell.

const VERSION = new URL(self.location.href).searchParams.get('v') || 'dev';
const CACHE = `eukhe-shell-${VERSION}`;
const SHELL = [
  './',
  'index.html',
  'theme.js',
  'manifest.webmanifest',
  'icon.svg',
  'fonts/inter.woff2',
  'fonts/ioskeley-mono.woff2',
  'css/tokens.css',
  'css/base.css',
  'css/shell.css',
  'css/chat.css',
  'css/dock.css',
  'css/pages.css',
  'js/main.js',
  'js/store.js',
  'js/link.js',
  'js/router.js',
  'js/pages.js',
  'js/ui.js',
  'js/format.js',
  'js/markdown.js',
  'js/turn.js',
  'js/viewport.js',
  'js/chat.js',
  'js/composer.js',
  'js/dock.js',
  'js/inbox.js',
  'js/notify.js',
  'js/prefs.js',
  'js/sessions.js',
  'js/binding.js',
  'js/approvals.js',
];

self.addEventListener('install', (event) => {
  event.waitUntil(
    caches.open(CACHE)
      .then((cache) => Promise.allSettled(SHELL.map((path) => cache.add(new Request(path, { cache: 'reload' })))))
      .then(() => self.skipWaiting()),
  );
});

self.addEventListener('activate', (event) => {
  event.waitUntil(
    caches.keys()
      .then((keys) => Promise.all(keys.filter((key) => key.startsWith('eukhe-shell-') && key !== CACHE).map((key) => caches.delete(key))))
      .then(() => self.clients.claim()),
  );
});

const SHELL_EXTENSIONS = /\.(?:html|css|js|woff2|svg|png|webmanifest|txt)$/;

self.addEventListener('fetch', (event) => {
  const { request } = event;
  if (request.method !== 'GET') return;
  const url = new URL(request.url);
  if (url.origin !== self.location.origin || url.pathname.endsWith('/api/ws') || url.pathname.includes('/api/')) return;
  const scope = new URL(self.registration.scope);
  const isNavigation = request.mode === 'navigate';
  if (!isNavigation && !SHELL_EXTENSIONS.test(url.pathname)) return;
  event.respondWith((async () => {
    const cache = await caches.open(CACHE);
    const key = isNavigation ? new URL('index.html', scope).href : request;
    const hit = await cache.match(key, { ignoreSearch: true });
    if (hit) return hit;
    const response = await fetch(request);
    if (response.ok && !isNavigation) cache.put(request, response.clone());
    return response;
  })());
});
