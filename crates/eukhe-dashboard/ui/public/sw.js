// Self-destructing service worker. Earlier builds registered a cache-first
// worker; the browser's update check fetches this file, which takes over,
// deletes every cache, unregisters itself and reloads each open tab from
// the network. Nothing registers a worker any more.

self.addEventListener('install', () => {
  self.skipWaiting();
});

self.addEventListener('activate', (event) => {
  event.waitUntil((async () => {
    const keys = await caches.keys();
    await Promise.all(keys.map((key) => caches.delete(key)));
    await self.registration.unregister();
    const clients = await self.clients.matchAll({ type: 'window' });
    await Promise.all(clients.map((client) => client.navigate(client.url).catch(() => null)));
  })());
});
