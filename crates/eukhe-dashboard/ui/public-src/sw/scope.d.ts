// sw.js runs as a classic service worker script, so it cannot declare `self` as a
// ServiceWorkerGlobalScope: lib.webworker types `self` as a WorkerGlobalScope, and a module's
// `declare const self` would make the script an ES module. The service worker members sw.ts uses
// merge into the lib's interfaces instead (merging needs `interface`; a `type` cannot).

interface WorkerGlobalScope {
  readonly clients: ServiceWorkerGlobalScope["clients"];
  readonly registration: ServiceWorkerGlobalScope["registration"];
  skipWaiting: ServiceWorkerGlobalScope["skipWaiting"];
}

interface WorkerGlobalScopeEventMap {
  install: ExtendableEvent;
  activate: ExtendableEvent;
}
