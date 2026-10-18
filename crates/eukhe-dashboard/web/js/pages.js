// The page registry. A page renders into a root element it owns; the host
// calls `update` on every store or route change while it is mounted.

import { store } from './store.js';
import { request, run } from './link.js';
import { current, href, navigate } from './router.js';
import * as ui from './ui.js';
import { fmt } from './format.js';

const registry = new Map();

/** Register a page: `{ id, title(ctx), render(root, ctx), update?(root, ctx), dispose?(root) }`. */
export function definePage(spec) {
  registry.set(spec.id, spec);
  return spec;
}

/** The registered page for `id`, or undefined. */
export function pageFor(id) {
  return registry.get(id);
}

function context(route, pane) {
  return { state: store.get(), route, request, run, navigate, href, ui, fmt, pane };
}

/**
 * One pane's mounted page. `show(id, route)` mounts (or updates) a page;
 * `refresh()` re-runs `update` against the latest state.
 */
export class PageHost {
  constructor(root, pane) {
    this.root = root;
    this.pane = pane;
    this.spec = null;
    this.route = null;
    this.body = null;
  }

  show(id, route) {
    const spec = registry.get(id);
    this.route = route;
    if (spec === this.spec && this.body) {
      this.refresh();
      return;
    }
    this.dispose();
    this.spec = spec || null;
    this.body = ui.el('div', { class: 'page', 'data-page': id });
    this.root.replaceChildren(this.body);
    if (!spec) {
      this.body.append(ui.empty({ title: 'Nothing here', body: `There is no page called “${id}”.`, action: { label: 'Go to the chat', href: '#/' } }));
      return;
    }
    spec.render(this.body, context(route, this.pane));
  }

  refresh() {
    if (!this.spec || !this.body || !this.spec.update) return;
    this.spec.update(this.body, context(this.route || current(), this.pane));
  }

  title() {
    if (!this.spec || !this.spec.title) return '';
    return this.spec.title(context(this.route || current(), this.pane));
  }

  dispose() {
    if (this.spec && this.spec.dispose && this.body) this.spec.dispose(this.body);
    this.spec = null;
    this.body = null;
    this.root.replaceChildren();
  }
}
