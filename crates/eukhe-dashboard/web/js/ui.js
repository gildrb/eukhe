// DOM atoms in the gildrb idiom (no innerHTML, textContent only): `el`,
// SVG icons, text and icon buttons, controls that look like controls
// (segmented, select, field), and the layer stack every overlay shares
// (popovers, bottom sheets, the drawer, dialogs): one Esc, one scrim,
// and on phones one history entry per layer so Back closes it.

const SVG = 'http://www.w3.org/2000/svg';

function isAttrs(value) {
  return value !== null && typeof value === 'object' && !(value instanceof Node) && !Array.isArray(value);
}

function appendChildren(node, children) {
  for (const child of children) {
    if (child === null || child === undefined || child === false) continue;
    if (Array.isArray(child)) appendChildren(node, child);
    else if (child instanceof Node) node.append(child);
    else node.append(String(child));
  }
}

/**
 * `el('a', { href, class, onClick, 'aria-label': … }, child, …)`. Keys
 * starting with `on` attach listeners, booleans toggle attributes, `text`
 * sets textContent, everything else becomes an attribute.
 */
export function el(tag, attrs, ...children) {
  const node = document.createElement(tag);
  if (isAttrs(attrs)) {
    for (const [key, value] of Object.entries(attrs)) {
      if (value === null || value === undefined || value === false) continue;
      if (key === 'text') node.textContent = String(value);
      else if (key.startsWith('on') && typeof value === 'function') node.addEventListener(key.slice(2).toLowerCase(), value);
      else if (value === true) node.setAttribute(key, '');
      else node.setAttribute(key, String(value));
    }
  } else if (attrs !== undefined) {
    children.unshift(attrs);
  }
  appendChildren(node, children);
  return node;
}

// 20×20 strokes (1.5px, round joins) unless noted; fill icons say so.
const ICONS = {
  menu: { stroke: ['M3.5 7h13', 'M3.5 13h9'] },
  newChat: { stroke: ['M9 3.75H5.5a1.75 1.75 0 0 0-1.75 1.75v9a1.75 1.75 0 0 0 1.75 1.75h9a1.75 1.75 0 0 0 1.75-1.75V11', 'M14.6 3.4a1.55 1.55 0 0 1 2.2 2.2L10.5 11.9l-2.9.7.7-2.9z'] },
  chevron: { stroke: ['M6 8l4 4 4-4'] },
  check: { stroke: ['M4.5 10.5l3.5 3.5 7.5-8'] },
  plus: { stroke: ['M10 4.5v11', 'M4.5 10h11'] },
  close: { stroke: ['M5.5 5.5l9 9', 'M14.5 5.5l-9 9'] },
  settings: { stroke: ['M3.5 6h8', 'M15 6h1.5', 'M3.5 14h1.5', 'M8.5 14h8', 'M13 4v4', 'M6.5 12v4'] },
  search: { stroke: ['M9 15a6 6 0 1 0 0-12 6 6 0 0 0 0 12z', 'M13.5 13.5L17 17'] },
  arrowUp: { stroke: ['M10 15.5v-11', 'M5 9.5l5-5 5 5'], width: 2 },
  stop: { fill: ['M6 6h8v8H6z'] },
  sun: { fill: ['M10 2a.75.75 0 0 1 .75.75v1.5a.75.75 0 0 1-1.5 0v-1.5A.75.75 0 0 1 10 2ZM10 15a.75.75 0 0 1 .75.75v1.5a.75.75 0 0 1-1.5 0v-1.5A.75.75 0 0 1 10 15ZM10 7a3 3 0 1 0 0 6 3 3 0 0 0 0-6ZM15.657 5.404a.75.75 0 1 0-1.06-1.06l-1.061 1.06a.75.75 0 0 0 1.06 1.06l1.06-1.06ZM6.464 14.596a.75.75 0 1 0-1.06-1.06l-1.06 1.06a.75.75 0 0 0 1.06 1.06l1.06-1.06ZM18 10a.75.75 0 0 1-.75.75h-1.5a.75.75 0 0 1 0-1.5h1.5A.75.75 0 0 1 18 10ZM5 10a.75.75 0 0 1-.75.75h-1.5a.75.75 0 0 1 0-1.5h1.5A.75.75 0 0 1 5 10ZM14.596 15.657a.75.75 0 0 0 1.06-1.06l-1.06-1.061a.75.75 0 1 0-1.06 1.06l1.06 1.06ZM5.404 6.464a.75.75 0 0 0 1.06-1.06l-1.06-1.06a.75.75 0 0 0-1.061 1.06l1.06 1.06Z'] },
  moon: { fill: ['M7.455 2.004a.75.75 0 0 1 .26.77 7 7 0 0 0 9.958 7.967.75.75 0 0 1 1.067.853A8.5 8.5 0 1 1 6.647 1.921a.75.75 0 0 1 .808.083Z'], evenodd: true },
};

/** An inline SVG icon (`currentColor`), hidden from assistive tech. */
export function icon(name, className = '') {
  const spec = ICONS[name];
  const svg = document.createElementNS(SVG, 'svg');
  svg.setAttribute('viewBox', '0 0 20 20');
  svg.setAttribute('aria-hidden', 'true');
  svg.setAttribute('focusable', 'false');
  svg.setAttribute('class', `icon icon-${name}${className ? ` ${className}` : ''}`);
  for (const d of spec.stroke || []) {
    const path = document.createElementNS(SVG, 'path');
    path.setAttribute('d', d);
    path.setAttribute('fill', 'none');
    path.setAttribute('stroke', 'currentColor');
    path.setAttribute('stroke-width', String(spec.width || 1.5));
    path.setAttribute('stroke-linecap', 'round');
    path.setAttribute('stroke-linejoin', 'round');
    svg.append(path);
  }
  for (const d of spec.fill || []) {
    const path = document.createElementNS(SVG, 'path');
    path.setAttribute('d', d);
    path.setAttribute('fill', 'currentColor');
    if (spec.evenodd) {
      path.setAttribute('fill-rule', 'evenodd');
      path.setAttribute('clip-rule', 'evenodd');
    }
    svg.append(path);
  }
  return svg;
}

/** A text button (gildrb: looks like a link; state is a gray level). */
export function textButton(label, onClick, { kind = 'plain', className = '', title = null } = {}) {
  return el('button', { type: 'button', class: `text-button${className ? ` ${className}` : ''}`, 'data-kind': kind, title, onClick, text: label });
}

/** A square icon button with an accessible label. */
export function iconButton(label, name, onClick, { className = '' } = {}) {
  return el('button', { type: 'button', class: `icon-button${className ? ` ${className}` : ''}`, 'aria-label': label, title: label, onClick }, icon(name));
}

/** A filled control button (`kind: 'primary'` inverts it). */
export function button(label, onClick, { kind = 'plain', type = 'button', className = '' } = {}) {
  return el('button', { type, class: `button${className ? ` ${className}` : ''}`, 'data-kind': kind, onClick, text: label });
}

/** A `Copy` text button that says `Copied` / `Copy failed` for a second. */
export function copyButton(getText, label = 'Copy') {
  const node = textButton(label, async () => {
    let word = 'Copied';
    try {
      await navigator.clipboard.writeText(getText());
    } catch {
      word = 'Copy failed';
    }
    node.textContent = word;
    setTimeout(() => {
      node.textContent = label;
    }, 1000);
  }, { className: 'copy-button' });
  return node;
}

/** Tell screen readers something (`assertive` for approvals and failures). */
export function announce(text, { assertive = false } = {}) {
  const region = document.getElementById(assertive ? 'alerter' : 'announcer');
  if (!region) return;
  region.textContent = '';
  requestAnimationFrame(() => {
    region.textContent = text;
  });
}

let fieldCount = 0;
function nextId(prefix) {
  fieldCount += 1;
  return `${prefix}-${fieldCount}`;
}

/**
 * A segmented control (2–5 options; rectangular, codeBg track). `onPick`
 * may return a promise: the new value shows at once and rolls back with
 * the error when it rejects. Returns the node with `set(value)`.
 */
export function segmented({ label, options, value, onPick, onError = null, size = 'normal' }) {
  const group = el('div', { class: 'segmented', role: 'radiogroup', 'aria-label': label, 'data-size': size });
  let current = value;
  const items = options.map((option) => {
    const spec = typeof option === 'string' ? { value: option, label: option } : option;
    const node = el('button', { type: 'button', role: 'radio', class: 'segment', 'data-value': spec.value, text: spec.label });
    node.addEventListener('click', async () => {
      if (spec.value === current) return;
      const previous = current;
      paint(spec.value);
      try {
        await onPick(spec.value);
      } catch (error) {
        paint(previous);
        if (onError) onError(error);
      }
    });
    node.addEventListener('keydown', (event) => {
      if (!['ArrowLeft', 'ArrowRight'].includes(event.key)) return;
      event.preventDefault();
      const index = items.findIndex((item) => item.node === node);
      const next = items[(index + (event.key === 'ArrowRight' ? 1 : items.length - 1)) % items.length];
      next.node.focus();
      next.node.click();
    });
    group.append(node);
    return { spec, node };
  });
  function paint(next) {
    current = next;
    for (const { spec, node } of items) {
      const on = spec.value === next;
      node.setAttribute('aria-checked', on ? 'true' : 'false');
      node.tabIndex = on || (next === undefined && items[0].spec === spec) ? 0 : -1;
    }
  }
  paint(value);
  group.set = (next) => {
    if (next !== current) paint(next);
  };
  group.value = () => current;
  return group;
}

/** A labelled control row: the label (14/20 secondary) above, the control below. */
export function labelled(text, control, note = null) {
  const id = control.id || nextId('control');
  control.id = id;
  const head = el('span', { class: 'control-label', id: `${id}-label`, text });
  if (control.getAttribute('role') === 'radiogroup') control.setAttribute('aria-labelledby', `${id}-label`);
  const node = el('div', { class: 'control' }, control.tagName === 'DIV' ? head : el('label', { class: 'control-label', for: id, text }), control);
  if (note) node.append(el('p', { class: 'control-note', text: note }));
  return node;
}

/** A styled native select (explicit bg and color). */
export function select({ options, value, onPick, onError = null, label = null }) {
  const node = el('select', { class: 'select', 'aria-label': label });
  for (const option of options) {
    const spec = typeof option === 'string' ? { value: option, label: option } : option;
    const item = el('option', { value: spec.value, text: spec.label });
    if (spec.value === value) item.selected = true;
    node.append(item);
  }
  let current = value;
  node.addEventListener('change', async () => {
    const previous = current;
    current = node.value;
    try {
      await onPick(node.value);
    } catch (error) {
      current = previous;
      node.value = previous;
      if (onError) onError(error);
    }
  });
  node.set = (next) => {
    current = next;
    node.value = next;
  };
  return node;
}

/** A text input (codeBg, radius 8). */
export function input({ value = '', placeholder = '', name = null, type = 'text', label = null, mono = false }) {
  const node = el('input', {
    class: `input${mono ? ' mono' : ''}`,
    type,
    name: name || nextId('input'),
    placeholder,
    autocomplete: 'off',
    autocapitalize: mono ? 'off' : null,
    spellcheck: 'false',
    'aria-label': label,
  });
  node.value = value;
  return node;
}

/** An inline status line (14/20): calm words, or primary 500 for errors. */
export function statusLine() {
  const node = el('p', { class: 'status-line', role: 'status', 'aria-live': 'polite' });
  node.hidden = true;
  node.say = (text, { error = false } = {}) => {
    node.textContent = text || '';
    node.hidden = !text;
    node.dataset.error = error ? 'true' : 'false';
  };
  return node;
}

// ------------------------------------------------------------- layers --

const phone = matchMedia('(max-width: 767px)');
const reducedMotion = matchMedia('(prefers-reduced-motion: reduce)');
const stack = [];
let layerSeq = 0;
// Resolvers of `history.back()` calls the stack made itself (their popstate is not a user Back).
const ownPops = [];

/** True below 768px (phones: sheets instead of popovers, history entries). */
export function isPhone() {
  return phone.matches;
}

function afterMotion(fn, ms) {
  if (reducedMotion.matches) fn();
  else setTimeout(fn, ms);
}

/**
 * Put a layer on the stack. `dismiss()` must remove it from the page;
 * with `history: true` a history entry is pushed so Back closes it.
 * Returns the layer handle `{ close(options) → Promise }`, resolved once
 * the history settled; `close({ replaceWith })` swaps the layer's history
 * entry for a new hash instead of going back.
 */
export function pushLayer({ dismiss, history: wantsHistory = false, restoreFocus = true }) {
  layerSeq += 1;
  const layer = { id: layerSeq, history: wantsHistory, open: true, focus: restoreFocus ? document.activeElement : null };
  layer.close = ({ replaceWith = null, fromPop = false } = {}) => {
    if (!layer.open) return Promise.resolve();
    layer.open = false;
    const index = stack.indexOf(layer);
    if (index >= 0) stack.splice(index, 1);
    dismiss();
    let settled = Promise.resolve();
    if (layer.history && !fromPop) {
      if (replaceWith !== null) location.replace(replaceWith);
      else {
        settled = new Promise((resolve) => ownPops.push(resolve));
        history.back();
      }
    } else if (replaceWith !== null) {
      location.hash = replaceWith.replace(/^#/, '');
    }
    if (layer.focus && layer.focus.isConnected && replaceWith === null) layer.focus.focus({ preventScroll: true });
    return settled;
  };
  if (wantsHistory) history.pushState({ eukheLayer: layer.id }, '', location.href);
  stack.push(layer);
  return layer;
}

/** Close every open layer (e.g. a route change that replaces the view). */
export function closeLayers() {
  while (stack.length) stack[stack.length - 1].close();
}

/** The number of open layers. */
export function layerCount() {
  return stack.length;
}

let settleWaiters = [];

/**
 * Resolves once every `history.back()` a closing layer started has landed.
 * Navigation waits on it, so a closing drawer or sheet can never pop the
 * entry a navigation just pushed (router.js).
 */
export function historySettled() {
  return ownPops.length ? new Promise((resolve) => settleWaiters.push(resolve)) : Promise.resolve();
}

window.addEventListener('popstate', (event) => {
  if (ownPops.length) {
    ownPops.shift()();
    if (!ownPops.length) {
      const waiters = settleWaiters;
      settleWaiters = [];
      for (const resolve of waiters) resolve();
    }
    return;
  }
  const top = stack[stack.length - 1];
  if (!top || !top.history) return;
  const state = event.state;
  if (state && state.eukheLayer === top.id) return;
  top.close({ fromPop: true });
});

document.addEventListener('keydown', (event) => {
  if (event.key !== 'Escape' || !stack.length || event.defaultPrevented) return;
  // A filled search field takes Esc first (it clears); the next Esc closes the layer.
  if (event.target instanceof HTMLInputElement && event.target.type === 'search' && event.target.value) return;
  event.preventDefault();
  event.stopImmediatePropagation();
  stack[stack.length - 1].close();
}, true);

function focusables(root) {
  return [...root.querySelectorAll('a[href], button:not([disabled]), input:not([disabled]), select:not([disabled]), textarea:not([disabled]), [tabindex]:not([tabindex="-1"])')]
    .filter((node) => node.offsetParent !== null || node === document.activeElement);
}

/** Keep Tab inside `root`. */
export function trapFocus(root) {
  root.addEventListener('keydown', (event) => {
    if (event.key !== 'Tab') return;
    const items = focusables(root);
    if (!items.length) return;
    const first = items[0];
    const last = items[items.length - 1];
    if (event.shiftKey && document.activeElement === first) {
      event.preventDefault();
      last.focus();
    } else if (!event.shiftKey && document.activeElement === last) {
      event.preventDefault();
      first.focus();
    }
  });
}

/**
 * A menu: a popover by its anchor on wide screens (radius 8, hairline,
 * no shadow, opacity 120ms), a bottom sheet with 44px rows on phones.
 * `build(panel, close)` fills it. Returns `{ close, panel }`.
 */
export function openMenu({ anchor, above = null, label, placement = 'below', align = 'start', build, onClose = null, className = '' }) {
  const sheet = isPhone();
  const panel = el('div', { class: `menu${sheet ? ' as-sheet' : ''}${className ? ` ${className}` : ''}`, role: 'dialog', 'aria-label': label, tabindex: '-1' });
  const catcher = el('div', { class: `layer-catcher${sheet ? ' scrim-layer' : ''}` });
  const host = el('div', { class: 'layer' }, catcher, panel);
  let layer = null;
  const close = (options) => layer && layer.close(options);
  catcher.addEventListener('pointerdown', (event) => {
    event.preventDefault();
    close();
  });
  layer = pushLayer({
    history: sheet,
    dismiss: () => {
      host.classList.remove('open');
      host.classList.add('closing');
      afterMotion(() => host.remove(), sheet ? 330 : 120);
      if (anchor) anchor.setAttribute('aria-expanded', 'false');
      if (onClose) onClose();
    },
  });
  build(panel, close);
  document.body.append(host);
  if (anchor) anchor.setAttribute('aria-expanded', 'true');
  const place = () => {
    if (sheet || !anchor || !anchor.isConnected) return;
    const rect = anchor.getBoundingClientRect();
    const width = panel.offsetWidth;
    // Item text (4px panel + 12px row padding) lines up with the anchor's text (8px padding).
    const left = align === 'end' ? rect.right - width + 8 : rect.left - 8;
    panel.style.left = `${Math.max(8, Math.min(left, innerWidth - width - 8))}px`;
    if (placement === 'above') {
      const top = above ? above.getBoundingClientRect().top : rect.top;
      panel.style.bottom = `${innerHeight - top + 8}px`;
      panel.style.maxHeight = `${Math.max(160, top - 16)}px`;
    } else {
      panel.style.top = `${rect.bottom + 4}px`;
      panel.style.maxHeight = `${Math.max(160, innerHeight - rect.bottom - 16)}px`;
    }
  };
  place();
  panel.place = place;
  trapFocus(panel);
  requestAnimationFrame(() => {
    host.classList.add('open');
    const first = panel.querySelector('[data-autofocus]') || focusables(panel)[0] || panel;
    first.focus({ preventScroll: true });
  });
  return { close, panel };
}

/** A menu item row (`kind: 'danger'` for Delete…). */
export function menuItem(label, onClick, { trail = null, checked = null, kind = 'plain', role = 'menuitem' } = {}) {
  const node = el('button', {
    type: 'button',
    class: 'menu-item',
    role: checked === null ? role : 'menuitemradio',
    'aria-checked': checked === null ? null : checked ? 'true' : 'false',
    'data-kind': kind,
    onClick,
  }, el('span', { class: 'menu-item-label', text: label }));
  if (trail !== null) node.append(el('span', { class: 'menu-item-trail' }, trail));
  if (checked !== null) node.append(el('span', { class: 'menu-item-check' }, checked ? icon('check') : null));
  return node;
}

/**
 * A centered dialog (confirmations, rename on phones): bg, hairline,
 * radius 8, scrim bg 60%. Returns `{ close, panel, body }`.
 */
export function openDialog({ title, build, onClose = null, className = '' }) {
  const heading = el('h2', { class: 'dialog-title', text: title });
  const body = el('div', { class: 'dialog-body' });
  const panel = el('div', { class: `dialog${className ? ` ${className}` : ''}`, role: 'dialog', 'aria-modal': 'true', 'aria-label': title, tabindex: '-1' }, heading, body);
  const scrim = el('div', { class: 'layer-catcher scrim-layer' });
  const host = el('div', { class: 'layer layer-center' }, scrim, panel);
  let layer = null;
  const close = (options) => layer && layer.close(options);
  scrim.addEventListener('pointerdown', (event) => {
    event.preventDefault();
    close();
  });
  layer = pushLayer({
    history: isPhone(),
    dismiss: () => {
      host.classList.remove('open');
      host.classList.add('closing');
      afterMotion(() => host.remove(), 120);
      if (onClose) onClose();
    },
  });
  build(body, close);
  document.body.append(host);
  trapFocus(panel);
  requestAnimationFrame(() => {
    host.classList.add('open');
    const first = panel.querySelector('[data-autofocus]') || focusables(panel)[0] || panel;
    first.focus({ preventScroll: true });
  });
  return { close, panel, body };
}

/**
 * Ask before a destructive step. With `action` (async), the dialog stays
 * open while it runs and shows its error inline; it closes on success.
 * Resolves true when confirmed (and the action succeeded).
 */
export function confirmDialog({ title, body, confirm, cancel = 'Cancel', action = null, busyLabel = null }) {
  return new Promise((resolve) => {
    let settling = false;
    openDialog({
      title,
      onClose: () => {
        if (!settling) resolve(false);
      },
      build: (root, close) => {
        const status = statusLine();
        const cancelButton = button(cancel, () => close(), { className: 'dialog-cancel' });
        const confirmButton = button(confirm, async () => {
          if (!action) {
            settling = true;
            await close();
            resolve(true);
            return;
          }
          cancelButton.disabled = true;
          confirmButton.disabled = true;
          confirmButton.textContent = busyLabel || confirm;
          status.say('');
          try {
            await action();
            settling = true;
            await close();
            resolve(true);
          } catch (error) {
            status.say(error.message, { error: true });
            cancelButton.disabled = false;
            confirmButton.disabled = false;
            confirmButton.textContent = confirm;
          }
        }, { kind: 'primary' });
        root.append(
          el('p', { class: 'dialog-text', text: body }),
          status,
          el('div', { class: 'dialog-actions' }, cancelButton, confirmButton),
        );
        cancelButton.setAttribute('data-autofocus', '');
      },
    });
  });
}

/** Save `bytes` (base64) as a file through a temporary object URL. */
export function download(name, mimeType, base64) {
  const binary = atob(base64);
  const bytes = new Uint8Array(binary.length);
  for (let index = 0; index < binary.length; index += 1) bytes[index] = binary.charCodeAt(index);
  const url = URL.createObjectURL(new Blob([bytes], { type: mimeType }));
  const link = el('a', { href: url, download: name, class: 'sr-only', tabindex: '-1' });
  document.body.append(link);
  link.click();
  link.remove();
  setTimeout(() => URL.revokeObjectURL(url), 10_000);
}
