// DOM atoms in the gildrb idiom: buttons look like text, state is a gray
// level, and nothing is built from HTML strings (textContent only).

const SHOW_DELAY_MS = 150;
const MIN_SHOWN_MS = 300;

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

/** A text button. `kind` sets its gray level; `busy` keeps the label and adds `…`. */
export function button({ label, icon = null, onClick, kind = 'plain', busy = false, type = 'button', hint = null, title = null, current = false }) {
  const node = el('button', {
    type,
    class: 'btn target',
    'data-kind': kind,
    'aria-label': icon ? label : null,
    title: title || (icon ? label : null),
    'aria-busy': busy ? 'true' : null,
    'aria-pressed': current ? 'true' : null,
    disabled: busy,
    onClick,
  });
  if (icon) node.append(el('span', { class: 'btn-icon', 'aria-hidden': 'true', text: icon }));
  else node.append(el('span', { class: 'btn-label', text: busy ? `${label}…` : label }));
  if (hint) node.append(el('kbd', { class: 'hint', 'aria-hidden': 'true', text: hint }));
  return node;
}

/** A list row: lead · title/detail · trail. A link with `href`, else a button. */
export function row({ lead = null, title, detail = null, trail = null, href = null, onClick = null, current = false }) {
  const attrs = { class: 'row', 'aria-current': current ? 'true' : null };
  const node = href ? el('a', { ...attrs, href }) : onClick ? el('button', { ...attrs, type: 'button', onClick }) : el('div', attrs);
  if (href && onClick) node.addEventListener('click', onClick);
  if (lead !== null) node.append(el('span', { class: 'row-lead' }, lead));
  const body = el('span', { class: 'row-body' }, el('span', { class: 'row-title' }, title));
  if (detail !== null) body.append(el('span', { class: 'row-detail' }, detail));
  node.append(body);
  if (trail !== null) node.append(el('span', { class: 'row-trail' }, trail));
  return node;
}

const reducedMotion = matchMedia('(prefers-reduced-motion: reduce)');

/**
 * A modal sheet (native <dialog>: focus trap and Esc for free). A bottom
 * sheet on phones, a right pane from 768px. Returns `{ close, dialog, body }`.
 */
export function sheet({ title, content, onClose = null, actions = null }) {
  const heading = el('h2', { class: 'sheet-title', text: title });
  const body = el('div', { class: 'sheet-body' });
  appendChildren(body, [content]);
  let closed = false;
  const dialog = el('dialog', { class: 'sheet', 'aria-label': title });
  const close = () => {
    if (closed) return;
    closed = true;
    dialog.classList.remove('open');
    const done = () => {
      dialog.close();
      dialog.remove();
      if (onClose) onClose();
    };
    if (reducedMotion.matches) done();
    else setTimeout(done, 330);
  };
  const footer = el('div', { class: 'sheet-footer' });
  appendChildren(footer, [actions]);
  footer.append(button({ label: 'Close', onClick: close }));
  dialog.append(el('div', { class: 'sheet-handle', 'aria-hidden': 'true' }), heading, body, footer);
  dialog.addEventListener('cancel', (event) => {
    event.preventDefault();
    close();
  });
  dialog.addEventListener('click', (event) => {
    if (event.target === dialog) close();
  });
  document.body.append(dialog);
  dialog.showModal();
  requestAnimationFrame(() => dialog.classList.add('open'));
  return { close, dialog, body };
}

/** Ask before a destructive step. `action` is the confirm label (or `{ label, kind }`). */
export function confirm({ title, body, action }) {
  const spec = typeof action === 'string' ? { label: action, kind: 'danger' } : action;
  return new Promise((resolve) => {
    let answer = false;
    const handle = sheet({
      title,
      content: el('p', { class: 'sheet-text', text: body }),
      onClose: () => resolve(answer),
      actions: button({
        label: spec.label,
        kind: spec.kind || 'danger',
        onClick: () => {
          answer = true;
          handle.close();
        },
      }),
    });
  });
}

let toastRegion = null;

function toastHost() {
  if (!toastRegion || !toastRegion.isConnected) {
    toastRegion = el('div', { class: 'toasts', role: 'status', 'aria-live': 'polite' });
    document.body.append(toastRegion);
  }
  return toastRegion;
}

/**
 * A short text note. `action: { label, onClick }` adds a button; `undo: ms`
 * adds Undo for that long. Returns `{ close, undone: Promise<boolean> }`.
 */
export function toast({ text, action = null, undo = 0, error = false }) {
  const node = el('div', { class: 'toast', 'data-error': error ? 'true' : null }, el('span', { class: 'toast-text', text }));
  let settle;
  const undone = new Promise((resolve) => {
    settle = resolve;
  });
  let timer = 0;
  const close = (wasUndone) => {
    clearTimeout(timer);
    node.remove();
    settle(wasUndone);
  };
  if (action) {
    node.append(button({ label: action.label, onClick: () => {
      action.onClick();
      close(false);
    } }));
  }
  if (undo > 0) node.append(button({ label: 'Undo', kind: 'primary', onClick: () => close(true) }));
  toastHost().append(node);
  const lifetime = undo > 0 ? undo : error ? 0 : 4000;
  if (lifetime > 0) timer = setTimeout(() => close(false), lifetime);
  else node.append(button({ label: 'Dismiss', onClick: () => close(false) }));
  return { close: () => close(false), undone };
}

/** Placeholder lines with the geometry of real 24px rows. */
export function skeleton(lines = 3) {
  const node = el('div', { class: 'skeleton', 'aria-hidden': 'true' });
  for (let index = 0; index < lines; index += 1) node.append(el('span', { class: 'skeleton-line', 'data-n': String(index % 4) }));
  return node;
}

/** A titled section. */
export function section(title, ...children) {
  const node = el('section', { class: 'section' });
  if (title) node.append(el('h2', { class: 'section-title', text: title }));
  appendChildren(node, children);
  return node;
}

let fieldCount = 0;

/** A labelled bare input. `onCommit` fires on Enter and on change. */
export function field({ label, value = '', type = 'text', inputmode = null, placeholder = null, onInput = null, onCommit = null, name = null, autocomplete = 'off' }) {
  fieldCount += 1;
  const id = `field-${fieldCount}`;
  const input = el('input', {
    id,
    class: 'field-input',
    type,
    inputmode,
    placeholder,
    name: name || id,
    autocomplete,
    spellcheck: 'false',
  });
  input.value = value;
  if (onInput) input.addEventListener('input', () => onInput(input.value));
  if (onCommit) {
    input.addEventListener('change', () => onCommit(input.value));
    input.addEventListener('keydown', (event) => {
      if (event.key === 'Enter' && !event.isComposing) {
        event.preventDefault();
        onCommit(input.value);
      }
    });
  }
  return el('label', { class: 'field', for: id }, el('span', { class: 'field-label', text: label }), input);
}

/** An on/off switch whose state is a word, not a color. */
export function toggle({ label, checked, onChange }) {
  const state = el('span', { class: 'toggle-state', text: checked ? 'On' : 'Off' });
  const node = el('button', {
    type: 'button',
    class: 'toggle target',
    role: 'switch',
    'aria-checked': checked ? 'true' : 'false',
  }, el('span', { class: 'toggle-label', text: label }), state);
  node.addEventListener('click', () => {
    const next = node.getAttribute('aria-checked') !== 'true';
    node.setAttribute('aria-checked', next ? 'true' : 'false');
    state.textContent = next ? 'On' : 'Off';
    onChange(next);
  });
  return node;
}

/** A native select. `options` are strings or `{ value, label }`. */
export function select({ label, options, value, onChange }) {
  fieldCount += 1;
  const id = `field-${fieldCount}`;
  const node = el('select', { id, class: 'select-input', name: id });
  for (const option of options) {
    const spec = typeof option === 'string' ? { value: option, label: option } : option;
    const item = el('option', { value: spec.value, text: spec.label });
    if (spec.value === value) item.selected = true;
    node.append(item);
  }
  node.addEventListener('change', () => onChange(node.value));
  return el('label', { class: 'field select', for: id }, el('span', { class: 'field-label', text: label }), node);
}

/** An empty or error state with an optional way out. */
export function empty({ title, body = null, action = null }) {
  const node = el('div', { class: 'empty' }, el('p', { class: 'empty-title', text: title }));
  if (body) node.append(el('p', { class: 'empty-body', text: body }));
  if (action) {
    node.append(action.href
      ? el('a', { class: 'link target', href: action.href, text: action.label })
      : button({ label: action.label, kind: 'primary', onClick: action.onClick }));
  }
  return node;
}

/**
 * A container for async content: a skeleton appears only after 150ms and
 * stays at least 300ms; then `render(value)` replaces it. Failures show
 * the error with Retry when `retry` is given.
 */
export function delayed(promise, render, { lines = 3, retry = null } = {}) {
  const host = el('div', { class: 'delayed', 'aria-busy': 'true' });
  let shownAt = 0;
  const timer = setTimeout(() => {
    shownAt = performance.now();
    host.replaceChildren(skeleton(lines));
  }, SHOW_DELAY_MS);
  const finish = (paint) => {
    clearTimeout(timer);
    const wait = shownAt ? Math.max(0, MIN_SHOWN_MS - (performance.now() - shownAt)) : 0;
    setTimeout(() => {
      host.removeAttribute('aria-busy');
      host.replaceChildren();
      paint();
    }, wait);
  };
  promise.then(
    (value) => finish(() => appendChildren(host, [render(value)])),
    (error) => finish(() => host.append(empty({
      title: 'Could not load this.',
      body: error && error.message ? error.message : String(error),
      action: retry ? { label: 'Try again', onClick: () => host.replaceWith(delayed(retry(), render, { lines, retry })) } : null,
    }))),
  );
  return host;
}

/** A `Copy` text button that says `Copied` / `Copy failed` for a second. */
export function copyButton(getText, label = 'Copy') {
  const node = button({ label, onClick: async () => {
    const text = node.querySelector('.btn-label');
    try {
      await navigator.clipboard.writeText(getText());
      text.textContent = 'Copied';
    } catch {
      text.textContent = 'Copy failed';
    }
    setTimeout(() => {
      text.textContent = label;
    }, 1000);
  } });
  node.classList.add('copy');
  return node;
}

let announcer = null;

/** Say `text` politely to assistive tech (phase changes only, never tokens). */
export function announce(text, { assertive = false } = {}) {
  if (!announcer || !announcer.isConnected) announcer = document.getElementById('announcer');
  if (!announcer) return;
  announcer.setAttribute('aria-live', assertive ? 'assertive' : 'polite');
  announcer.textContent = '';
  requestAnimationFrame(() => {
    announcer.textContent = text;
  });
}
