// The composer: one box with the same footprint in every state (its only
// size change is its own text growing, in exact 24px lines from 1 to 8),
// attach / paste / drop images, the model button, Steer | Queue while a
// turn runs and the box has text, and the one action button (Send, muted
// Send, Stop). Optimistic sends with a client admissionId; a failure keeps
// the message as "Not sent" with Retry and Edit; drafts persist per chat.

import { store } from './store.js';
import { request, linkState } from './link.js';
import { el, icon, segmented } from './ui.js';
import { setPref } from './prefs.js';
import { modelName, contentText, withoutSignalRules } from './turn.js';

const LINE = 24;
const MAX_LINES = 8;
const FIELD_PADDING = 20; // 12 above, 8 below (css/composer.css)
const DRAFT_DEBOUNCE_MS = 300;
const coarse = matchMedia('(pointer: coarse)');
const nativeSizing = typeof CSS !== 'undefined' && CSS.supports && CSS.supports('field-sizing', 'content');

function admissionId() {
  if (crypto.randomUUID) return crypto.randomUUID();
  const bytes = crypto.getRandomValues(new Uint8Array(16));
  return [...bytes].map((byte) => byte.toString(16).padStart(2, '0')).join('');
}

function setPending(sessionId, fn) {
  store.set((state) => {
    if (!state.session || state.session.id !== sessionId) return null;
    return { session: { ...state.session, pending: fn(state.session.pending) } };
  });
}

function readImage(file) {
  return new Promise((resolve, reject) => {
    const reader = new FileReader();
    reader.addEventListener('load', () => {
      const url = String(reader.result);
      resolve({ data: url.slice(url.indexOf(',') + 1), mimeType: file.type, preview: URL.createObjectURL(file), name: file.name });
    });
    reader.addEventListener('error', () => reject(reader.error));
    reader.readAsDataURL(file);
  });
}

/**
 * `createComposer(app)` → `{ node, input, update(state), fill(text),
 * resend(item), editPending(item), retryLast(), stop(), focus() }`.
 * `app` gives `openModelMenu(anchor)`, `notice(text)`, `editLastQueued()`.
 */
export function createComposer(app) {
  const input = el('textarea', {
    id: 'composer-input',
    class: 'composer-input',
    name: 'message',
    rows: '1',
    autocomplete: 'off',
    autocapitalize: 'sentences',
    spellcheck: 'true',
    placeholder: 'Message eukhe',
    'aria-label': 'Message eukhe',
  });
  const mirror = el('div', { class: 'composer-mirror', 'aria-hidden': 'true' });
  const images = el('div', { class: 'composer-images' });
  images.hidden = true;
  const fileInput = el('input', { type: 'file', accept: 'image/*', multiple: true, class: 'sr-only', tabindex: '-1', 'aria-hidden': 'true' });
  const attach = el('button', { type: 'button', class: 'icon-button composer-attach', 'aria-label': 'Attach images', title: 'Attach images' }, icon('plus'));
  attach.addEventListener('click', () => fileInput.click());
  const modelLabel = el('span', { class: 'model-button-label', text: '' });
  const modelButton = el('button', { type: 'button', class: 'model-button', 'aria-haspopup': 'dialog', 'aria-expanded': 'false' }, modelLabel, icon('chevron'));
  modelButton.addEventListener('click', () => app.openModelMenu(modelButton));
  const lane = segmented({
    label: 'When to send',
    options: [{ value: 'steer', label: 'Steer' }, { value: 'followUp', label: 'Queue' }],
    value: store.get().prefs.lane,
    size: 'small',
    onPick: (value) => setPref('lane', value),
  });
  lane.classList.add('composer-lane');
  lane.hidden = true;
  const action = el('button', { type: 'button', class: 'send-button', 'data-state': 'empty', 'aria-label': 'Send', title: 'Send' }, icon('arrowUp', 'send-icon'), icon('stop', 'stop-icon'));
  const row = el('div', { class: 'composer-row' },
    el('div', { class: 'composer-left' }, attach, modelButton),
    el('div', { class: 'composer-right' }, lane, action));
  const form = el('form', { class: 'composer', 'aria-label': 'Message' }, images, el('div', { class: 'composer-field' }, input, mirror), row, fileInput);
  const node = el('div', { class: 'composer-wrap' }, form);

  let sessionId = null;
  let running = false;
  let attached = [];
  let draftTimer = 0;
  let lines = 1;

  // --------------------------------------------------------- sizing --
  const autosize = () => {
    if (nativeSizing) return;
    mirror.style.width = `${input.clientWidth}px`;
    mirror.textContent = `${input.value}\u200b`;
    const next = Math.min(MAX_LINES, Math.max(1, Math.round(mirror.offsetHeight / LINE)));
    if (next !== lines) {
      lines = next;
      input.style.height = `${lines * LINE + FIELD_PADDING}px`;
    }
  };
  if (!nativeSizing) {
    form.classList.add('measured');
    input.style.height = `${LINE + FIELD_PADDING}px`;
    new ResizeObserver(() => autosize()).observe(input);
  }

  const paintAction = () => {
    const hasText = Boolean(input.value.trim()) || attached.length > 0;
    let word = 'Send';
    let mode = hasText ? 'send' : 'empty';
    if (running && !hasText) {
      word = 'Stop';
      mode = 'stop';
    }
    if (action.dataset.state !== mode) {
      action.dataset.state = mode;
      action.setAttribute('aria-label', word);
      action.title = word;
      action.setAttribute('aria-disabled', mode === 'empty' ? 'true' : 'false');
    }
    lane.hidden = !(running && hasText);
  };

  const saveDraft = () => {
    clearTimeout(draftTimer);
    const id = sessionId;
    const text = input.value;
    draftTimer = setTimeout(() => {
      if (!id) return;
      try {
        if (text) localStorage.setItem(`eukhe.draft.${id}`, text);
        else localStorage.removeItem(`eukhe.draft.${id}`);
      } catch {
        // Storage full or blocked: the draft lives in the field.
      }
    }, DRAFT_DEBOUNCE_MS);
  };

  const paintImages = () => {
    images.replaceChildren(...attached.map((image, index) => el('div', { class: 'composer-image' },
      el('img', { src: image.preview, alt: image.name || 'Attached image' }),
      el('button', {
        type: 'button',
        class: 'icon-button composer-image-remove',
        'aria-label': 'Remove image',
        title: 'Remove image',
        onClick: () => {
          URL.revokeObjectURL(image.preview);
          attached = attached.filter((_, at) => at !== index);
          paintImages();
          paintAction();
        },
      }, icon('close')))));
    images.hidden = attached.length === 0;
  };

  const addFiles = async (files) => {
    const picked = [...files].filter((file) => file.type.startsWith('image/'));
    if (!picked.length) return;
    try {
      attached = [...attached, ...(await Promise.all(picked.map(readImage)))];
    } catch {
      app.notice('That image could not be read.');
    }
    paintImages();
    paintAction();
  };

  const setText = (text) => {
    input.value = text;
    autosize();
    paintAction();
    saveDraft();
  };

  // ---------------------------------------------------------- sends --
  async function send(item) {
    const state = store.get();
    const session = state.session;
    if (!session) return;
    const online = linkState() === 'open' && state.link.status === 'open';
    const entry = { ...item, status: online ? 'sending' : 'held', error: null };
    setPending(session.id, (pending) => [...pending.filter((other) => other.admissionId !== item.admissionId), entry]);
    if (!online) return;
    try {
      const fields = { text: item.text, mode: item.mode, admissionId: item.admissionId };
      if (item.images.length) fields.images = item.images.map((image) => ({ data: image.data, mimeType: image.mimeType }));
      await request('prompt', fields);
      // A message sent while a turn runs is now in the daemon's queue (shown from it).
      if (item.queued) setPending(session.id, (pending) => pending.filter((other) => other.admissionId !== item.admissionId));
    } catch (error) {
      setPending(session.id, (pending) => pending.map((other) => (other.admissionId === item.admissionId ? { ...other, status: 'failed', error: error.message } : other)));
    }
  }

  function submit() {
    const text = input.value;
    if (!text.trim() && !attached.length) return;
    const session = store.get().session;
    if (!session) return;
    const mode = running ? store.get().prefs.lane : 'followUp';
    const item = { admissionId: admissionId(), text, images: attached, mode, queued: running };
    attached = [];
    paintImages();
    setText('');
    send(item);
  }

  function stop() {
    if (!running) return;
    request('abort').catch((error) => app.notice(`Not stopped. ${error.message}`));
  }

  action.addEventListener('click', () => {
    const mode = action.dataset.state;
    if (mode === 'stop') stop();
    else if (mode === 'send') submit();
    else input.focus();
  });
  form.addEventListener('submit', (event) => {
    event.preventDefault();
    submit();
  });
  input.addEventListener('input', () => {
    autosize();
    paintAction();
    saveDraft();
  });
  input.addEventListener('keydown', (event) => {
    if (event.isComposing || event.keyCode === 229) return;
    if (event.key === 'Enter') {
      const mod = event.metaKey || event.ctrlKey;
      if (event.shiftKey && !mod) return;
      const enterSends = !coarse.matches || store.get().prefs.enterSendsOnTouch;
      if (mod || enterSends) {
        event.preventDefault();
        submit();
      }
      return;
    }
    if (event.key === 'ArrowUp' && !input.value && !event.altKey && !event.metaKey && !event.ctrlKey) {
      if (app.editLastQueued()) event.preventDefault();
    }
  });
  input.addEventListener('paste', (event) => {
    const files = event.clipboardData ? [...event.clipboardData.files] : [];
    if (files.some((file) => file.type.startsWith('image/'))) {
      event.preventDefault();
      addFiles(files);
    }
  });
  fileInput.addEventListener('change', () => {
    addFiles(fileInput.files);
    fileInput.value = '';
  });
  form.addEventListener('dragover', (event) => {
    if (event.dataTransfer && [...event.dataTransfer.items].some((item) => item.type.startsWith('image/'))) {
      event.preventDefault();
      form.dataset.drag = 'true';
    }
  });
  form.addEventListener('dragleave', () => {
    delete form.dataset.drag;
  });
  form.addEventListener('drop', (event) => {
    delete form.dataset.drag;
    if (!event.dataTransfer || !event.dataTransfer.files.length) return;
    event.preventDefault();
    addFiles(event.dataTransfer.files);
  });

  let lastModel = null;
  return {
    node,
    input,
    update(state) {
      const session = state.session;
      if (session && session.id !== sessionId) {
        sessionId = session.id;
        let draft = '';
        try {
          draft = localStorage.getItem(`eukhe.draft.${session.id}`) || '';
        } catch {
          draft = '';
        }
        input.value = draft;
        autosize();
      }
      running = Boolean(session && session.turn.running);
      const name = session ? modelName(session.state.model) || 'Model' : 'Model';
      if (name !== lastModel) {
        lastModel = name;
        modelLabel.textContent = name;
      }
      modelButton.disabled = !session;
      lane.set(state.prefs.lane);
      input.enterKeyHint = coarse.matches && !state.prefs.enterSendsOnTouch ? 'enter' : 'send';
      paintAction();
      // Held sends go out once the link is back.
      if (session && state.link.status === 'open' && linkState() === 'open') {
        for (const item of session.pending) if (item.status === 'held') send(item);
      }
    },
    fill(text) {
      setText(text);
      input.focus();
      input.setSelectionRange(text.length, text.length);
    },
    resend(item) {
      send({ ...item, queued: running, mode: running ? item.mode : 'followUp' });
    },
    editPending(item) {
      if (sessionId) setPending(sessionId, (pending) => pending.filter((other) => other.admissionId !== item.admissionId));
      attached = item.images || [];
      paintImages();
      this.fill(item.text);
    },
    retryLast() {
      const session = store.get().session;
      if (!session) return;
      const last = [...session.messages].reverse().find((message) => message.role === 'user');
      if (!last) return;
      send({ admissionId: admissionId(), text: withoutSignalRules(contentText(last.content)), images: [], mode: 'followUp', queued: running });
    },
    stop,
    hasText() {
      return Boolean(input.value.trim());
    },
    focus() {
      input.focus({ preventScroll: true });
    },
  };
}
