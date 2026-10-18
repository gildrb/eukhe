// The composer: auto-growing 16px textarea on the gildrb drop zone, image
// paste/drop/attach, per-session drafts, ↑ recall, optimistic sends with
// a client admissionId, and one held send while offline.

import { store } from './store.js';
import { request, linkState } from './link.js';
import { el, button } from './ui.js';
import { contentText, withoutSignalRules } from './turn.js';

const DRAFT_DEBOUNCE_MS = 300;
const coarse = matchMedia('(pointer: coarse)');
export const MAC = /Mac|iPhone|iPad/.test(navigator.platform || navigator.userAgent);

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
      const comma = url.indexOf(',');
      resolve({ data: url.slice(comma + 1), mimeType: file.type, preview: URL.createObjectURL(file), name: file.name });
    });
    reader.addEventListener('error', () => reject(reader.error));
    reader.readAsDataURL(file);
  });
}

/**
 * `createComposer()` → `{ node, input, update(ctx, session), submit(mode),
 * fill(text), resend(item), edit(item), retryLast(), focus() }`.
 */
export function createComposer() {
  const input = el('textarea', {
    id: 'composer-input',
    class: 'composer-input',
    name: 'message',
    rows: '1',
    autocomplete: 'off',
    autocapitalize: 'sentences',
    spellcheck: 'true',
    placeholder: 'Message…',
  });
  const label = el('label', { class: 'sr-only', for: 'composer-input', text: 'Message' });
  const images = el('div', { class: 'composer-images' });
  const note = el('p', { class: 'composer-note', role: 'status', 'aria-live': 'polite' });
  const fileInput = el('input', { type: 'file', accept: 'image/*', multiple: true, class: 'sr-only', tabindex: '-1', 'aria-hidden': 'true' });
  const attach = button({ label: 'Attach image', icon: '+', onClick: () => fileInput.click() });
  attach.classList.add('composer-attach');
  const queueChip = button({ label: 'Queue', onClick: () => api.submit('followUp') });
  queueChip.classList.add('composer-queue');
  const primary = button({ label: 'Send', kind: 'primary', type: 'submit' });
  const foot = el('div', { class: 'composer-foot' }, attach, fileInput, queueChip, primary);
  const form = el('form', { class: 'composer', 'aria-label': 'Message composer' }, label, images, input, foot, note);
  note.hidden = true;

  let sessionId = null;
  let busy = false;
  let attached = [];
  let draftTimer = 0;
  let held = null;
  let failed = null;

  const autosize = () => {
    input.style.height = 'auto';
    input.style.height = `${input.scrollHeight}px`;
  };
  const say = (text, retry = null) => {
    note.replaceChildren();
    note.hidden = !text;
    if (!text) return;
    note.append(text);
    if (retry) note.append(' ', button({ label: 'Retry', kind: 'primary', onClick: retry }));
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
      el('img', { src: image.preview, alt: image.name || 'Pasted image', width: '64', height: '64' }),
      button({ label: 'Remove image', icon: '×', onClick: () => {
        URL.revokeObjectURL(image.preview);
        attached = attached.filter((_, at) => at !== index);
        paintImages();
      } }))));
    images.hidden = attached.length === 0;
  };
  const addFiles = async (files) => {
    const picked = [...files].filter((file) => file.type.startsWith('image/'));
    if (!picked.length) return;
    try {
      attached = [...attached, ...(await Promise.all(picked.map(readImage)))];
    } catch {
      say('That image could not be read.');
    }
    paintImages();
  };

  async function send({ text, images: sendImages, mode, id }) {
    const state = store.get();
    const session = state.session;
    if (!session || linkState() !== 'open' || state.link.status !== 'open') {
      held = { text, images: sendImages, mode, id };
      say('Offline. Your message stays here and sends when you’re back.');
      return;
    }
    const queued = session.turn.running;
    const item = { admissionId: id, text, mode, status: 'sending', queued, error: null };
    setPending(session.id, (pending) => [...pending.filter((entry) => entry.admissionId !== id), item]);
    failed = null;
    say('');
    try {
      const fields = { text, mode, admissionId: id };
      if (sendImages.length) fields.images = sendImages.map((image) => ({ data: image.data, mimeType: image.mimeType }));
      await request('prompt', fields);
      try {
        localStorage.setItem(`eukhe.last.${session.id}`, text);
      } catch {
        // Recall falls back to the transcript.
      }
      if (queued) setPending(session.id, (pending) => pending.filter((entry) => entry.admissionId !== id));
    } catch (error) {
      setPending(session.id, (pending) => pending.filter((entry) => entry.admissionId !== id));
      failed = { text, images: sendImages, mode, id };
      if (!input.value.trim()) {
        input.value = text;
        autosize();
        attached = sendImages;
        paintImages();
      }
      say(`Not sent: ${error.message} Edit and send again.`, () => {
        const retry = failed;
        if (!retry) return;
        input.value = '';
        autosize();
        attached = [];
        paintImages();
        send(retry);
      });
    }
  }

  const api = {
    node: form,
    input,
    /** Send the field's text in `mode` ('steer' | 'followUp'); empty → focus. */
    submit(mode) {
      const text = input.value;
      if (!text.trim() && !attached.length) {
        input.focus();
        return;
      }
      const lane = mode || (busy ? 'steer' : 'followUp');
      const sendImages = attached;
      input.value = '';
      attached = [];
      paintImages();
      autosize();
      saveDraft();
      send({ text, images: sendImages, mode: lane, id: admissionId() });
    },
    fill(text) {
      input.value = text;
      autosize();
      saveDraft();
      input.focus();
    },
    focus() {
      input.focus();
    },
    resend(item) {
      send({ text: item.text, images: [], mode: item.mode, id: item.admissionId });
    },
    edit(item) {
      setPending(sessionId, (pending) => pending.filter((entry) => entry.admissionId !== item.admissionId));
      api.fill(item.text);
    },
    retryLast() {
      const session = store.get().session;
      if (!session) return;
      const last = [...session.messages].reverse().find((message) => message.role === 'user');
      if (!last) return;
      send({ text: withoutSignalRules(contentText(last.content)), images: [], mode: 'followUp', id: admissionId() });
    },
    update(ctx, session) {
      if (!session) return;
      if (session.id !== sessionId) {
        sessionId = session.id;
        held = null;
        failed = null;
        say('');
        let draft = '';
        try {
          draft = localStorage.getItem(`eukhe.draft.${session.id}`) || '';
        } catch {
          draft = '';
        }
        input.value = draft;
        autosize();
      }
      busy = session.turn.running;
      const word = busy ? 'Steer' : 'Send';
      const labelNode = primary.querySelector('.btn-label');
      if (labelNode.textContent !== word) labelNode.textContent = word;
      input.placeholder = busy ? 'Steer or queue…' : 'Message…';
      queueChip.hidden = !busy;
      input.enterKeyHint = coarse.matches && !ctx.state.prefs.enterSendsOnTouch ? 'enter' : 'send';
      if (held && ctx.state.link.status === 'open' && linkState() === 'open') {
        const next = held;
        held = null;
        send(next);
      }
    },
  };

  form.addEventListener('submit', (event) => {
    event.preventDefault();
    api.submit(null);
  });
  input.addEventListener('input', () => {
    autosize();
    saveDraft();
  });
  input.addEventListener('keydown', (event) => {
    if (event.isComposing || event.keyCode === 229) return;
    if (event.key === 'Enter') {
      const mod = event.metaKey || event.ctrlKey;
      if (event.altKey && busy) {
        event.preventDefault();
        api.submit('followUp');
        return;
      }
      if (event.shiftKey && !mod) return;
      const enterSends = !coarse.matches || store.get().prefs.enterSendsOnTouch;
      if (mod || enterSends) {
        event.preventDefault();
        api.submit(null);
      }
      return;
    }
    if (event.key === 'ArrowUp' && !input.value && !event.altKey) {
      const session = store.get().session;
      let last = '';
      try {
        last = (session && localStorage.getItem(`eukhe.last.${session.id}`)) || '';
      } catch {
        last = '';
      }
      if (!last && session) {
        const message = [...session.messages].reverse().find((entry) => entry.role === 'user');
        last = message ? withoutSignalRules(contentText(message.content)) : '';
      }
      if (last) {
        event.preventDefault();
        api.fill(last);
      }
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
  images.hidden = true;
  queueChip.hidden = true;
  return api;
}
