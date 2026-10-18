// The Dock under the transcript: status line (derivePhase), the inverted
// approval card, the queue strip, the composer, the lane bar (busy only)
// and the nav row. Everything is one tap and never moves.

import { store } from './store.js';
import { request, run, reconnect } from './link.js';
import { el, button, sheet, toast } from './ui.js';
import { derivePhase, effectWords } from './turn.js';
import { answerApproval } from './approvals.js';
import { createComposer, MAC } from './composer.js';
import { trackDockHeight } from './viewport.js';
import { fmt } from './format.js';
import { href } from './router.js';

const UNDO_MS = 5000;
const KEYS = MAC ? { alt: '⌥', enter: '↵' } : { alt: 'Alt+', enter: '↵' };

function openSessionSheet(ctx) {
  import('./pages/session-sheet.js')
    .then((module) => module.openSessionSheet(ctx))
    .catch(() => toast({ text: 'Session settings are not available in this build.', error: true }));
}

function pulseParts(phase) {
  const parts = [el('span', { class: 'pulse-phase', text: phase.label })];
  if (phase.detail) parts.push(el('span', { class: 'pulse-sep', text: ' · ' }), el('span', { class: 'pulse-detail', translate: 'no', text: phase.detail }));
  phase.metrics.forEach((metric, index) => {
    const low = index === phase.metrics.length - 1 && index > 0;
    parts.push(el('span', { class: 'pulse-metric', 'data-priority': low ? 'low' : null }, el('span', { class: 'pulse-sep', text: ' · ' }), metric));
  });
  return parts;
}

/** Queue-lane mutation through MutateQueuedMessage; resolves the daemon's status word. */
async function mutate(lane, index, expectedText, mutation) {
  const data = await run({ type: 'mutate_queued_message', lane, index, expectedText, mutation });
  return data && data.status ? data.status : 'applied';
}

function queueSheet(item) {
  const text = el('textarea', { class: 'field-input', rows: '4', 'aria-label': 'Queued message' });
  text.value = item.text;
  const other = item.lane === 'steering' ? 'followUp' : 'steering';
  const otherWord = other === 'steering' ? 'Steer' : 'Queue';
  const report = (status) => {
    if (status !== 'applied') toast({ text: status === 'rejected' ? 'It already ran.' : `The daemon said “${status}”.` });
  };
  const handle = sheet({
    title: item.lane === 'steering' ? 'Steer' : 'Queued',
    content: text,
    actions: [
      button({ label: 'Delete', kind: 'danger', onClick: async () => {
        handle.close();
        const { undone } = toast({ text: 'Queued message deleted.', undo: UNDO_MS });
        if (await undone) return;
        mutate(item.lane, item.index, item.text, { type: 'delete' }).then(report, (error) => toast({ text: error.message, error: true }));
      } }),
      button({ label: `Move to ${otherWord}`, onClick: () => {
        handle.close();
        mutate(item.lane, item.index, item.text, { type: 'replace', text: text.value.trim() || item.text, lane: other }).then(report, (error) => toast({ text: error.message, error: true }));
      } }),
      button({ label: 'Save', kind: 'primary', onClick: () => {
        handle.close();
        const next = text.value.trim();
        const mutation = next ? { type: 'replace', text: next, lane: item.lane } : { type: 'delete' };
        mutate(item.lane, item.index, item.text, mutation).then(report, (error) => toast({ text: error.message, error: true }));
      } }),
    ],
  });
}

/** `createDock(ctx)` → `{ node, update(ctx, session), fill, resend, edit, retryLast, dispose }`. */
export function createDock(initialCtx) {
  let ctx = initialCtx;
  const composer = createComposer();
  const pulseLink = el('a', { class: 'pulse', href: '#/' });
  const pulseText = el('span', { class: 'pulse-text' });
  pulseLink.append(pulseText, el('span', { class: 'pulse-go', 'aria-hidden': 'true', text: '⌃' }));
  const pulseActions = el('div', { class: 'pulse-actions' });
  const pulseRow = el('div', { class: 'pulse-row' }, pulseLink, pulseActions);
  const approvalSlot = el('div', { class: 'approval-slot' });
  const queueSlot = el('div', { class: 'queue-slot' });

  let stopping = false;
  const stop = button({ label: 'Stop', hint: 'Esc', onClick: () => api.stop() });
  const queue = button({ label: 'Queue', hint: `${KEYS.alt}${KEYS.enter}`, onClick: () => composer.submit('followUp') });
  const steer = button({ label: 'Steer', kind: 'primary', hint: KEYS.enter, onClick: () => composer.submit('steer') });
  const lanes = el('div', { class: 'lanes', role: 'group', 'aria-label': 'Turn controls' }, stop, el('div', { class: 'lanes-right' }, queue, steer));

  const back = el('a', { class: 'link navrow-back', href: '#/sessions', text: '← Chats' });
  const title = el('button', { type: 'button', class: 'navrow-title', 'aria-haspopup': 'dialog', onClick: () => openSessionSheet(ctx) });
  const more = button({ label: 'Session settings', icon: '⋯', onClick: () => openSessionSheet(ctx) });
  more.classList.add('navrow-more');
  more.setAttribute('aria-haspopup', 'dialog');
  const navrow = el('nav', { class: 'navrow', 'aria-label': 'Session' }, back, title, more);

  const inner = el('div', { class: 'dock-inner' }, pulseRow, approvalSlot, queueSlot, composer.node, lanes, navrow);
  const node = el('div', { class: 'dock' }, inner);
  const untrack = trackDockHeight(node);

  let approvalSig = '';
  let queueSig = '';
  let queueOpen = false;
  let pulseSig = '';

  const paintPulse = (phase, session) => {
    const sig = `${phase.phase}|${phase.label}|${phase.detail}|${phase.metrics.join('|')}`;
    if (sig === pulseSig) return;
    pulseSig = sig;
    pulseText.replaceChildren(...pulseParts(phase));
    pulseLink.dataset.dim = phase.phase === 'catchingUp' ? 'true' : 'false';
    pulseLink.setAttribute('href', session ? href('turn', { sessionId: session.id }) : '#/');
    pulseLink.setAttribute('aria-label', `${phase.label}${phase.detail ? `, ${phase.detail}` : ''}. Open the turn.`);
    const actions = [];
    switch (phase.phase) {
      case 'offline':
      case 'unavailable':
        actions.push(button({ label: 'Retry', kind: 'primary', onClick: reconnect }));
        break;
      case 'retrying':
        actions.push(button({ label: 'Cancel', onClick: () => run({ type: 'abort_retry' }).catch((error) => toast({ text: error.message, error: true })) }));
        break;
      case 'compacting':
        actions.push(button({ label: 'Cancel', onClick: () => run({ type: 'abort_compaction' }).catch((error) => toast({ text: error.message, error: true })) }));
        break;
      case 'failed':
        actions.push(button({ label: 'Retry', kind: 'primary', onClick: () => composer.retryLast() }));
        break;
      case 'bash':
        actions.push(button({ label: 'Stop', onClick: () => run({ type: 'abort_bash' }).catch((error) => toast({ text: error.message, error: true })) }));
        break;
      default:
        break;
    }
    pulseActions.replaceChildren(...actions);
  };

  let tapped = null;
  const paintApproval = (approvals) => {
    const live = approvals;
    const sig = live.map((item) => `${item.requestId}:${item.status}`).join(',');
    if (sig === approvalSig) return;
    const arriving = !approvalSig && sig;
    approvalSig = sig;
    if (!live.length) {
      approvalSlot.replaceChildren();
      return;
    }
    const first = live[0];
    const answering = first.status === 'answering';
    const elsewhere = first.status === 'elsewhere';
    const command = el('div', { class: 'approval-command', translate: 'no', text: first.command });
    const answer = (verdict) => () => {
      if (first.status !== 'pending') return;
      tapped = { requestId: first.requestId, verdict };
      answerApproval(first.requestId, verdict);
    };
    const tappedVerdict = answering && tapped && tapped.requestId === first.requestId ? tapped.verdict : null;
    const deny = button({ label: tappedVerdict === 'deny' ? 'Denying' : 'Deny', busy: tappedVerdict === 'deny', hint: 'D', onClick: answer('deny') });
    const approve = button({ label: tappedVerdict === 'approve' ? 'Approving' : 'Approve', busy: tappedVerdict === 'approve', hint: 'A', onClick: answer('approve') });
    if (answering || elsewhere) {
      deny.disabled = true;
      approve.disabled = true;
    }
    const head = el('div', { class: 'approval-head' },
      el('span', { text: elsewhere ? 'Answered elsewhere' : `Needs approval · bash step ${first.step + 1}` }),
      live.length > 1 ? el('span', { class: 'fig', text: `1 of ${fmt.num(live.length)}` }) : null);
    const card = el('section', { class: 'approval', tabindex: '-1', role: 'alertdialog', 'aria-label': 'Needs approval' },
      head, command, el('div', { class: 'approval-effect', text: effectWords(first.effect) }));
    if (first.command.split('\n').length > 4 || first.command.length > 240) {
      const all = button({ label: 'Show all', onClick: () => {
        command.dataset.all = 'true';
        all.remove();
      } });
      all.classList.add('btn-show');
      card.append(all);
    }
    card.append(el('div', { class: 'approval-actions' }, deny, approve));
    card.addEventListener('keydown', (event) => {
      if (event.metaKey || event.ctrlKey || event.altKey) return;
      if (event.key === 'a' || event.key === 'A') answer('approve')();
      else if (event.key === 'd' || event.key === 'D') answer('deny')();
    });
    approvalSlot.replaceChildren(card);
    if (arriving && document.activeElement !== composer.input) card.focus({ preventScroll: true });
  };

  const paintQueue = (session) => {
    const items = [];
    if (session) {
      session.queue.steering.forEach((entry, index) => items.push({ lane: 'steering', index, text: entry.text, origin: entry.origin }));
      session.queue.followUps.forEach((entry, index) => items.push({ lane: 'followUp', index, text: entry.text, origin: entry.origin }));
      for (const pending of session.pending.filter((entry) => entry.queued)) {
        items.push({ lane: pending.mode === 'steer' ? 'steering' : 'followUp', index: -1, text: pending.text, sending: pending.status === 'sending' });
      }
    }
    const sig = `${queueOpen}|${items.map((item) => `${item.lane}:${item.text}:${item.sending ? 1 : 0}`).join('\u0001')}`;
    if (sig === queueSig) return;
    queueSig = sig;
    if (!items.length) {
      queueSlot.replaceChildren();
      return;
    }
    const row = (item) => {
      const internal = item.index < 0 || (item.origin && item.origin.kind && item.origin.kind !== 'user');
      const word = item.lane === 'steering' ? 'Steer' : 'Next';
      const node = el(internal ? 'div' : 'button', {
        class: 'queue-item',
        type: internal ? null : 'button',
        'data-internal': internal ? 'true' : null,
        onClick: internal ? null : () => queueSheet(item),
      }, el('span', { class: 'queue-item-lane', text: word }), el('span', { class: 'queue-item-text', text: `${item.text}${item.sending ? ' (sending…)' : ''}` }));
      return node;
    };
    const strip = el('div', { class: 'queue-strip', role: 'region', 'aria-label': 'Queued messages' });
    if (items.length === 1) strip.append(row(items[0]));
    else {
      const steers = items.filter((item) => item.lane === 'steering').length;
      const summary = `${fmt.num(items.length)} queued · ${fmt.num(steers)} steer, ${fmt.num(items.length - steers)} next`;
      const toggle = button({ label: summary, onClick: () => {
        queueOpen = !queueOpen;
        paintQueue(store.get().session);
      } });
      toggle.setAttribute('aria-expanded', queueOpen ? 'true' : 'false');
      toggle.classList.add('queue-strip-summary');
      strip.append(toggle);
      if (queueOpen) {
        strip.append(el('div', { class: 'queue-list' }, items.map(row)));
        strip.append(el('div', { class: 'lanes' }, el('span'), button({ label: 'Clear queue', onClick: async () => {
          const { undone } = toast({ text: 'Queue cleared.', undo: UNDO_MS });
          if (await undone) return;
          run({ type: 'clear_queue' }).catch((error) => toast({ text: error.message, error: true }));
        } })));
      }
    }
    queueSlot.replaceChildren(strip);
  };

  const api = {
    node,
    update(nextCtx, session) {
      ctx = nextCtx;
      const state = nextCtx.state;
      const phase = derivePhase({ ...state, session }, Date.now(), fmt);
      paintPulse(phase, session);
      node.style.setProperty('--progress', phase.progress !== null && phase.progress !== undefined ? String(phase.progress) : '0');
      paintApproval(state.approvals);
      // An approval replaces the status area.
      pulseRow.hidden = state.approvals.length > 0;
      paintQueue(session);
      composer.update(nextCtx, session);
      const running = Boolean(session && session.turn.running);
      if (!running) stopping = false;
      lanes.hidden = !running;
      const steering = session ? session.queue.steering.length : 0;
      const stopWord = stopping ? 'Stopping…' : steering ? 'Stop & steer' : 'Stop';
      const stopLabel = stop.querySelector('.btn-label');
      if (stopLabel.textContent !== stopWord) stopLabel.textContent = stopWord;
      stop.disabled = stopping;
      const titleText = session ? session.title : 'eukhe';
      if (title.textContent !== titleText) title.textContent = titleText;
      title.setAttribute('aria-label', `${titleText}: session settings`);
    },
    /** Stop the turn (or abort and deliver queued steering). */
    stop() {
      const session = store.get().session;
      if (!session || !session.turn.running || stopping) return;
      stopping = true;
      api.update(ctx, session);
      const call = session.queue.steering.length ? run({ type: 'abort_and_send_queued' }) : request('abort');
      call.catch((error) => {
        stopping = false;
        toast({ text: `Stop failed: ${error.message}`, error: true });
      });
    },
    fill: (text) => composer.fill(text),
    focus: () => composer.focus(),
    resend: (item) => composer.resend(item),
    edit: (item) => composer.edit(item),
    retryLast: () => composer.retryLast(),
    dispose() {
      untrack();
    },
  };
  node.dockApi = api;
  return api;
}
