// Attention while away: document title, app badge, aria-live phase
// announcements, and (opt-in, hidden tab only) a Notification when a turn
// finishes, fails or needs approval. Everything renders from derivePhase.

import { announce } from './ui.js';

let lastPhase = null;
let lastAnnounced = '';
let lastBadge = -1;
let lastTitle = '';

const FINISHED = new Set(['idle', 'stopped']);

function show(title, body, tag) {
  try {
    const notification = new Notification(title, { body, tag, icon: 'icons/icon-192.png' });
    notification.addEventListener('click', () => {
      window.focus();
      notification.close();
    });
  } catch {
    // Some platforms only allow notifications from a service worker.
  }
}

/**
 * Called on every state change with the bound session's phase and title.
 * `pageTitle` is the current page's own title (empty on Chat).
 */
export function attend({ phase, sessionTitle, pageTitle, needsYou, notify, hidden }) {
  const status = phase.phase === 'approval'
    ? '● Needs approval'
    : phase.phase === 'failed'
      ? 'Failed'
      : ['writing', 'thinking', 'tool', 'tools', 'prefill', 'waiting', 'retrying', 'compacting', 'bash', 'admission'].includes(phase.phase)
        ? `${phase.phase === 'thinking' ? 'Thinking' : 'Working'}…`
        : '';
  const title = [status, pageTitle, sessionTitle, 'eukhe'].filter(Boolean).join(' · ');
  if (title !== lastTitle) {
    document.title = title;
    lastTitle = title;
  }

  if (needsYou !== lastBadge && 'setAppBadge' in navigator) {
    lastBadge = needsYou;
    (needsYou ? navigator.setAppBadge(needsYou) : navigator.clearAppBadge()).catch(() => {});
  }

  const previous = lastPhase;
  lastPhase = phase.phase;
  if (previous === phase.phase) return;

  if (phase.announce && phase.announce !== lastAnnounced) {
    lastAnnounced = phase.announce;
    announce(phase.announce, { assertive: phase.phase === 'approval' });
  }
  if (phase.phase === 'approval' && 'vibrate' in navigator) navigator.vibrate([60, 40, 60]);

  if (!notify || !hidden || previous === null) return;
  if (!('Notification' in window) || Notification.permission !== 'granted') return;
  if (phase.phase === 'approval') show('Needs approval', `${sessionTitle}: ${phase.detail}`, 'eukhe-approval');
  else if (phase.phase === 'failed') show('Turn failed', `${sessionTitle}: ${phase.detail}`, 'eukhe-turn');
  else if (FINISHED.has(phase.phase) && previous !== 'connecting' && previous !== 'catchingUp' && previous !== 'opening') {
    show(phase.label, sessionTitle, 'eukhe-turn');
  }
}
