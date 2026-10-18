// Attention while away: the document title (mirrors the activity line),
// the app badge, aria-live announcements, and (opt-in, hidden tab only) a
// Notification when a turn finishes, fails or needs approval. Everything
// renders from derivePhase.

import { announce } from './ui.js';

let lastPhase = null;
let lastAnnounced = '';
let lastBadge = -1;
let lastTitle = '';

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

/** Called on every state change with the bound session's phase and title. */
export function attend({ phase, sessionTitle, notify, hidden }) {
  const status = phase.phase === 'failed' ? 'Failed' : phase.running ? phase.label : '';
  const title = [status, sessionTitle, 'eukhe'].filter(Boolean).join(' – ');
  if (title !== lastTitle) {
    document.title = title;
    lastTitle = title;
  }

  const needsYou = phase.phase === 'approval' || phase.phase === 'failed' ? 1 : 0;
  if (needsYou !== lastBadge && 'setAppBadge' in navigator) {
    lastBadge = needsYou;
    (needsYou ? navigator.setAppBadge(needsYou) : navigator.clearAppBadge()).catch(() => {});
  }

  const previous = lastPhase;
  lastPhase = phase.phase;
  if (previous === phase.phase) return;

  if (phase.announce && phase.announce !== lastAnnounced) {
    lastAnnounced = phase.announce;
    announce(phase.announce, { assertive: phase.urgent });
  }

  if (!notify || !hidden || previous === null || previous === 'none') return;
  if (!('Notification' in window) || Notification.permission !== 'granted') return;
  if (phase.phase === 'approval') show('eukhe needs your approval', sessionTitle, 'eukhe-approval');
  else if (phase.phase === 'failed') show('eukhe failed', sessionTitle, 'eukhe-turn');
  else if (phase.phase === 'idle' && previous !== 'sending') show('eukhe is done', sessionTitle, 'eukhe-turn');
}
