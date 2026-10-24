// Boot: the theme, the link (frames folded into the session), the route
// (which chat is bound), the 4 Hz tick while a turn runs, the document
// title and the notifications, then the app.

import "./global.css";
import { render } from "preact";
import { App } from "./components/App.tsx";
import { applyTheme, reloadState } from "./lib/actions.ts";
import { fmt } from "./lib/format.ts";
import { connect, onFrame, onReady } from "./lib/link.ts";
import { chatHref, currentRoute, navigate } from "./lib/router.ts";
import { addApproval, approvalSettled, bind, opening, refreshSessions } from "./lib/session.ts";
import { store } from "./lib/store.ts";
import { derivePhase, reduce, type PhaseName } from "./lib/turn.ts";

const TICK_MS = 250;

applyTheme(store.get().prefs.theme);

// --------------------------------------------------------------- frames --
onFrame("event", (frame) => {
  const state = store.get();
  if (opening() || !state.session) return;
  const session = reduce(state.session, frame.event, Date.now());
  store.set({ session: frame.cursor ? { ...session, cursor: frame.cursor } : session });
  switch (frame.event.type) {
    case "agent_end":
      // Context usage and message counts carry no event: re-read them when a turn ends.
      void reloadState().catch(() => {});
      void refreshSessions().catch(() => {});
      break;
    case "turn_end":
      void reloadState().catch(() => {});
      break;
    case "session_info_changed":
      void refreshSessions().catch(() => {});
      break;
    default:
      break;
  }
});
onFrame("approval", (frame) => addApproval(frame.request));
onFrame("approval_settled", (frame) => approvalSettled(frame.requestId));
onFrame("resync", () => {
  void bind(currentRoute().sessionId ?? store.get().session?.id ?? null, true).catch(() => {});
});
onReady(() => {
  const route = currentRoute();
  void refreshSessions().catch(() => {});
  bind(route.sessionId, true).then(
    (session) => {
      if (!route.sessionId) navigate(chatHref(session.id, route.settings), true);
    },
    () => {},
  );
});

// ---------------------------------------------------------------- route --
window.addEventListener("hashchange", () => {
  const route = currentRoute();
  if (store.get().link.status !== "open") return;
  if (route.sessionId) void bind(route.sessionId).catch(() => {});
  else {
    bind(null).then(
      (session) => navigate(chatHref(session.id, route.settings), true),
      () => {},
    );
  }
});

// ---------------------------------------------------- title and notices --
let lastPhase: PhaseName | null = null;
let lastTitle = "";
let lastBadge = -1;

function notify(title: string, body: string) {
  try {
    const shown = new Notification(title, { body, tag: "eukhe", icon: "icons/icon-192.png" });
    shown.addEventListener("click", () => {
      window.focus();
      shown.close();
    });
  } catch {
    // Some platforms only allow notifications from a service worker.
  }
}

function attend() {
  const state = store.get();
  const phase = derivePhase(state, Date.now(), fmt);
  const status = phase.phase === "failed" ? "Failed" : phase.running ? phase.label : "";
  const title = [status, state.session?.title, "eukhe"].filter(Boolean).join(" – ");
  if (title !== lastTitle) {
    document.title = title;
    lastTitle = title;
  }
  const needsYou = phase.phase === "approval" || phase.phase === "failed" ? 1 : 0;
  if (needsYou !== lastBadge && "setAppBadge" in navigator) {
    lastBadge = needsYou;
    void (needsYou ? navigator.setAppBadge(needsYou) : navigator.clearAppBadge()).catch(() => {});
  }
  const previous = lastPhase;
  lastPhase = phase.phase;
  if (previous === phase.phase || previous === null || previous === "none") return;
  if (!state.prefs.notify || !document.hidden) return;
  if (!("Notification" in window) || Notification.permission !== "granted") return;
  const body = state.session?.title ?? "";
  if (phase.phase === "approval") notify("eukhe needs your approval", body);
  else if (phase.phase === "failed") notify("eukhe failed", body);
  else if (phase.phase === "idle" && previous !== "sending") notify("eukhe is done", body);
}
store.subscribe(attend);

setInterval(() => {
  if (document.hidden) return;
  if (derivePhase(store.get(), Date.now(), fmt).running) store.set({ tick: Date.now() });
}, TICK_MS);

// ----------------------------------------------------------------- boot --
// Earlier builds registered a cache-first service worker; drop it.
if ("serviceWorker" in navigator) {
  navigator.serviceWorker.getRegistrations().then(
    (registrations) => {
      for (const registration of registrations) void registration.unregister();
    },
    () => {},
  );
}

const root = document.getElementById("app");
if (root) render(<App />, root);
connect();
