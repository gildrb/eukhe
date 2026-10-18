// Hash routes: `#/c/<sessionId>` is a chat; `#/c/<id>/settings[/<section>]`
// overlays Settings on it; `#/settings[/<section>]` overlays Settings on
// the newest chat; `#/` opens the newest chat.

import { useEffect, useState } from "react";

/** `settings`: null (closed), "" (the section list) or a section id. */
export type Route = { sessionId: string | null; settings: string | null };

export function currentRoute(): Route {
  const parts = location.hash
    .replace(/^#\/?/, "")
    .split("/")
    .filter(Boolean)
    .map(decodeURIComponent);
  let sessionId: string | null = null;
  let rest = parts;
  if (parts[0] === "c" && parts[1]) {
    sessionId = parts[1];
    rest = parts.slice(2);
  }
  const settings = rest[0] === "settings" ? (rest[1] ?? "") : null;
  return { sessionId, settings };
}

/** The hash for a chat (and optionally a Settings section over it). */
export function chatHref(sessionId: string | null, settings: string | null = null): string {
  let hash = sessionId ? `#/c/${encodeURIComponent(sessionId)}` : "#/";
  if (settings !== null) {
    hash = `${sessionId ? hash : "#"}/settings${settings ? `/${encodeURIComponent(settings)}` : ""}`;
  }
  return hash;
}

/** Go to `hash`; `replace` keeps the history length. */
export function navigate(hash: string, replace = false): void {
  if (location.hash === hash) return;
  if (replace) location.replace(hash);
  else location.hash = hash.replace(/^#/, "");
}

export function useRoute(): Route {
  const [route, setRoute] = useState(currentRoute);
  useEffect(() => {
    const sync = () => setRoute(currentRoute());
    window.addEventListener("hashchange", sync);
    return () => window.removeEventListener("hashchange", sync);
  }, []);
  return route;
}
