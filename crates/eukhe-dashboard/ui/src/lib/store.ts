// The tab's one state object. `store.set` merges a patch into the top
// level; subscribers hear about it once per animation frame. Components
// read it with `useStore(select)`.

import { useSyncExternalStore } from "react";
import type { Approval, Session } from "./turn.ts";
import type { SessionRow } from "./types.ts";

export type Theme = "system" | "light" | "dark";
export type Lane = "steer" | "followUp";

export type Prefs = { theme: Theme; enterSendsOnTouch: boolean; notify: boolean; lane: Lane };

export type LinkStatus = "connecting" | "open" | "offline" | "unavailable";

export type Frame = {
  seq: number;
  at: number;
  dir: "in" | "out";
  type: string;
  data: Record<string, unknown>;
};

export type State = {
  link: {
    status: LinkStatus;
    everOpen: boolean;
    catchingUp: boolean;
    retryAt: number;
    error: string | null;
    hello: { protocol: number; build: string; ops: string[] } | null;
  };
  sessions: { rows: SessionRow[]; loaded: boolean; loading: boolean; error: string | null };
  session: Session | null;
  approvals: Approval[];
  /** While (or after failing) binding a session. */
  opening: { id: string | null; error: string | null } | null;
  prefs: Prefs;
  /** A ring of the last frames (≤ 2000), mutated in place; `framesSeq` moves on each one. */
  frames: Frame[];
  framesSeq: number;
  /** Moves at 4 Hz while a turn runs (elapsed counters). */
  tick: number;
  /** One dismissible line under the conversation: an action that failed out of sight. */
  notice: string | null;
};

export const PREFS_KEY = "eukhe.prefs";

function storedPrefs(): Prefs {
  const defaults: Prefs = {
    theme: "system",
    enterSendsOnTouch: false,
    notify: false,
    lane: "steer",
  };
  try {
    const saved: Partial<Prefs> = JSON.parse(localStorage.getItem(PREFS_KEY) ?? "{}");
    const theme = localStorage.getItem("theme");
    return {
      ...defaults,
      ...saved,
      theme: theme === "dark" || theme === "light" ? theme : "system",
    };
  } catch {
    return defaults;
  }
}

let state: State = {
  link: {
    status: "connecting",
    everOpen: false,
    catchingUp: false,
    retryAt: 0,
    error: null,
    hello: null,
  },
  sessions: { rows: [], loaded: false, loading: false, error: null },
  session: null,
  approvals: [],
  opening: null,
  prefs: storedPrefs(),
  frames: [],
  framesSeq: 0,
  tick: 0,
  notice: null,
};

const listeners = new Set<() => void>();
let scheduled = false;

function flush() {
  scheduled = false;
  for (const listener of listeners) listener();
}

export const store = {
  get(): State {
    return state;
  },
  set(patch: Partial<State> | ((current: State) => Partial<State> | null)): void {
    const next = typeof patch === "function" ? patch(state) : patch;
    if (!next) return;
    state = { ...state, ...next };
    if (scheduled) return;
    scheduled = true;
    // A hidden tab gets no animation frames; status still has to move.
    if (document.hidden) queueMicrotask(flush);
    else requestAnimationFrame(flush);
  },
  subscribe(listener: () => void): () => void {
    listeners.add(listener);
    return () => listeners.delete(listener);
  },
};

/** The part of the state that `select` picks; re-renders when it changes (by identity). */
export function useStore<T>(select: (current: State) => T): T {
  return useSyncExternalStore(
    (listener) => store.subscribe(listener),
    () => select(state),
  );
}
