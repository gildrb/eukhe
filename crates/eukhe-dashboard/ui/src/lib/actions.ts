// Chat and session actions shared by the sidebar, the chat menu, the
// model menu, the composer and Settings. Each resolves with a short
// success sentence or rejects with an Error whose message shows inline.

import { fmt } from "./format.ts";
import { linkOpen, request, run, supports } from "./link.ts";
import { chatHref, navigate } from "./router.ts";
import { bind, createSession, refreshSessions } from "./session.ts";
import { store, type Prefs } from "./store.ts";
import { contentText, withoutSignalRules, type Pending } from "./turn.ts";
import type { AgentState, Model, ModelRef } from "./types.ts";

/** Re-read the bound session's AgentConnectionState (switch commands carry no event). */
export async function reloadState(): Promise<void> {
  const id = store.get().session?.id;
  const fresh = await run<AgentState | null>({ type: "get_connection_state" });
  store.set((state) =>
    state.session && state.session.id === id && fresh
      ? { session: { ...state.session, state: { ...state.session.state, ...fresh } } }
      : null,
  );
}

/** Run one switch command, then re-read the state so the UI shows the daemon's value. */
export async function setAndReload(command: {
  type: string;
  [field: string]: unknown;
}): Promise<void> {
  await run(command);
  await reloadState();
}

/**
 * Start a new chat in the current chat's folder and open it (`open` gets
 * its hash: the drawer replaces its own history entry with it). A failure
 * shows as the notice under the conversation.
 */
export async function newChat(open: (hash: string) => void = navigate): Promise<void> {
  try {
    const session = await createSession(store.get().session?.state.cwd ?? null);
    open(chatHref(session.id));
  } catch (error) {
    store.set({ notice: `No new chat. ${error instanceof Error ? error.message : String(error)}` });
  }
}

/** Rename chat `id` (through its live worker, else the catalog). */
export async function renameChat(id: string, name: string): Promise<string> {
  const trimmed = name.trim();
  if (!trimmed) throw new Error("A name cannot be empty.");
  await request("rename", { sessionId: id, name: trimmed });
  store.set((state) => ({
    sessions: {
      ...state.sessions,
      rows: state.sessions.rows.map((row) => (row.id === id ? { ...row, title: trimmed } : row)),
    },
    ...(state.session && state.session.id === id
      ? {
          session: {
            ...state.session,
            title: trimmed,
            state: { ...state.session.state, sessionName: trimmed },
          },
        }
      : {}),
  }));
  return "Renamed.";
}

/** Fork the whole chat (at its latest entry) into a new chat and open it. */
export async function forkChat(): Promise<string> {
  const tree = await run<{ leafId?: string } | null>({ type: "get_session_tree" });
  if (!tree?.leafId) throw new Error("There is nothing to fork yet.");
  const reply = await run<{ cancelled?: boolean } | null>({
    type: "fork",
    entryId: tree.leafId,
    position: "at",
  });
  if (reply?.cancelled) throw new Error("The fork was cancelled.");
  const stats = await run<{ sessionId?: string } | null>({ type: "get_session_stats" });
  await refreshSessions().catch(() => {});
  if (stats?.sessionId) {
    navigate(chatHref(stats.sessionId));
    await bind(stats.sessionId, true).catch(() => {});
  }
  return "Forked into a new chat.";
}

/** Download the bound chat as HTML or JSONL (the bridge's `export` op). */
export async function exportChat(format: "html" | "jsonl"): Promise<string> {
  if (!supports("export")) throw new Error("This eukhe build cannot export from the dashboard.");
  const file = await request<{ name: string; mimeType: string; data: string }>("export", {
    format,
  });
  const bytes = Uint8Array.from(atob(file.data), (char) => char.charCodeAt(0));
  const url = URL.createObjectURL(new Blob([bytes], { type: file.mimeType }));
  const link = document.createElement("a");
  link.href = url;
  link.download = file.name;
  document.body.append(link);
  link.click();
  link.remove();
  setTimeout(() => URL.revokeObjectURL(url), 10_000);
  return `Downloaded ${file.name}`;
}

/** Compact the bound chat's context (optional instructions). */
export async function compactChat(instructions = ""): Promise<string> {
  const text = instructions.trim();
  const result = await run<{ tokensBefore?: number } | null>(
    text ? { type: "compact", customInstructions: text } : { type: "compact" },
  );
  return typeof result?.tokensBefore === "number"
    ? `Compacted ${fmt.tokens(result.tokensBefore)} of context.`
    : "Compacted.";
}

/**
 * Delete chat `id` (the bridge stops its worker first and refuses a chat
 * open in another window). Deleting the current chat lands on the newest
 * remaining one, or a new chat.
 */
export async function deleteChat(id: string): Promise<void> {
  const current = store.get().session;
  const wasCurrent = current?.id === id;
  const cwd = current?.state.cwd ?? null;
  await request("delete", { sessionId: id });
  store.set((state) => ({
    sessions: { ...state.sessions, rows: state.sessions.rows.filter((row) => row.id !== id) },
    ...(wasCurrent ? { session: null, approvals: [] } : {}),
  }));
  const rows = await refreshSessions().catch(() => store.get().sessions.rows);
  if (!wasCurrent) return;
  const newest = rows.toSorted(
    (a, b) => (Date.parse(b.modified) || 0) - (Date.parse(a.modified) || 0),
  )[0];
  if (newest) {
    navigate(chatHref(newest.id), true);
    await bind(newest.id, true).catch(() => {});
  } else {
    navigate(chatHref((await createSession(cwd)).id), true);
  }
}

// --------------------------------------------------------------- models --

/** `provider/id` of a model. */
export function modelKey(model: ModelRef | Model | null | undefined): string {
  return model ? `${model.provider}/${model.id || ("modelId" in model ? model.modelId : "")}` : "";
}

/** The usable models (`get_available_models`) or, with `all`, the catalog. */
export async function listModels(all = false): Promise<Model[]> {
  const reply = await run<{ models?: Model[] } | null>({
    type: all ? "get_model_catalog" : "get_available_models",
  });
  return (reply?.models ?? []).toSorted((a, b) =>
    `${a.provider}/${a.name || a.id}`.localeCompare(`${b.provider}/${b.name || b.id}`),
  );
}

// Level and tier names are the daemon's strings, shown verbatim as the CLI
// shows them: `availableThinkingLevels` and `availableServiceTiers` of the
// connection state. The UI keeps no list of its own.

/** Switch the model. */
export function setModel(model: Model): Promise<void> {
  return setAndReload({ type: "set_model", provider: model.provider, modelId: model.id });
}

/** Switch the thinking level (one of `availableThinkingLevels`). */
export function setThinking(level: string): Promise<void> {
  return setAndReload({ type: "set_thinking_level", level });
}

/** Switch the service tier (one of `availableServiceTiers`); the daemon may keep its own. */
export async function setTier(serviceTier: string): Promise<void> {
  await setAndReload({ type: "set_service_tier", serviceTier });
  const kept = store.get().session?.state.serviceTier;
  if (kept && kept !== serviceTier) {
    throw new Error(`eukhe kept ${kept}: this model has no ${serviceTier} tier.`);
  }
}

// -------------------------------------------------------------- sending --

export function admissionId(): string {
  return crypto.randomUUID();
}

function setPending(sessionId: string, change: (pending: Pending[]) => Pending[]) {
  store.set((state) =>
    state.session && state.session.id === sessionId
      ? { session: { ...state.session, pending: change(state.session.pending) } }
      : null,
  );
}

/** Send one message optimistically; a failure keeps it as "Not sent". Held while offline. */
export async function send(item: Omit<Pending, "status" | "error">): Promise<void> {
  const state = store.get();
  const session = state.session;
  if (!session) return;
  const online = linkOpen() && state.link.status === "open";
  const entry: Pending = { ...item, status: online ? "sending" : "held", error: null };
  setPending(session.id, (pending) => [
    ...pending.filter((other) => other.admissionId !== item.admissionId),
    entry,
  ]);
  if (!online) return;
  try {
    const fields: Record<string, unknown> = {
      text: item.text,
      mode: item.mode,
      admissionId: item.admissionId,
    };
    if (item.images.length)
      fields.images = item.images.map(({ data, mimeType }) => ({ data, mimeType }));
    await request("prompt", fields);
    // A message sent while a turn runs is now in the daemon's queue (shown from it).
    if (item.queued) {
      setPending(session.id, (pending) =>
        pending.filter((other) => other.admissionId !== item.admissionId),
      );
    }
  } catch (error) {
    const reason = error instanceof Error ? error.message : String(error);
    setPending(session.id, (pending) =>
      pending.map((other) =>
        other.admissionId === item.admissionId
          ? { ...other, status: "failed", error: reason }
          : other,
      ),
    );
  }
}

/** Send the held messages once the link is back. */
export function flushHeld(): void {
  const session = store.get().session;
  if (!session || !linkOpen()) return;
  for (const item of session.pending) if (item.status === "held") void send(item);
}

/** Drop one pending message (before editing it). */
export function dropPending(item: Pending): void {
  const id = store.get().session?.id;
  if (id)
    setPending(id, (pending) => pending.filter((other) => other.admissionId !== item.admissionId));
}

/** Send the last user message again. */
export function retryLast(): void {
  const session = store.get().session;
  const last = session
    ? session.messages.findLast((message) => message.role === "user")
    : undefined;
  if (!session || !last) return;
  const running = session.turn.running;
  void send({
    admissionId: admissionId(),
    text: withoutSignalRules(contentText(last.content)),
    images: [],
    mode: "followUp",
    queued: running,
  });
}

/** Stop the running turn. */
export async function stop(): Promise<void> {
  await request("abort");
}

/** Take a queued message out of the daemon's queue; resolves its text. */
export async function unqueue(
  lane: "steering" | "followUp",
  index: number,
  text: string,
): Promise<string> {
  const reply = await run<{ status?: string } | null>({
    type: "mutate_queued_message",
    lane,
    index,
    expectedText: text,
    mutation: { type: "delete" },
  });
  if (reply?.status === "rejected") throw new Error("It was already sent.");
  return text;
}

// ---------------------------------------------------------------- prefs --

const systemDark = matchMedia("(prefers-color-scheme: dark)");

/** Apply the theme: `color-scheme` on the root drives every `light-dark()` color. */
export function applyTheme(theme: Prefs["theme"]): void {
  const root = document.documentElement;
  root.style.colorScheme = theme === "system" ? "light dark" : theme;
  const dark = theme === "dark" || (theme === "system" && systemDark.matches);
  for (const meta of document.querySelectorAll('meta[name="theme-color"]')) {
    meta.setAttribute("content", dark ? "#212121" : "#ffffff");
  }
  try {
    if (theme === "system") localStorage.removeItem("theme");
    else localStorage.setItem("theme", theme);
  } catch {
    // Private mode: the choice lasts for this tab.
  }
}
systemDark.addEventListener("change", () => applyTheme(store.get().prefs.theme));

export function notificationsSupported(): boolean {
  return window.isSecureContext && "Notification" in window;
}

/** Set one preference. Resolves false when it could not take effect (notifications refused). */
export async function setPref<K extends keyof Prefs>(key: K, value: Prefs[K]): Promise<boolean> {
  let effective: Prefs[K] = value;
  if (key === "notify" && value === true) {
    let granted = notificationsSupported();
    if (granted && Notification.permission !== "granted") {
      granted = (await Notification.requestPermission()) === "granted";
    }
    effective = granted as Prefs[K];
  }
  if (key === "theme") applyTheme(value as Prefs["theme"]);
  const prefs = { ...store.get().prefs, [key]: effective };
  store.set({ prefs });
  try {
    const { theme: _theme, ...rest } = prefs;
    localStorage.setItem("eukhe.prefs", JSON.stringify(rest));
  } catch {
    // Private mode.
  }
  return effective === value;
}
