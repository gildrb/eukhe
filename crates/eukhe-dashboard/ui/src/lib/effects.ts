// The commands the dashboard runs itself instead of sending them to the
// agent: `/effects` (the irreversible effects that ran, then the steps a
// crash left unknown), `/undo` and `/diff [all]` (the per-prompt workspace
// snapshots). The bridge words each reply (`text`): the text every surface
// shows. Each answer becomes one note of the transcript.

import { run } from "./link.ts";
import { store } from "./store.ts";
import { withNote } from "./turn.ts";
import type { TextReply } from "./types.ts";

/** A command the dashboard runs itself. */
export type Command =
  | { name: "effects" }
  | { name: "undo" }
  | { name: "diff"; all: boolean }
  | { name: "usage"; text: string };

/** The command `text` names, or null for a message to the agent. The word after `/diff` is read in any case. */
export function parseCommand(text: string): Command | null {
  const [head, ...args] = text.trim().split(/\s+/);
  switch (head) {
    case "/effects":
      return args.length ? { name: "usage", text: "Usage: /effects" } : { name: "effects" };
    case "/undo":
      return args.length ? { name: "usage", text: "Usage: /undo" } : { name: "undo" };
    case "/diff": {
      if (!args.length) return { name: "diff", all: false };
      if (args.length === 1 && args[0]?.toLowerCase() === "all") return { name: "diff", all: true };
      return { name: "usage", text: "Usage: /diff [all]" };
    }
    default:
      return null;
  }
}

/** Add one note to the bound session's transcript. */
function show(kind: "output" | "error", text: string): void {
  store.set((state) =>
    state.session ? { session: withNote(state.session, kind, text, Date.now()) } : null,
  );
}

/** The answer to `/effects`: the ledger, then each step a crash left unknown. */
async function effectsText(): Promise<string> {
  const [ran, unknown] = await Promise.all([
    run<TextReply>({ type: "get_ran_effects" }),
    run<TextReply>({ type: "get_unknown_effects" }),
  ]);
  return [ran.text, unknown.text].filter(Boolean).join("\n");
}

/** Run one command; its answer, or why it failed, becomes a note. */
export async function runCommand(command: Command): Promise<void> {
  try {
    switch (command.name) {
      case "effects":
        return show("output", await effectsText());
      case "undo":
        return show("output", (await run<TextReply>({ type: "undo_turn" })).text);
      case "diff": {
        const scope = command.all ? "all" : "turn";
        return show("output", (await run<TextReply>({ type: "get_turn_diff", scope })).text);
      }
      case "usage":
        return show("error", command.text);
    }
  } catch (error) {
    show("error", (error as Error).message);
  }
}
