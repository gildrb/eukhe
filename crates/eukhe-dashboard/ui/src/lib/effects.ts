// The command the dashboard runs itself instead of sending it to the
// agent: `/effects` (the irreversible effects that ran, then the steps a
// crash left unknown). The bridge words each reply (`text`): the text
// every surface shows. The answer becomes one note of the transcript.

import { run } from "./link.ts";
import { store } from "./store.ts";
import { withNote } from "./turn.ts";
import type { TextReply } from "./types.ts";

/** A command the dashboard runs itself. */
export type Command = { name: "effects" } | { name: "usage"; text: string };

/** The command `text` names, or null for a message to the agent. */
export function parseCommand(text: string): Command | null {
  const [head, ...args] = text.trim().split(/\s+/);
  switch (head) {
    case "/effects":
      return args.length ? { name: "usage", text: "Usage: /effects" } : { name: "effects" };
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
      case "usage":
        return show("error", command.text);
    }
  } catch (error) {
    show("error", (error as Error).message);
  }
}
