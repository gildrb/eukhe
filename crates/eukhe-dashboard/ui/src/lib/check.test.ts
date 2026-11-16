// The checks twin: each `check_update` of a running check sets its line
// (elapsed time running on from the report, the last output line); the
// ended report drops the line and leaves one note of how it ended.

import { describe, expect, test } from "vite-plus/test";
import { checkLine } from "./check.ts";
import { openSession, reduce } from "./turn.ts";
import type { CheckProgress, SessionEvent } from "./types.ts";

const NOW = 1_000_000;

const open = () =>
  openSession(
    {
      session: { id: "s", path: "/s" },
      state: null,
      summary: null,
      messages: null,
      cursor: null,
      replay: null,
    },
    null,
    NOW,
  );

/** A wire payload as eukhe-types serializes it. Whole minutes: a test text names no seconds. */
const running: CheckProgress = {
  child: "sub-1",
  place: "checkout",
  command: "./check.sh",
  elapsedMs: 715_400,
  phase: { kind: "running", lastLine: "waiting for a slot" },
};

const update = (check: CheckProgress, text: string): SessionEvent => ({
  type: "check_update",
  check,
  text,
});

describe("check_update", () => {
  test("a running check shows its line, the elapsed time running on", () => {
    const session = reduce(open(), update(running, "check running"), NOW);
    // 715.4 s at the report, 65 s since: 13 minutes.
    expect(Object.values(session.checks).map((check) => checkLine(check, NOW + 65_000))).toEqual([
      "check running 13m 0s: ./check.sh (sub-1's checkout); last line: waiting for a slot",
    ]);
  });

  test("an ended check drops its line and leaves one note of how it ended", () => {
    const text =
      "check failed (exit 1) in 30m 0s: ./check.sh (sub-1's checkout); last lines: FMT FAILED | CHECK EXIT 1";
    const ended: CheckProgress = {
      ...running,
      elapsedMs: 1_800_000,
      phase: {
        kind: "ended",
        outcome: { kind: "failed", code: 1 },
        lastLines: ["FMT FAILED", "CHECK EXIT 1"],
      },
    };
    const session = reduce(
      reduce(open(), update(running, "check running"), NOW),
      update(ended, text),
      NOW + 1,
    );
    expect([session.checks, session.notes.map((note) => [note.kind, note.text])]).toEqual([
      {},
      [["error", text]],
    ]);
  });
});
