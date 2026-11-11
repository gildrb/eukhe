// The `/loop` twin: the open reply seeds `state.loop`, every `loop_update`
// replaces it, a loop that ends leaves one note of why, and the loop line
// shows the phase, the iteration, what is left, the condition and the last
// check with its iteration (the TUI's label, eukhe-tui `loop_surface.rs`).

import { describe, expect, test } from "vite-plus/test";
import { loopCountsDown, loopLine, timeLeft } from "./loop.ts";
import { openSession, reduce, type Session } from "./turn.ts";
import type { AgentState, LoopStatus } from "./types.ts";

const NOW = 1_000_000;

function open(state: AgentState): Session {
  return openSession(
    {
      session: { id: "s1", path: "/tmp/s1.jsonl" },
      state,
      summary: null,
      messages: [],
      cursor: null,
      replay: null,
    },
    null,
    NOW,
  );
}

/** A wire payload as eukhe-types serializes it (`loop_update_roundtrips`). */
const judging: LoopStatus = JSON.parse(
  '{"phase":{"state":"judging"},"iteration":2,"remaining":8,"deadlineMs":90000,"condition":{"command":"test -f done","until":true},"prompt":"fix it","failures":1,"lastCheck":{"iteration":1,"evidence":{"kind":"exited","code":1}},"limit":{"kind":"iterations","iterations":10},"startedAtMs":5,"verdict":1,"message":"Loop mode enabled."}',
) as LoopStatus;

function status(phase: LoopStatus["phase"], extra: Partial<LoopStatus> = {}): LoopStatus {
  return { phase, iteration: 3, prompt: "fix it", failures: 0, ...extra };
}

describe("the session's loop", () => {
  test("the open reply seeds it from state.loop, and an old daemon's state has none", () => {
    expect(open({ loop: judging }).loop).toEqual(judging);
    expect(open({}).loop).toBeNull();
  });

  test("loop_update replaces it", () => {
    const session = reduce(open({}), { type: "loop_update", loop: judging }, NOW);
    expect(session.loop).toEqual(judging);
    expect(session.notes).toEqual([]);
    const off = status({ state: "off" }, { iteration: 0 });
    expect(reduce(session, { type: "loop_update", loop: off }, NOW).loop).toEqual(off);
  });

  test("a loop that ends leaves one note of why; a replayed end leaves none", () => {
    const running = reduce(open({}), { type: "loop_update", loop: judging }, NOW);
    const satisfied = status(
      { state: "ended", end: "satisfied" },
      { condition: { command: "test -f done", until: true } },
    );
    const ended = reduce(running, { type: "loop_update", loop: satisfied }, NOW);
    expect(ended.notes.map(({ kind, text }) => ({ kind, text }))).toEqual([
      { kind: "note", text: "Loop ended after iteration 3: its condition holds." },
    ]);
    expect(reduce(ended, { type: "loop_update", loop: satisfied }, NOW).notes).toHaveLength(1);
    const seeded = open({ loop: satisfied });
    expect(reduce(seeded, { type: "loop_update", loop: satisfied }, NOW).notes).toEqual([]);
  });

  test("each end reads its reason; a broken check or failing turns read as errors", () => {
    const running = reduce(open({}), { type: "loop_update", loop: judging }, NOW);
    const endNote = (loop: LoopStatus) => {
      const [only] = reduce(running, { type: "loop_update", loop }, NOW).notes;
      return only && { kind: only.kind, text: only.text };
    };
    const whileCondition = { command: "pgrep server", until: false };
    expect([
      endNote(status({ state: "ended", end: "satisfied" }, { condition: whileCondition })),
      endNote(
        status(
          { state: "ended", end: "check_broke" },
          { lastCheck: { iteration: 3, evidence: { kind: "exited", code: 3 } } },
        ),
      ),
      endNote(status({ state: "ended", end: "out_of_turns" })),
      endNote(status({ state: "ended", end: "out_of_time" })),
      endNote(status({ state: "ended", end: "turns_failed" })),
      endNote(status({ state: "ended", end: "out_of_budget" })),
      endNote(status({ state: "ended", end: "stopped" }, { iteration: 0 })),
    ]).toEqual([
      { kind: "note", text: "Loop ended after iteration 3: its condition no longer holds." },
      { kind: "error", text: "Loop ended after iteration 3: the condition check broke (exit 3)." },
      { kind: "note", text: "Loop ended after iteration 3: its iterations are used up." },
      { kind: "note", text: "Loop ended after iteration 3: its time is up." },
      { kind: "error", text: "Loop ended after iteration 3: 3 turns failed in a row." },
      { kind: "note", text: "Loop ended after iteration 3: the budget funds no further turn." },
      { kind: "note", text: "Loop ended: you stopped it." },
    ]);
  });
});

describe("the loop line", () => {
  test("no loop, or one that ended, shows no line", () => {
    expect(loopLine(null, NOW)).toBeNull();
    expect(loopLine(status({ state: "off" }), NOW)).toBeNull();
    expect(loopLine(status({ state: "ended", end: "satisfied" }), NOW)).toBeNull();
  });

  test("each phase leads the line; a paused loop is marked", () => {
    expect(
      (["armed", "turn", "judging", "paused"] as const).map((state) =>
        loopLine(status({ state }), NOW),
      ),
    ).toEqual([
      { lead: "Loop: your next prompt repeats", parts: ["iteration 3"], paused: false },
      { lead: "Loop running", parts: ["iteration 3"], paused: false },
      { lead: "Loop checking", parts: ["iteration 3"], paused: false },
      { lead: "Loop paused", parts: ["iteration 3"], paused: true },
    ]);
  });

  test("everything at once: iteration, count left, condition, last check with its verdict", () => {
    expect(loopLine(judging, NOW)).toEqual({
      lead: "Loop checking",
      parts: [
        "iteration 2",
        "8 of 10 left",
        "until test -f done",
        "last check after iteration 1: exit 1, not met yet",
      ],
      paused: false,
    });
  });

  test("a duration shows the time left; a multi-line condition reads on one line", () => {
    const timed = status(
      { state: "turn" },
      {
        iteration: 0,
        deadlineMs: NOW + 330_000,
        limit: { kind: "duration", durationMs: 600_000 },
        condition: { command: "pgrep  -f\n\tserver", until: false },
        lastCheck: { iteration: 4, evidence: { kind: "timed_out" } },
      },
    );
    expect(loopLine(timed, NOW)).toEqual({
      lead: "Loop running",
      parts: ["5m30s left", "while pgrep -f server", "last check after iteration 4: timed out"],
      paused: false,
    });
    expect(loopCountsDown(timed)).toBe(true);
    expect(loopCountsDown(judging)).toBe(false);
    expect(
      loopCountsDown(status({ state: "ended", end: "out_of_time" }, { deadlineMs: NOW })),
    ).toBe(false);
  });

  test("the time left keeps the two largest units and counts a started second whole", () => {
    expect([7_500_000, 7_200_000, 330_000, 300_000, 101_001, -5_000].map(timeLeft)).toEqual([
      "2h5m left",
      "2h left",
      "5m30s left",
      "5m left",
      "1m42s left",
      "0s left",
    ]);
  });
});
