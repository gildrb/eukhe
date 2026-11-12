// PURE `/loop` view: the words the conversation's loop line and the loop's
// end note show for a LoopStatus (eukhe-types `loop_mode`, the payload of
// `loop_update` and of the open reply's `state.loop`). The line follows the
// TUI's status-line label (eukhe-tui `loop_surface.rs`): the phase, the
// iteration, what is left of the count or the time, the condition, and the
// last check with the iteration it was read after. No clock reads: callers
// pass `now`.

import type { LoopEnd, LoopEvidence, LoopPhase, LoopStatus } from "./types.ts";

/** The loop line: shown while a loop is on (armed, in a turn, judging or paused). */
export type LoopLine = { lead: string; parts: string[]; paused: boolean };

/** Whether a loop is on: armed, in a turn, judging or paused. */
export function loopIsOn(phase: LoopPhase | undefined): boolean {
  return (
    phase?.state === "armed" ||
    phase?.state === "turn" ||
    phase?.state === "judging" ||
    phase?.state === "paused"
  );
}

/** Whether the loop's line counts down a deadline (the page ticks for it). */
export function loopCountsDown(status: LoopStatus | null): boolean {
  return (
    status !== null &&
    loopIsOn(status.phase) &&
    status.limit?.kind === "duration" &&
    status.deadlineMs !== undefined
  );
}

const LEADS: Record<string, string> = {
  armed: "Loop: your next prompt repeats",
  turn: "Loop running",
  judging: "Loop checking",
  paused: "Loop paused",
};

/** `2h5m left`, `5m30s left`, `42s left`: the two largest units, a started second counted whole. */
export function timeLeft(leftMs: number): string {
  const total = Math.ceil(Math.max(0, leftMs) / 1000);
  const hours = Math.floor(total / 3600);
  const minutes = Math.floor((total % 3600) / 60);
  const seconds = total % 60;
  if (hours > 0) return minutes > 0 ? `${hours}h${minutes}m left` : `${hours}h left`;
  if (minutes > 0) return seconds > 0 ? `${minutes}m${seconds}s left` : `${minutes}m left`;
  return `${seconds}s left`;
}

/** What one run of the condition command showed (`exit 1`, `timed out`). */
export function evidenceText(evidence: LoopEvidence): string {
  switch (evidence.kind) {
    case "exited":
      return `exit ${evidence.code}`;
    case "no_status":
      return "no exit status";
    case "timed_out":
      return "timed out";
    case "spawn_failed":
      return "could not run";
    case "cancelled":
      return "cancelled";
    default:
      return "unknown";
  }
}

/** The verdict of the last check on the stop condition (0 confirmed … 3 unjudged). */
const VERDICTS = ["condition met", "not met yet", "check broken", "no answer"];

/** The condition on one line: `until test -f done`, `while pgrep server`. */
function conditionText(status: LoopStatus): string | null {
  const condition = status.condition;
  if (!condition) return null;
  const command = condition.command
    .split(/[\s\p{Cc}]+/u)
    .filter(Boolean)
    .join(" ");
  return `${condition.until ? "until" : "while"} ${command}`;
}

/** What is left of the bound given at `/loop`: `7 of 10 left`, `5m30s left`. */
function limitText(status: LoopStatus, now: number): string | null {
  const limit = status.limit;
  if (!limit) return null;
  if (limit.kind === "iterations") {
    return status.remaining === undefined
      ? null
      : `${status.remaining} of ${limit.iterations} left`;
  }
  return status.deadlineMs === undefined ? null : timeLeft(status.deadlineMs - now);
}

/** The loop line at `now`, or null when no loop is on. */
export function loopLine(status: LoopStatus | null, now: number): LoopLine | null {
  if (!status || !loopIsOn(status.phase)) return null;
  const parts: string[] = [];
  if (status.iteration > 0) parts.push(`iteration ${status.iteration}`);
  const limit = limitText(status, now);
  if (limit) parts.push(limit);
  const condition = conditionText(status);
  if (condition) parts.push(condition);
  const check = status.lastCheck;
  if (check) {
    const verdict = status.verdict === undefined ? undefined : VERDICTS[status.verdict];
    parts.push(
      `last check after iteration ${check.iteration}: ${evidenceText(check.evidence)}${verdict ? `, ${verdict}` : ""}`,
    );
  }
  return {
    lead: LEADS[status.phase.state] ?? "Loop",
    parts,
    paused: status.phase.state === "paused",
  };
}

/** Why a loop ended, as the end of a sentence. */
export function endReason(end: LoopEnd, status: LoopStatus): string {
  switch (end) {
    case "satisfied":
      return status.condition && !status.condition.until
        ? "its condition no longer holds"
        : "its condition holds";
    case "check_broke": {
      const check = status.lastCheck;
      return check
        ? `the condition check broke (${evidenceText(check.evidence)})`
        : "the condition check broke";
    }
    case "out_of_turns":
      return "its iterations are used up";
    case "out_of_time":
      return "its time is up";
    case "turns_failed":
      return "3 turns failed in a row";
    case "out_of_budget":
      return "the budget funds no further turn";
    case "stopped":
      return "you stopped it";
    default:
      return end;
  }
}

/** The end note of a loop that just ended, or null when the status is no end. */
export function loopEndNote(status: LoopStatus): { kind: string; text: string } | null {
  if (status.phase.state !== "ended") return null;
  const { end } = status.phase;
  const after = status.iteration > 0 ? ` after iteration ${status.iteration}` : "";
  return {
    kind: end === "check_broke" || end === "turns_failed" ? "error" : "note",
    text: `Loop ended${after}: ${endReason(end, status)}.`,
  };
}
