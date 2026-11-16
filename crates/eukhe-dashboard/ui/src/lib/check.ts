// PURE check view: the line the conversation shows for each running
// hand-back check of the session's children (eukhe-types `CheckProgress`,
// the payload of `check_update`). The line follows the TUI's status line
// (`CheckProgress::text`): `check running 12m 30s: <command> (<child>'s
// checkout); last line: <line>`. The elapsed time runs on from the last
// report: callers pass the report's arrival time and `now`.

import type { CheckProgress } from "./types.ts";

/** A running check: its last report and when it arrived. */
export type RunningCheck = { check: CheckProgress; at: number };

/** The key of a check: its child and place (one check runs per pair). */
export function checkKey(check: CheckProgress): string {
  return `${check.child}:${check.place}`;
}

/** `1h 2m 3s`, `12m 30s`, `45s` (eukhe-types `elapsed_text`). */
export function elapsedText(ms: number): string {
  const total = Math.floor(Math.max(0, ms) / 1000);
  const hours = Math.floor(total / 3600);
  const minutes = Math.floor((total % 3600) / 60);
  const seconds = total % 60;
  if (hours > 0) return `${hours}h ${minutes}m ${seconds}s`;
  if (minutes > 0) return `${minutes}m ${seconds}s`;
  return `${seconds}s`;
}

/** The line of a running check at `now`. */
export function checkLine({ check, at }: RunningCheck, now: number): string {
  const place =
    check.place === "checkout" ? `${check.child}'s checkout` : `after ${check.child}'s integration`;
  const elapsed = elapsedText(check.elapsedMs + Math.max(0, now - at));
  const head = `check running ${elapsed}: ${check.command} (${place})`;
  const last = check.phase.kind === "running" ? check.phase.lastLine : null;
  return last ? `${head}; last line: ${last}` : head;
}
