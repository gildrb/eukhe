# eukhe: the laws of area loop, section model: each decision of `/loop`
# (bend/loop.bend), one event at a time, stated with the helpers of
# spec/loop/loop.bend. Section history (laws/loop/history.bend) states
# what holds over whole histories of events; section entry
# (laws/loop/entry.bend) the entry of the compiled core.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S

# Requirements (spec/README.md L1-L9)
# -----------------------------------
#   L1 `/loop` starts a loop with its bound and condition: with an inline
#      prompt the first turn runs at once, unjudged; without one the loop
#      waits for the prompt. `/loop` while a loop is on ends it;
#      `/loop --stop` ends it and never starts one.
#                     loop_enter_first_turn, loop_enter_arms,
#                     loop_enter_sets_bounds, loop_enter_starts_fresh,
#                     loop_enter_ends_running,
#                     loop_stop_ends, loop_stop_never_starts
#   L2 every automatic iteration sends the loop's prompt, byte for byte;
#      a prompt the user sends while the loop is on becomes the prompt
#      from then on and spends nothing of the count.
#                     loop_resends_body, loop_prompt_adopted,
#                     loop_unattended_resends_same
#   L3 a loop with a condition judges after every settled turn, on the
#      exit status of its command only (the verdict table); it ends satisfied
#      only on fresh evidence that shows the stop condition, and starts an
#      automatic iteration only on fresh evidence that shows it does not
#      hold yet.
#                     loop_verdict_table, loop_settled_turn_is_judged,
#                     loop_satisfied_needs_confirmation,
#                     loop_auto_needs_refutation, loop_confirmed_ends,
#                     loop_broken_check_ends, loop_cancelled_check_waits
#   L4 an automatic iteration starts only inside every bound: the count,
#      the deadline, fewer than three failed turns in a row, a funded
#      budget; each bound ends the loop with its own reason (when several
#      hold at once: the failed turns, then the budget, then the count,
#      then the time); inside every bound the loop goes on.
#                     loop_count_bounds, loop_deadline_bounds,
#                     loop_failing_run_ends, loop_good_turn_forgives,
#                     loop_failed_turn_counts, loop_failed_turn_goes_on,
#                     loop_unfunded_never_starts, loop_tired_gives_up,
#                     loop_unfunded_stops, loop_spent_stops,
#                     loop_late_stops, loop_inside_continues,
#                     loop_enter_sets_bounds, loop_keeps_deadline,
#                     loop_count_conserved, loop_uncounted_stays,
#                     loop_prompt_clears_failures
#   L5 after the user's interrupt no turn and no check starts until the
#      user acts again; a turn that did not run to its end pauses the loop.
#                     loop_abort_holds, loop_halted_turn_pauses,
#                     loop_abort_pauses
#   L6 a loop ends once: it reports its end once, and after the end (or
#      with no loop) nothing changes and nothing starts until a new `/loop`.
#                     loop_off_stays_off, loop_reports_once,
#                     loop_report_names_the_end
#   L7 a restart resumes the same loop at the same iteration: it changes
#      nothing and takes up the work that was pending (the turn in flight,
#      never sent twice; the check); an event delivered twice is a no-op
#      the second time; no event but a new `/loop` changes the condition.
#                     loop_restart_changes_nothing,
#                     loop_restart_resumes_submit,
#                     loop_restart_resumes_adopted, loop_restart_rejudges,
#                     loop_restart_idle_rests, loop_redelivery_is_noop,
#                     loop_keeps_condition, loop_keeps_deadline
#   L8 while user input is queued or work is unsettled the loop waits: it
#      starts nothing, judges nothing and changes nothing, and asks again.
#                     loop_blocked_waits, loop_blocked_defers
#   L9 the loop keeps the last evidence it read and the iteration it was
#      read after (why it is still running), and only a check or a new
#      `/loop` changes it.
#                     loop_records_evidence, loop_evidence_only_from_checks,
#                     loop_report_names_the_end
#
# Every law is about Lp.step or Lp.judge, the two defs the entry
# (bend/ffi_loop.bend) calls. Inputs are free unless a premise says
# otherwise; each premise is the condition its requirement states.

# Laws: the verdict (L3)
# ----------------------

# LAW loop_verdict_table (L3): the verdict of each piece of evidence, for
# `--until` (True) and `--while` (False): exit 1 is the only "condition is
# false" status, so any exit status of 2 or more (k free) is a broken check.
# EXCLUDES: exit 1 read as a broken check, a status above 1 or a timeout
#   read as "false" (a typo'd condition ending the loop like finished
#   work, or running it forever), stdout consulted, the polarity swapped
law loop_verdict_table:
  for k: Nat
  {Lp.judge(True{}, Lp.Exited{0n}) == Lp.Confirmed{} : Lp.Verdict} &      # exit 0, --until: halt, "is now satisfied"
  {Lp.judge(True{}, Lp.Exited{1n}) == Lp.Refuted{} : Lp.Verdict} &        # exit 1, --until: continue
  {Lp.judge(False{}, Lp.Exited{0n}) == Lp.Refuted{} : Lp.Verdict} &       # exit 0, --while: continue
  {Lp.judge(False{}, Lp.Exited{1n}) == Lp.Confirmed{} : Lp.Verdict} &     # exit 1, --while: halt, "no longer holds"
  {Lp.judge(True{}, Lp.Exited{2n+k}) == Lp.Broken{} : Lp.Verdict} &       # exit > 1: error, "failed (exit N)"
  {Lp.judge(False{}, Lp.Exited{2n+k}) == Lp.Broken{} : Lp.Verdict} &      # either polarity
  {Lp.judge(True{}, Lp.NoStatus{}) == Lp.Broken{} : Lp.Verdict} &         # "no exit status": error
  {Lp.judge(False{}, Lp.NoStatus{}) == Lp.Broken{} : Lp.Verdict} &        # either polarity
  {Lp.judge(True{}, Lp.TimedOut{}) == Lp.Broken{} : Lp.Verdict} &         # timed out: error, before the abort check
  {Lp.judge(False{}, Lp.TimedOut{}) == Lp.Broken{} : Lp.Verdict} &        # either polarity
  {Lp.judge(True{}, Lp.SpawnFailed{}) == Lp.Broken{} : Lp.Verdict} &      # "could not run": error
  {Lp.judge(False{}, Lp.SpawnFailed{}) == Lp.Broken{} : Lp.Verdict} &     # either polarity
  {Lp.judge(True{}, Lp.Cancelled{}) == Lp.Unjudged{} : Lp.Verdict} &      # cancelled: aborted, no verdict
  {Lp.judge(False{}, Lp.Cancelled{}) == Lp.Unjudged{} : Lp.Verdict}       # either polarity

# LAW loop_settled_turn_is_judged (L3): when the turn of a loop with a
# condition settles in an idle session, having run to its end or failed,
# the loop runs the condition command for that iteration and starts no
# iteration before its evidence
# EXCLUDES: the next iteration sent without a check, a check skipped after
#   a failed turn, a check numbered for another iteration
law loop_settled_turn_is_judged:
  for i: Nat
  for l: Maybe<&2, Nat>
  for d: Maybe<&2, Nat>
  for +c: Lp.Cond
  for b: String
  for f: Nat
  for x: Lp.Last
  for +o: Lp.Out
  for now: Nat
  for fu: Bool
  for hc: {S.has_cond(c) == True{} : Bool}
  for ho: {S.out_halted(o) == False{} : Bool}
  {(S.does(Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}, Lp.Settled{i, o, False{}, now, fu}), S.phase(S.next(Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}, Lp.Settled{i, o, False{}, now, fu}))) == (Lp.Judge{i}, Lp.Judging{}) : Lp.Act & Lp.Phase}

# LAW loop_satisfied_needs_confirmation (L3): a loop becomes ended
# satisfied only at a judged check that is fresh (the loop is judging,
# the check is of its current iteration, the session is idle) and whose
# evidence shows the stop condition (S.confirms)
# EXCLUDES: a loop that reports success when its count, time or budget ran
#   out, when it was stopped, on a settled turn, on stale evidence of an
#   earlier iteration, on exit 1 of `--until`, on a broken or cancelled
#   check, or with no condition at all
law loop_satisfied_needs_confirmation:
  for +s: Lp.St
  for +e: Lp.Ev
  for h: {S.newly_satisfied(s, e) == True{} : Bool}
  {S.confirms(s, e) == True{} : Bool}

# LAW loop_auto_needs_refutation (L3): a loop with a condition starts an
# automatic iteration (any Submit but the first turn of a new `/loop`)
# only at a fresh judged check whose evidence shows the stop condition
# does not hold yet (S.refutes)
# EXCLUDES: an iteration started on a settled turn without evidence, on a
#   broken, cancelled or stale check, or on evidence that shows the stop
#   condition
law loop_auto_needs_refutation:
  for +s: Lp.St
  for +e: Lp.Ev
  for h: {Bool.and(S.has_cond(S.cond(s)), Bool.and(Bool.not(S.is_enter(e)), S.is_submit(S.does(s, e)))) == True{} : Bool}
  {S.refutes(s, e) == True{} : Bool}

# LAW loop_confirmed_ends (L3): fresh evidence that shows the stop
# condition ends the loop satisfied and reports it, whatever the bounds
# say, and is kept as the last evidence
# EXCLUDES: a satisfied condition ignored (the loop runs on), reported as
#   a bound reached, or one more iteration sent first
law loop_confirmed_ends:
  for i: Nat
  for l: Maybe<&2, Nat>
  for d: Maybe<&2, Nat>
  for +c: Lp.Cond
  for b: String
  for f: Nat
  for x: Lp.Last
  for +ev: Lp.Evid
  for now: Nat
  for fu: Bool
  for h: {S.shows_stop(c, ev) == True{} : Bool}
  {Lp.step(Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}, Lp.Judged{i, ev, False{}, now, fu}) == (Lp.St{Lp.Ended{Lp.Satisfied{}}, i, l, d, c, b, f, Lp.Check{i, ev}}, Lp.Report{Lp.Satisfied{}}) : Lp.St & Lp.Act}

# LAW loop_broken_check_ends (L3): evidence that decides (the check was
# not cancelled) and shows neither the stop condition nor its absence ends
# a loop with a condition as a broken check, and reports it
# EXCLUDES: a broken check read as "not yet" (the loop runs forever on a
#   typo), read as satisfied, or silently retried
law loop_broken_check_ends:
  for i: Nat
  for l: Maybe<&2, Nat>
  for d: Maybe<&2, Nat>
  for +c: Lp.Cond
  for b: String
  for f: Nat
  for x: Lp.Last
  for +ev: Lp.Evid
  for now: Nat
  for fu: Bool
  for hc: {S.has_cond(c) == True{} : Bool}
  for hd: {S.decides(ev) == True{} : Bool}
  for hs: {S.shows_stop(c, ev) == False{} : Bool}
  for hg: {S.shows_go(c, ev) == False{} : Bool}
  {(S.does(Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}, Lp.Judged{i, ev, False{}, now, fu}), S.phase(S.next(Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}, Lp.Judged{i, ev, False{}, now, fu}))) == (Lp.Report{Lp.CheckBroke{}}, Lp.Ended{Lp.CheckBroke{}}) : Lp.Act & Lp.Phase}

# LAW loop_cancelled_check_waits (L3): a cancelled check of a loop with a
# condition decides nothing: the loop stays judging the same iteration,
# unchanged
# EXCLUDES: a cancelled check read as a verdict (the loop ends, or the
#   next iteration starts unjudged)
law loop_cancelled_check_waits:
  for i: Nat
  for l: Maybe<&2, Nat>
  for d: Maybe<&2, Nat>
  for +c: Lp.Cond
  for b: String
  for f: Nat
  for x: Lp.Last
  for now: Nat
  for fu: Bool
  for hc: {S.has_cond(c) == True{} : Bool}
  {Lp.step(Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}, Lp.Judged{i, Lp.Cancelled{}, False{}, now, fu}) == (Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}, Lp.Rest{}) : Lp.St & Lp.Act}

# Laws: the start and the stop (L1)
# ---------------------------------

# LAW loop_enter_first_turn (L1): `/loop` with an inline prompt t, when no
# loop is on, sends t as iteration 1 at once (no check first) and the new
# loop is in its turn with t as its prompt and the given condition
# EXCLUDES: the condition judged before the first turn, the first turn
#   numbered 0, another text sent, the condition of an earlier loop kept
law loop_enter_first_turn:
  for +s: Lp.St
  for lim: Lp.Limit
  for c: Lp.Cond
  for t: String
  for now: Nat
  for off: {S.is_on(S.phase(s)) == False{} : Bool}
  {(S.does(s, Lp.Enter{lim, c, Some{t}, now}), (S.phase(S.next(s, Lp.Enter{lim, c, Some{t}, now})), (S.body(S.next(s, Lp.Enter{lim, c, Some{t}, now})), S.cond(S.next(s, Lp.Enter{lim, c, Some{t}, now}))))) == (Lp.Submit{1n, t}, (Lp.Turn{}, (t, c))) : Lp.Act & (Lp.Phase & (String & Lp.Cond))}

# LAW loop_enter_arms (L1): `/loop` with no inline prompt, when no loop is
# on, starts nothing: the new loop is armed with the given condition
# EXCLUDES: an empty prompt sent, the loop left off
law loop_enter_arms:
  for +s: Lp.St
  for lim: Lp.Limit
  for c: Lp.Cond
  for now: Nat
  for off: {S.is_on(S.phase(s)) == False{} : Bool}
  {(S.does(s, Lp.Enter{lim, c, None{}, now}), (S.phase(S.next(s, Lp.Enter{lim, c, None{}, now})), S.cond(S.next(s, Lp.Enter{lim, c, None{}, now})))) == (Lp.Rest{}, (Lp.Armed{}, c)) : Lp.Act & (Lp.Phase & Lp.Cond)}

# LAW loop_enter_sets_bounds (L1, L4): the loop `/loop` starts, when no
# loop is on, has the bound that was typed: a count n leaves exactly n
# automatic iterations and no deadline; a span of ms milliseconds sets
# the deadline ms after the clock of the start and no count; no bound
# sets neither; with or without an inline prompt
# EXCLUDES: `/loop 10m` running with no deadline, a count stored one off
#   or not at all, the first turn spending an automatic iteration, the
#   bound of an earlier loop kept
law loop_enter_sets_bounds:
  for +s: Lp.St
  for n: Nat
  for ms: Nat
  for c: Lp.Cond
  for pr: Maybe<&2, String>
  for now: Nat
  for off: {S.is_on(S.phase(s)) == False{} : Bool}
  {(S.left(S.next(s, Lp.Enter{Lp.Count{n}, c, pr, now})), S.deadline(S.next(s, Lp.Enter{Lp.Count{n}, c, pr, now}))) == (Some{n}, None{}) : Maybe<&2, Nat> & Maybe<&2, Nat>} &
  {(S.left(S.next(s, Lp.Enter{Lp.Span{ms}, c, pr, now})), S.deadline(S.next(s, Lp.Enter{Lp.Span{ms}, c, pr, now}))) == (None{}, Some{Nat.add(now, ms)}) : Maybe<&2, Nat> & Maybe<&2, Nat>} &
  {(S.left(S.next(s, Lp.Enter{Lp.NoLimit{}, c, pr, now})), S.deadline(S.next(s, Lp.Enter{Lp.NoLimit{}, c, pr, now}))) == (None{}, None{}) : Maybe<&2, Nat> & Maybe<&2, Nat>}

# LAW loop_enter_starts_fresh (L1, L6): the loop `/loop` starts, when no
# loop is on, keeps nothing of an earlier loop: no failed turn is counted,
# no evidence is kept, and its iterations are numbered from the start (1
# with an inline prompt, its first turn; 0 without one)
# EXCLUDES: a new loop that inherits the failed turns of the last one (it
#   gives up at its first failure), that shows the last loop's evidence
#   as its own, or whose first turn is numbered after the last loop's
law loop_enter_starts_fresh:
  for +s: Lp.St
  for lim: Lp.Limit
  for c: Lp.Cond
  for t: String
  for now: Nat
  for off: {S.is_on(S.phase(s)) == False{} : Bool}
  {(S.iter(S.next(s, Lp.Enter{lim, c, Some{t}, now})), (S.fails(S.next(s, Lp.Enter{lim, c, Some{t}, now})), S.last(S.next(s, Lp.Enter{lim, c, Some{t}, now})))) == (1n, (0n, Lp.NoCheck{})) : Nat & (Nat & Lp.Last)} &
  {(S.iter(S.next(s, Lp.Enter{lim, c, None{}, now})), (S.fails(S.next(s, Lp.Enter{lim, c, None{}, now})), S.last(S.next(s, Lp.Enter{lim, c, None{}, now})))) == (0n, (0n, Lp.NoCheck{})) : Nat & (Nat & Lp.Last)}

# LAW loop_enter_ends_running (L1): `/loop` while a loop is on ends it as
# stopped and reports it, whatever its arguments; nothing is sent
# EXCLUDES: a second loop started over a running one, its inline prompt
#   sent, the bounds changed under a running loop
law loop_enter_ends_running:
  for +s: Lp.St
  for lim: Lp.Limit
  for c: Lp.Cond
  for pr: Maybe<&2, String>
  for now: Nat
  for on: {S.is_on(S.phase(s)) == True{} : Bool}
  {(S.does(s, Lp.Enter{lim, c, pr, now}), S.phase(S.next(s, Lp.Enter{lim, c, pr, now}))) == (Lp.Report{Lp.Stopped{}}, Lp.Ended{Lp.Stopped{}}) : Lp.Act & Lp.Phase}

# LAW loop_stop_ends (L1): `/loop --stop` while a loop is on ends it as
# stopped and reports it
# EXCLUDES: a stop that only pauses, a stop ignored in a turn or a check
law loop_stop_ends:
  for +s: Lp.St
  for on: {S.is_on(S.phase(s)) == True{} : Bool}
  {(S.does(s, Lp.Stop{}), S.phase(S.next(s, Lp.Stop{}))) == (Lp.Report{Lp.Stopped{}}, Lp.Ended{Lp.Stopped{}}) : Lp.Act & Lp.Phase}

# LAW loop_stop_never_starts (L1): `/loop --stop` with no loop on changes
# nothing and reports nothing
# EXCLUDES: a stop that toggles a loop on, a second end report
law loop_stop_never_starts:
  for +s: Lp.St
  for off: {S.is_on(S.phase(s)) == False{} : Bool}
  {Lp.step(s, Lp.Stop{}) == (s, Lp.Rest{}) : Lp.St & Lp.Act}

# Laws: what is sent again (L2)
# -----------------------------

# LAW loop_resends_body (L2): every automatic iteration (any Submit but
# the first turn of a new `/loop`) sends the loop's prompt as it stands,
# numbered one past the iterations started
# EXCLUDES: a re-send of another text (the last answer, a "continue"
#   note, an empty prompt), an iteration number repeated or skipped
law loop_resends_body:
  for +s: Lp.St
  for +e: Lp.Ev
  for h: {Bool.and(Bool.not(S.is_enter(e)), S.is_submit(S.does(s, e))) == True{} : Bool}
  {S.does(s, e) == Lp.Submit{1n+S.iter(s), S.body(s)} : Lp.Act}

# LAW loop_prompt_adopted (L2): a prompt t the user sends while a loop is
# on becomes the loop's prompt and its turn the next iteration; the count
# left and the condition stay as they were
# EXCLUDES: the old prompt kept after the user sent a new one, a manual
#   prompt spending an automatic iteration, a prompt that drops the
#   condition, a paused loop that stays paused
law loop_prompt_adopted:
  for +s: Lp.St
  for t: String
  for on: {S.is_on(S.phase(s)) == True{} : Bool}
  {(S.does(s, Lp.Prompt{t}), (S.phase(S.next(s, Lp.Prompt{t})), (S.body(S.next(s, Lp.Prompt{t})), (S.left(S.next(s, Lp.Prompt{t})), S.cond(S.next(s, Lp.Prompt{t})))))) == (Lp.Adopt{1n+S.iter(s)}, (Lp.Turn{}, (t, (S.left(s), S.cond(s))))) : Lp.Act & (Lp.Phase & (String & (Maybe<&2, Nat> & Lp.Cond)))}

# LAW loop_prompt_clears_failures (L4): a prompt the user sends while the
# loop is on clears its failed turns: the loop gives up only after three
# turns failed in a row after the user's prompt
# EXCLUDES: a user's prompt that leaves the loop one or two failures from
#   giving up (one failed turn of the user's prompt ends the loop)
law loop_prompt_clears_failures:
  for +s: Lp.St
  for t: String
  for on: {S.is_on(S.phase(s)) == True{} : Bool}
  {S.fails(S.next(s, Lp.Prompt{t})) == 0n : Nat}

# Laws: the bounds (L4)
# ---------------------

# LAW loop_deadline_bounds (L4): a loop with deadline d starts no
# automatic iteration at an event whose clock is at or past d (S.past: any
# event but a new `/loop`; events with no clock never start one)
# EXCLUDES: an iteration started at the deadline itself, the deadline
#   checked only before the condition command ran, a deadline dropped
#   when a count or a condition is set
law loop_deadline_bounds:
  for +s: Lp.St
  for +e: Lp.Ev
  for +d: Nat
  for hd: {S.deadline(s) == Some{d} : Maybe<&2, Nat>}
  for hp: {S.past(e, d) == True{} : Bool}
  {S.is_submit(S.does(s, e)) == False{} : Bool}

# LAW loop_good_turn_forgives (L4): a turn of the loop that ran to its end
# clears the failed turns in a row
# EXCLUDES: failures counted over the whole loop instead of in a row (a
#   long loop dying on its third transient failure)
law loop_good_turn_forgives:
  for i: Nat
  for l: Maybe<&2, Nat>
  for d: Maybe<&2, Nat>
  for c: Lp.Cond
  for b: String
  for f: Nat
  for x: Lp.Last
  for now: Nat
  for fu: Bool
  {S.fails(S.next(Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}, Lp.Settled{i, Lp.Ran{}, False{}, now, fu})) == 0n : Nat}

# LAW loop_failed_turn_counts (L4): a turn of a loop with a condition
# that failed counts as exactly one more failed turn in a row, and the
# condition is still judged (the failed turn may have met it)
# EXCLUDES: one failed turn counted as three (a loop that gives up at its
#   first transient failure), a failure not counted (a loop that never
#   gives up), a failed turn that skips the check
law loop_failed_turn_counts:
  for i: Nat
  for l: Maybe<&2, Nat>
  for d: Maybe<&2, Nat>
  for +c: Lp.Cond
  for b: String
  for f: Nat
  for x: Lp.Last
  for now: Nat
  for fu: Bool
  for hc: {S.has_cond(c) == True{} : Bool}
  {(S.does(Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}, Lp.Settled{i, Lp.Errored{}, False{}, now, fu}), S.fails(S.next(Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}, Lp.Settled{i, Lp.Errored{}, False{}, now, fu}))) == (Lp.Judge{i}, 1n+f) : Lp.Act & Nat}

# LAW loop_failed_turn_goes_on (L4): after a failed turn that is the first
# or the second in a row (f < 2 before it), a funded loop with no
# condition that is inside its bounds (an automatic iteration left when
# there is a count, 1 + n of them; a clock before the deadline dl when
# there is one) starts iteration 1 + i with its prompt, keeps one
# iteration fewer and the same deadline, and has one more failed turn
# counted: in each of the four shapes of the bound (count and deadline,
# count only, deadline only, neither)
# EXCLUDES: a loop that ends at its first or second failed turn, with or
#   without a count or a deadline; a failed turn that resets or skips the
#   count of failures, or that spends nothing of the count
law loop_failed_turn_goes_on:
  for i: Nat
  for n: Nat
  for +dl: Nat
  for b: String
  for +f: Nat
  for x: Lp.Last
  for +now: Nat
  for hf: {Nat.is_lt(f, 2n) == True{} : Bool}
  for hl: {Nat.is_lt(now, dl) == True{} : Bool}
  {Lp.step(Lp.St{Lp.Turn{}, i, Some{1n+n}, Some{dl}, Lp.NoCond{}, b, f, x}, Lp.Settled{i, Lp.Errored{}, False{}, now, True{}}) == (Lp.St{Lp.Turn{}, 1n+i, Some{n}, Some{dl}, Lp.NoCond{}, b, 1n+f, x}, Lp.Submit{1n+i, b}) : Lp.St & Lp.Act} &
  {Lp.step(Lp.St{Lp.Turn{}, i, Some{1n+n}, None{}, Lp.NoCond{}, b, f, x}, Lp.Settled{i, Lp.Errored{}, False{}, now, True{}}) == (Lp.St{Lp.Turn{}, 1n+i, Some{n}, None{}, Lp.NoCond{}, b, 1n+f, x}, Lp.Submit{1n+i, b}) : Lp.St & Lp.Act} &
  {Lp.step(Lp.St{Lp.Turn{}, i, None{}, Some{dl}, Lp.NoCond{}, b, f, x}, Lp.Settled{i, Lp.Errored{}, False{}, now, True{}}) == (Lp.St{Lp.Turn{}, 1n+i, None{}, Some{dl}, Lp.NoCond{}, b, 1n+f, x}, Lp.Submit{1n+i, b}) : Lp.St & Lp.Act} &
  {Lp.step(Lp.St{Lp.Turn{}, i, None{}, None{}, Lp.NoCond{}, b, f, x}, Lp.Settled{i, Lp.Errored{}, False{}, now, True{}}) == (Lp.St{Lp.Turn{}, 1n+i, None{}, None{}, Lp.NoCond{}, b, 1n+f, x}, Lp.Submit{1n+i, b}) : Lp.St & Lp.Act}

# LAW loop_unfunded_never_starts (L4): at an event that says the budget
# funds no further turn, the loop starts no automatic iteration
# EXCLUDES: a loop that spends past its budget, the budget consulted only
#   for loops without a condition
law loop_unfunded_never_starts:
  for +s: Lp.St
  for +e: Lp.Ev
  for h: {S.unfunded(e) == True{} : Bool}
  {S.is_submit(S.does(s, e)) == False{} : Bool}

# The decision point of the laws below: a loop judging iteration i reads
# fresh evidence ev that shows its stop condition does not hold yet (hg:
# the claims on `Lp.Judging{}` states); a loop with no condition whose
# turn i settled is at the same point (the claims on `Lp.Turn{}` states:
# the turn ran to its end, or, in loop_tired_gives_up, failed).

# LAW loop_tired_gives_up (L4): with three or more turns failed in a row
# the loop reports the end turns-failed and is stored as ended with that
# reason, whatever the other bounds
# EXCLUDES: the failure cap hidden behind the count or the budget, a
#   failed-turns end stored as another end (the status names another
#   reason than the report)
law loop_tired_gives_up:
  for i: Nat
  for l: Maybe<&2, Nat>
  for d: Maybe<&2, Nat>
  for +c: Lp.Cond
  for b: String
  for k: Nat
  for x: Lp.Last
  for +ev: Lp.Evid
  for now: Nat
  for fu: Bool
  for hg: {S.shows_go(c, ev) == True{} : Bool}
  {(S.does(Lp.St{Lp.Judging{}, i, l, d, c, b, 3n+k, x}, Lp.Judged{i, ev, False{}, now, fu}), S.phase(S.next(Lp.St{Lp.Judging{}, i, l, d, c, b, 3n+k, x}, Lp.Judged{i, ev, False{}, now, fu}))) == (Lp.Report{Lp.TurnsFailed{}}, Lp.Ended{Lp.TurnsFailed{}}) : Lp.Act & Lp.Phase} &
  {(S.does(Lp.St{Lp.Turn{}, i, l, d, Lp.NoCond{}, b, 2n+k, x}, Lp.Settled{i, Lp.Errored{}, False{}, now, fu}), S.phase(S.next(Lp.St{Lp.Turn{}, i, l, d, Lp.NoCond{}, b, 2n+k, x}, Lp.Settled{i, Lp.Errored{}, False{}, now, fu}))) == (Lp.Report{Lp.TurnsFailed{}}, Lp.Ended{Lp.TurnsFailed{}}) : Lp.Act & Lp.Phase}

# LAW loop_unfunded_stops (L4): with fewer than three turns failed in a
# row and a budget that funds no further turn the loop reports the end
# out-of-budget and is stored as ended with that reason, whatever the
# count and the time
# EXCLUDES: a budget stop reported or stored as the count, the time or
#   success
law loop_unfunded_stops:
  for i: Nat
  for l: Maybe<&2, Nat>
  for d: Maybe<&2, Nat>
  for +c: Lp.Cond
  for b: String
  for +f: Nat
  for x: Lp.Last
  for +ev: Lp.Evid
  for now: Nat
  for hg: {S.shows_go(c, ev) == True{} : Bool}
  for hf: {Nat.is_lt(f, 3n) == True{} : Bool}
  {(S.does(Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}, Lp.Judged{i, ev, False{}, now, False{}}), S.phase(S.next(Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}, Lp.Judged{i, ev, False{}, now, False{}}))) == (Lp.Report{Lp.OutOfBudget{}}, Lp.Ended{Lp.OutOfBudget{}}) : Lp.Act & Lp.Phase} &
  {(S.does(Lp.St{Lp.Turn{}, i, l, d, Lp.NoCond{}, b, f, x}, Lp.Settled{i, Lp.Ran{}, False{}, now, False{}}), S.phase(S.next(Lp.St{Lp.Turn{}, i, l, d, Lp.NoCond{}, b, f, x}, Lp.Settled{i, Lp.Ran{}, False{}, now, False{}}))) == (Lp.Report{Lp.OutOfBudget{}}, Lp.Ended{Lp.OutOfBudget{}}) : Lp.Act & Lp.Phase}

# LAW loop_spent_stops (L4): with fewer than three turns failed in a row,
# a funded budget and no automatic iteration left, the loop reports the
# end out-of-turns and is stored as ended with that reason, whatever the
# time
# EXCLUDES: one more iteration than the count, a spent count reported or
#   stored as the time or as success
law loop_spent_stops:
  for i: Nat
  for d: Maybe<&2, Nat>
  for +c: Lp.Cond
  for b: String
  for +f: Nat
  for x: Lp.Last
  for +ev: Lp.Evid
  for now: Nat
  for hg: {S.shows_go(c, ev) == True{} : Bool}
  for hf: {Nat.is_lt(f, 3n) == True{} : Bool}
  {(S.does(Lp.St{Lp.Judging{}, i, Some{0n}, d, c, b, f, x}, Lp.Judged{i, ev, False{}, now, True{}}), S.phase(S.next(Lp.St{Lp.Judging{}, i, Some{0n}, d, c, b, f, x}, Lp.Judged{i, ev, False{}, now, True{}}))) == (Lp.Report{Lp.OutOfTurns{}}, Lp.Ended{Lp.OutOfTurns{}}) : Lp.Act & Lp.Phase} &
  {(S.does(Lp.St{Lp.Turn{}, i, Some{0n}, d, Lp.NoCond{}, b, f, x}, Lp.Settled{i, Lp.Ran{}, False{}, now, True{}}), S.phase(S.next(Lp.St{Lp.Turn{}, i, Some{0n}, d, Lp.NoCond{}, b, f, x}, Lp.Settled{i, Lp.Ran{}, False{}, now, True{}}))) == (Lp.Report{Lp.OutOfTurns{}}, Lp.Ended{Lp.OutOfTurns{}}) : Lp.Act & Lp.Phase}

# LAW loop_late_stops (L4): with fewer than three turns failed in a row, a
# funded budget, automatic iterations left (n free: 1 + n of them, or no
# count) and a clock at or past the deadline dl, the loop reports the end
# out-of-time and is stored as ended with that reason, with or without a
# condition
# EXCLUDES: an iteration started after the deadline, a late stop reported
#   or stored as the count or as success
law loop_late_stops:
  for i: Nat
  for n: Nat
  for +dl: Nat
  for +c: Lp.Cond
  for b: String
  for +f: Nat
  for x: Lp.Last
  for +ev: Lp.Evid
  for +now: Nat
  for hg: {S.shows_go(c, ev) == True{} : Bool}
  for hf: {Nat.is_lt(f, 3n) == True{} : Bool}
  for hl: {Nat.is_le(dl, now) == True{} : Bool}
  {(S.does(Lp.St{Lp.Judging{}, i, Some{1n+n}, Some{dl}, c, b, f, x}, Lp.Judged{i, ev, False{}, now, True{}}), S.phase(S.next(Lp.St{Lp.Judging{}, i, Some{1n+n}, Some{dl}, c, b, f, x}, Lp.Judged{i, ev, False{}, now, True{}}))) == (Lp.Report{Lp.OutOfTime{}}, Lp.Ended{Lp.OutOfTime{}}) : Lp.Act & Lp.Phase} &
  {(S.does(Lp.St{Lp.Judging{}, i, None{}, Some{dl}, c, b, f, x}, Lp.Judged{i, ev, False{}, now, True{}}), S.phase(S.next(Lp.St{Lp.Judging{}, i, None{}, Some{dl}, c, b, f, x}, Lp.Judged{i, ev, False{}, now, True{}}))) == (Lp.Report{Lp.OutOfTime{}}, Lp.Ended{Lp.OutOfTime{}}) : Lp.Act & Lp.Phase} &
  {(S.does(Lp.St{Lp.Turn{}, i, Some{1n+n}, Some{dl}, Lp.NoCond{}, b, f, x}, Lp.Settled{i, Lp.Ran{}, False{}, now, True{}}), S.phase(S.next(Lp.St{Lp.Turn{}, i, Some{1n+n}, Some{dl}, Lp.NoCond{}, b, f, x}, Lp.Settled{i, Lp.Ran{}, False{}, now, True{}}))) == (Lp.Report{Lp.OutOfTime{}}, Lp.Ended{Lp.OutOfTime{}}) : Lp.Act & Lp.Phase} &
  {(S.does(Lp.St{Lp.Turn{}, i, None{}, Some{dl}, Lp.NoCond{}, b, f, x}, Lp.Settled{i, Lp.Ran{}, False{}, now, True{}}), S.phase(S.next(Lp.St{Lp.Turn{}, i, None{}, Some{dl}, Lp.NoCond{}, b, f, x}, Lp.Settled{i, Lp.Ran{}, False{}, now, True{}}))) == (Lp.Report{Lp.OutOfTime{}}, Lp.Ended{Lp.OutOfTime{}}) : Lp.Act & Lp.Phase}

# LAW loop_inside_continues (L4): with fewer than three turns failed in a
# row, a funded budget, an automatic iteration left when there is a count
# (1 + n of them) and a clock before the deadline dl when there is one,
# the loop starts iteration 1 + i with its prompt, keeps one iteration
# fewer (n) and the same deadline, and is in its turn: for a loop with a
# condition that read refuting evidence, and for a loop with none whose
# turn ran to its end, in each of the four shapes of the bound (count and
# deadline, count only, deadline only, neither)
# EXCLUDES: a loop that stops inside every bound (it never repeats; a
#   duration-only loop that ends at its first check), a count that does
#   not go down, a deadline dropped or moved, an iteration started at a
#   wrong number
law loop_inside_continues:
  for i: Nat
  for n: Nat
  for +dl: Nat
  for +c: Lp.Cond
  for b: String
  for +f: Nat
  for x: Lp.Last
  for +ev: Lp.Evid
  for +now: Nat
  for hg: {S.shows_go(c, ev) == True{} : Bool}
  for hf: {Nat.is_lt(f, 3n) == True{} : Bool}
  for hl: {Nat.is_lt(now, dl) == True{} : Bool}
  {Lp.step(Lp.St{Lp.Judging{}, i, Some{1n+n}, Some{dl}, c, b, f, x}, Lp.Judged{i, ev, False{}, now, True{}}) == (Lp.St{Lp.Turn{}, 1n+i, Some{n}, Some{dl}, c, b, f, Lp.Check{i, ev}}, Lp.Submit{1n+i, b}) : Lp.St & Lp.Act} &
  {Lp.step(Lp.St{Lp.Judging{}, i, Some{1n+n}, None{}, c, b, f, x}, Lp.Judged{i, ev, False{}, now, True{}}) == (Lp.St{Lp.Turn{}, 1n+i, Some{n}, None{}, c, b, f, Lp.Check{i, ev}}, Lp.Submit{1n+i, b}) : Lp.St & Lp.Act} &
  {Lp.step(Lp.St{Lp.Judging{}, i, None{}, Some{dl}, c, b, f, x}, Lp.Judged{i, ev, False{}, now, True{}}) == (Lp.St{Lp.Turn{}, 1n+i, None{}, Some{dl}, c, b, f, Lp.Check{i, ev}}, Lp.Submit{1n+i, b}) : Lp.St & Lp.Act} &
  {Lp.step(Lp.St{Lp.Judging{}, i, None{}, None{}, c, b, f, x}, Lp.Judged{i, ev, False{}, now, True{}}) == (Lp.St{Lp.Turn{}, 1n+i, None{}, None{}, c, b, f, Lp.Check{i, ev}}, Lp.Submit{1n+i, b}) : Lp.St & Lp.Act} &
  {Lp.step(Lp.St{Lp.Turn{}, i, Some{1n+n}, Some{dl}, Lp.NoCond{}, b, f, x}, Lp.Settled{i, Lp.Ran{}, False{}, now, True{}}) == (Lp.St{Lp.Turn{}, 1n+i, Some{n}, Some{dl}, Lp.NoCond{}, b, 0n, x}, Lp.Submit{1n+i, b}) : Lp.St & Lp.Act} &
  {Lp.step(Lp.St{Lp.Turn{}, i, Some{1n+n}, None{}, Lp.NoCond{}, b, f, x}, Lp.Settled{i, Lp.Ran{}, False{}, now, True{}}) == (Lp.St{Lp.Turn{}, 1n+i, Some{n}, None{}, Lp.NoCond{}, b, 0n, x}, Lp.Submit{1n+i, b}) : Lp.St & Lp.Act} &
  {Lp.step(Lp.St{Lp.Turn{}, i, None{}, Some{dl}, Lp.NoCond{}, b, f, x}, Lp.Settled{i, Lp.Ran{}, False{}, now, True{}}) == (Lp.St{Lp.Turn{}, 1n+i, None{}, Some{dl}, Lp.NoCond{}, b, 0n, x}, Lp.Submit{1n+i, b}) : Lp.St & Lp.Act} &
  {Lp.step(Lp.St{Lp.Turn{}, i, None{}, None{}, Lp.NoCond{}, b, f, x}, Lp.Settled{i, Lp.Ran{}, False{}, now, True{}}) == (Lp.St{Lp.Turn{}, 1n+i, None{}, None{}, Lp.NoCond{}, b, 0n, x}, Lp.Submit{1n+i, b}) : Lp.St & Lp.Act}

# Laws: the interrupt (L5)
# ------------------------

# LAW loop_halted_turn_pauses (L5): a turn of the loop that did not run to
# its end (refused, consumed locally, interrupted by the user) pauses the
# loop and starts nothing
# EXCLUDES: a refused prompt re-sent after every yield, an interrupted
#   turn followed by the next iteration
law loop_halted_turn_pauses:
  for i: Nat
  for l: Maybe<&2, Nat>
  for d: Maybe<&2, Nat>
  for c: Lp.Cond
  for b: String
  for f: Nat
  for x: Lp.Last
  for now: Nat
  for fu: Bool
  {(S.does(Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}, Lp.Settled{i, Lp.Halted{}, False{}, now, fu}), S.phase(S.next(Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}, Lp.Settled{i, Lp.Halted{}, False{}, now, fu}))) == (Lp.Rest{}, Lp.Paused{}) : Lp.Act & Lp.Phase}

# LAW loop_abort_pauses (L5): the user's interrupt of a loop that is on
# pauses it and starts nothing; the loop stays on at the same iteration
# with its count left, its deadline, its condition and its last evidence,
# so the next prompt the user sends takes it up again
# EXCLUDES: an Esc that ends the loop (the next prompt no longer resumes
#   it), an Esc that skips an iteration, refills or drops the count or the
#   deadline, forgets the condition or the evidence
law loop_abort_pauses:
  for +s: Lp.St
  for on: {S.is_on(S.phase(s)) == True{} : Bool}
  {(S.does(s, Lp.Abort{}), (S.phase(S.next(s, Lp.Abort{})), (S.iter(S.next(s, Lp.Abort{})), (S.left(S.next(s, Lp.Abort{})), (S.deadline(S.next(s, Lp.Abort{})), (S.cond(S.next(s, Lp.Abort{})), S.last(S.next(s, Lp.Abort{})))))))) == (Lp.Rest{}, (Lp.Paused{}, (S.iter(s), (S.left(s), (S.deadline(s), (S.cond(s), S.last(s))))))) : Lp.Act & (Lp.Phase & (Nat & (Maybe<&2, Nat> & (Maybe<&2, Nat> & (Lp.Cond & Lp.Last)))))}

# Laws: the end (L6)
# ------------------

# LAW loop_report_names_the_end (L6, L9): whenever the loop reports an
# end, at any event from any state, the state it stores is ended with
# that same reason
# EXCLUDES: a reported end with the loop left on (it runs on after "Loop
#   mode disabled"), an end stored with another reason than the one
#   reported (the status names the wrong reason)
law loop_report_names_the_end:
  for +s: Lp.St
  for +e: Lp.Ev
  for w: Lp.End
  for h: {S.does(s, e) == Lp.Report{w} : Lp.Act}
  {S.phase(S.next(s, e)) == Lp.Ended{w} : Lp.Phase}

# Laws: the restart (L7)
# ----------------------

# LAW loop_restart_changes_nothing (L7): a restart leaves the state as it
# was read from storage: the same phase, iteration, count, deadline,
# condition, prompt, failures and evidence
# EXCLUDES: a restart that counts an iteration, clears the condition,
#   resets the failures or ends the loop
law loop_restart_changes_nothing:
  for +s: Lp.St
  {S.next(s, Lp.Restart{}) == s : Lp.St}

# LAW loop_restart_resumes_submit (L7): after any event at which the loop
# started iteration k with text t, a restart takes up that same turn
# (Resume: Rust continues it and sends t only if it never was sent): no
# new iteration
# EXCLUDES: a restart that sends the next iteration, forgets the turn in
#   flight, or resumes with another text or number
law loop_restart_resumes_submit:
  for +s: Lp.St
  for +e: Lp.Ev
  for k: Nat
  for t: String
  for h: {S.does(s, e) == Lp.Submit{k, t} : Lp.Act}
  {S.does(S.next(s, e), Lp.Restart{}) == Lp.Resume{k, t} : Lp.Act}

# LAW loop_restart_resumes_adopted (L7): after the user's prompt t was
# adopted by a loop that is on, a restart takes up that turn with t
# EXCLUDES: a restart that re-sends the old prompt after the user changed
#   it
law loop_restart_resumes_adopted:
  for +s: Lp.St
  for t: String
  for on: {S.is_on(S.phase(s)) == True{} : Bool}
  {S.does(S.next(s, Lp.Prompt{t}), Lp.Restart{}) == Lp.Resume{1n+S.iter(s), t} : Lp.Act}

# LAW loop_restart_rejudges (L7): after any event at which the loop asked
# for the check of iteration k, a restart asks for that check again
# EXCLUDES: a restart that skips the check (the next iteration starts
#   unjudged, or the loop hangs judging)
law loop_restart_rejudges:
  for +s: Lp.St
  for +e: Lp.Ev
  for k: Nat
  for h: {S.does(s, e) == Lp.Judge{k} : Lp.Act}
  {S.does(S.next(s, e), Lp.Restart{}) == Lp.Judge{k} : Lp.Act}

# LAW loop_restart_idle_rests (L7): a restart of a loop that is neither in
# a turn nor judging (off, armed, paused, ended) has nothing to take up
# EXCLUDES: a restart that starts a turn of an armed, paused or ended loop
law loop_restart_idle_rests:
  for +s: Lp.St
  for h: {Bool.or(S.is_turn(S.phase(s)), S.is_judging(S.phase(s))) == False{} : Bool}
  {S.does(s, Lp.Restart{}) == Lp.Rest{} : Lp.Act}

# LAW loop_redelivery_is_noop (L7): an event that may be delivered twice
# after a crash (S.once: a stop, an abort, a settled turn or a judged
# check of an idle session), applied a second time right after the first,
# changes nothing and does nothing
# EXCLUDES: a settled turn counted twice (an iteration skipped, a failure
#   counted twice), a judged check that starts two iterations, a second
#   end report
law loop_redelivery_is_noop:
  for +s: Lp.St
  for +e: Lp.Ev
  for h: {S.once(e) == True{} : Bool}
  {Lp.step(S.next(s, e), e) == (S.next(s, e), Lp.Rest{}) : Lp.St & Lp.Act}

# Laws: queued input (L8)
# -----------------------

# LAW loop_blocked_waits (L8): at an event that says the session is not
# idle (queued user input, unsettled work), the loop changes nothing and
# only waits (Rest or Defer)
# EXCLUDES: an iteration sent ahead of a queued user message, a check run
#   or a verdict acted on while the user's input waits, a count spent
law loop_blocked_waits:
  for +s: Lp.St
  for +e: Lp.Ev
  for h: {S.blocked(e) == True{} : Bool}
  {(S.next(s, e), S.waits(S.does(s, e))) == (s, True{}) : Lp.St & Bool}

# LAW loop_blocked_defers (L8): a loop whose own turn settled, or whose own
# check was judged, while the session is not idle asks to be told again
# (Defer): the event is not dropped
# EXCLUDES: a loop that silently stops after a queued user message (Rest:
#   nobody asks again)
law loop_blocked_defers:
  for i: Nat
  for l: Maybe<&2, Nat>
  for d: Maybe<&2, Nat>
  for c: Lp.Cond
  for b: String
  for f: Nat
  for x: Lp.Last
  for o: Lp.Out
  for ev: Lp.Evid
  for now: Nat
  for fu: Bool
  {S.does(Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}, Lp.Settled{i, o, True{}, now, fu}) == Lp.Defer{} : Lp.Act} &
  {S.does(Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}, Lp.Judged{i, ev, True{}, now, fu}) == Lp.Defer{} : Lp.Act}

# Laws: the evidence kept (L9)
# ----------------------------

# LAW loop_records_evidence (L9): a loop with a condition that reads
# evidence that decides (not cancelled), fresh, keeps it with the
# iteration it was read after, whether the loop then ends or goes on
# EXCLUDES: a status that shows no or stale evidence while the loop runs
#   on, the evidence of the ending check lost
law loop_records_evidence:
  for i: Nat
  for l: Maybe<&2, Nat>
  for d: Maybe<&2, Nat>
  for +c: Lp.Cond
  for b: String
  for f: Nat
  for x: Lp.Last
  for +ev: Lp.Evid
  for now: Nat
  for fu: Bool
  for hc: {S.has_cond(c) == True{} : Bool}
  for hd: {S.decides(ev) == True{} : Bool}
  {S.last(S.next(Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}, Lp.Judged{i, ev, False{}, now, fu})) == Lp.Check{i, ev} : Lp.Last}

# LAW loop_evidence_only_from_checks (L9): no event but a judged check or
# a new `/loop` changes the evidence kept
# EXCLUDES: evidence invented at a settled turn, cleared by a restart, a
#   pause, a prompt or a stop
law loop_evidence_only_from_checks:
  for +s: Lp.St
  for +e: Lp.Ev
  for h: {Bool.or(S.is_enter(e), S.is_judged(e)) == False{} : Bool}
  {S.last(S.next(s, e)) == S.last(s) : Lp.Last}
