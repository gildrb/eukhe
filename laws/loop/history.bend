# eukhe: the laws of area loop, section history: what holds over whole
# histories of events of `/loop` (bend/loop.bend), from any state, stated
# with the helpers of spec/loop/loop.bend (S.acts: what the loop does at
# each event; S.after: the state after them). The requirements (L1-L9) are
# listed in laws/loop/model.bend.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S

# LAW loop_unattended_resends_same (L2): over any unattended history (no
# `/loop`, no prompt of the user) from any state, every text the loop
# sends (an iteration, or a turn taken up after a restart) is the prompt
# the loop had at the start of the history
# EXCLUDES: a prompt that drifts between iterations, a restart that sends
#   another text, a pause that later re-sends an emptied prompt
law loop_unattended_resends_same:
  for +s: Lp.St
  for +h: List<&2, Lp.Ev>
  for u: {S.unattended(h) == True{} : Bool}
  S.TextsAre(S.acts(h, s), S.body(s))

# LAW loop_count_bounds (L4): from any state with n automatic iterations
# left, over any unattended history, the loop starts at most n automatic
# iterations
# EXCLUDES: an off-by-one count, a count that a restart, a blocked or
#   repeated event, a failed turn or a check refills, a count ignored
#   when a condition is set
law loop_count_bounds:
  for +s: Lp.St
  for +h: List<&2, Lp.Ev>
  for +n: Nat
  for hl: {S.left(s) == Some{n} : Maybe<&2, Nat>}
  for u: {S.unattended(h) == True{} : Bool}
  {Nat.is_le(S.submits(S.acts(h, s)), n) == True{} : Bool}

# LAW loop_failing_run_ends (L4): over any unattended history in which no
# turn ran to its end, from a state with f turns already failed in a row,
# the loop starts at most 3 - f automatic iterations (none when f >= 3)
# EXCLUDES: a loop that re-sends forever while every turn fails (an
#   expired credential, a dead provider), a cap that a check or a restart
#   resets
law loop_failing_run_ends:
  for +s: Lp.St
  for +h: List<&2, Lp.Ev>
  for u: {S.unattended(h) == True{} : Bool}
  for nr: {S.none_ran(h) == True{} : Bool}
  {Nat.is_le(S.submits(S.acts(h, s)), Nat.sub(3n, S.fails(s))) == True{} : Bool}

# LAW loop_abort_holds (L5): from any state, at the user's interrupt and
# over any unattended history after it (settled turns, judged checks,
# restarts, stops, more interrupts), the loop starts no turn and no check
# EXCLUDES: an Esc that only skips one iteration, a check that was
#   running at the interrupt and still starts the next iteration, a
#   restart that revives an interrupted loop
law loop_abort_holds:
  for +s: Lp.St
  for +h: List<&2, Lp.Ev>
  for u: {S.unattended(h) == True{} : Bool}
  {S.none_starts(S.acts(Lp.Abort{} <> h, s)) == True{} : Bool}

# LAW loop_off_stays_off (L6): with no loop on (never started, or ended),
# over any history with no `/loop`, the state never changes and every
# answer is Rest
# EXCLUDES: an iteration, a check or a report after the end, an ended
#   loop revived by a prompt, a settled turn, a check or a restart
law loop_off_stays_off:
  for +s: Lp.St
  for +h: List<&2, Lp.Ev>
  for off: {S.is_on(S.phase(s)) == False{} : Bool}
  for ne: {S.no_enter(h) == True{} : Bool}
  {(S.after(h, s), S.all_rest(S.acts(h, s))) == (s, True{}) : Lp.St & Bool}

# LAW loop_reports_once (L6): over any history with no `/loop`, from any
# state, the loop reports an end at most once
# EXCLUDES: an end reported at every later event, a stop after a
#   satisfied condition reported again, an end reported after a restart
law loop_reports_once:
  for +s: Lp.St
  for +h: List<&2, Lp.Ev>
  for ne: {S.no_enter(h) == True{} : Bool}
  {Nat.is_le(S.reports(S.acts(h, s)), 1n) == True{} : Bool}

# LAW loop_keeps_condition (L7): over any history with no `/loop`, from
# any state, the condition stays the one the loop was started with
# EXCLUDES: a condition lost at a pause, a restart, an adopted prompt or
#   the end (a conditioned loop that later runs unjudged)
law loop_keeps_condition:
  for +s: Lp.St
  for +h: List<&2, Lp.Ev>
  for ne: {S.no_enter(h) == True{} : Bool}
  {S.cond(S.after(h, s)) == S.cond(s) : Lp.Cond}

# LAW loop_keeps_deadline (L4, L7): over any history with no `/loop`,
# from any state, the deadline stays the one the loop was started with
# EXCLUDES: a deadline dropped or moved by a pause, an adopted prompt, a
#   restart or an iteration (a paused loop that comes back with no time
#   limit)
law loop_keeps_deadline:
  for +s: Lp.St
  for +h: List<&2, Lp.Ev>
  for ne: {S.no_enter(h) == True{} : Bool}
  {S.deadline(S.after(h, s)) == S.deadline(s) : Maybe<&2, Nat>}

# LAW loop_count_conserved (L4, L7): over any history with no `/loop`,
# from a state with n automatic iterations left, the iterations left
# afterwards are n less the automatic iterations the loop started: only
# an automatic iteration spends the count, and nothing refills or drops
# it (a pause, an adopted prompt, a restart, a failed or a halted turn)
# EXCLUDES: a count refilled or dropped at a pause or a prompt (a paused
#   loop that comes back unbounded), an iteration that spends nothing or
#   two of the count, a count spent by a manual prompt
law loop_count_conserved:
  for +s: Lp.St
  for +h: List<&2, Lp.Ev>
  for +n: Nat
  for hl: {S.left(s) == Some{n} : Maybe<&2, Nat>}
  for ne: {S.no_enter(h) == True{} : Bool}
  {S.left(S.after(h, s)) == Some{Nat.sub(n, S.submits(S.acts(h, s)))} : Maybe<&2, Nat>}

# LAW loop_uncounted_stays (L4, L7): over any history with no `/loop`, a
# loop with no count never gains one
# EXCLUDES: an unbounded loop that stops as out-of-turns after a pause, a
#   prompt or a restart
law loop_uncounted_stays:
  for +s: Lp.St
  for +h: List<&2, Lp.Ev>
  for hl: {S.left(s) == None{} : Maybe<&2, Nat>}
  for ne: {S.no_enter(h) == True{} : Bool}
  {S.left(S.after(h, s)) == None{} : Maybe<&2, Nat>}

# LAW loop_example (L1-L7): anchor (one history, not the requirement):
# `/loop 1 --until 'test -f done' fix it` at clock 5, from no loop: the
# first turn is sent; it settles: the check is asked; exit 1: iteration 2
# is sent with the same text and the count is spent; a restart resumes
# iteration 2; it settles: the check; exit 0: the loop reports satisfied;
# a late settled turn does nothing
law loop_example:
  {S.acts([Lp.Enter{Lp.Count{1n}, Lp.Until{"test -f done"}, Some{"fix it"}, 5n}, Lp.Settled{1n, Lp.Ran{}, False{}, 6n, True{}}, Lp.Judged{1n, Lp.Exited{1n}, False{}, 7n, True{}}, Lp.Restart{}, Lp.Settled{2n, Lp.Ran{}, False{}, 8n, True{}}, Lp.Judged{2n, Lp.Exited{0n}, False{}, 9n, True{}}, Lp.Settled{2n, Lp.Ran{}, False{}, 10n, True{}}], Lp.St{Lp.Off{}, 0n, None{}, None{}, Lp.NoCond{}, "", 0n, Lp.NoCheck{}}) == [Lp.Submit{1n, "fix it"}, Lp.Judge{1n}, Lp.Submit{2n, "fix it"}, Lp.Resume{2n, "fix it"}, Lp.Judge{2n}, Lp.Report{Lp.Satisfied{}}, Lp.Rest{}] : List<&2, Lp.Act>}

