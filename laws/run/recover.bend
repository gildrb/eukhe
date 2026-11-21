# eukhe: the laws of area run, section recover: the recoveries of a stuck
# model (H4.8 of the requirement table in laws/run/model.bend), stated over
# the decision Rust calls (decide.recover, decide.reply of
# bend/run/decision.bend) and over the recoveries' model (Rec of
# bend/run/recovery.bend)

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ./model.bend as RunModel

# (H4.8) A stuck model gets a recovery, each with a cap
# -----------------------------------------------------
# What Rust calls is decide.recover (decide.rs `recover`): the stuck
# reply as Rust reads it (a length stop the stop walk continues, with its
# window's facts; leaked calls it could not rebuild; calls with the
# rounds in a row before them as repeat.rs counts them; an empty reply),
# the caps, and the recovery and row the request's note counts (note.rs
# `NoteCause::recovery`). Rust ends the next request with the note of the
# row a help names and asks about that request's reply with that note's
# recovery and row; the laws below feed each help's row back that way.
# An empty reply and a length stop: laws/stop/recover.bend.
# The recoveries' model Rec (Rec.step, Rec.run of
# bend/run/recovery.bend), which decide.recover reads one reply with, is
# stated after them.

# the note is a leak or a redirect note
def leak_note(k: RnRecovery.Rk) -> Bool:
  match k:
    case RnRecovery.Free{}:
      False{}
    case RnRecovery.Longs{}:
      False{}
    case RnRecovery.Leaks{}:
      True{}
    case RnRecovery.Loops{}:
      False{}
    case RnRecovery.Empties{}:
      False{}

def loop_note(k: RnRecovery.Rk) -> Bool:
  match k:
    case RnRecovery.Free{}:
      False{}
    case RnRecovery.Longs{}:
      False{}
    case RnRecovery.Leaks{}:
      False{}
    case RnRecovery.Loops{}:
      True{}
    case RnRecovery.Empties{}:
      False{}

# the helps a row of stuck replies s gets, the first of them h: each next
# request carries the note of recovery k with the row the help before
# made; a help that makes no such note ends the row, and so do `fuel`
# replies
def helps(fuel: Nat, +rc: RnRecovery.RCfg, +s: RnDecision.Stuck, +k: RnRecovery.Rk, +h: RnDecision.Help) -> List<&2, RnDecision.Help>:
  match fuel:
    case 0n:
      [h]
    case 1n+f:
      match h:
        case RnDecision.Runs{}:
          [RnDecision.Runs{}]
        case RnDecision.Redoes{+n}:
          RnDecision.Redoes{n} <> helps(f, rc, s, k, RnDecision.decide.recover(rc, s, k, n))
        case RnDecision.Quits{}:
          [RnDecision.Quits{}]
        case RnDecision.Compacts{}:
          [RnDecision.Compacts{}]
        case RnDecision.Lowers{n}:
          [RnDecision.Lowers{n}]

# m notes in a row after j notes (Redoes j+1 to j+m), then the run fails
def notes_then_quit(m: Nat, +j: Nat) -> List<&2, RnDecision.Help>:
  match m:
    case 0n:
      [RnDecision.Quits{}]
    case 1n+q:
      RnDecision.Redoes{1n+j} <> notes_then_quit(q, 1n+j)

# LAW rec_leak_notes_then_fails (H4.8): under any caps (`leak` leak
# notes), after a request whose note is no leak note (any row), leaked
# calls the harness could not rebuild, each request carrying the leak note
# the help before made, get leak notes 1 to `leak`, then the run fails:
# markup is never the answer; after a leak note of row `leak` or more
# they fail the run
# EXCLUDES: markup retried forever or answered, a cap off by one either
#   way, a row that does not grow or does not start at 1 after another
#   note
law rec_leak_notes_then_fails:
  for +rc: RnRecovery.RCfg
  for +k: RnRecovery.Rk
  for +row: Nat
  for +x: Nat
  for other: {leak_note(k) == False{} : Bool}
  {helps(1n+RnRecovery.RCfg.leak(rc), rc, RnDecision.Leaked{}, RnRecovery.Leaks{}, RnDecision.decide.recover(rc, RnDecision.Leaked{}, k, row)) == notes_then_quit(RnRecovery.RCfg.leak(rc), 0n) : List<&2, RnDecision.Help>} &
  {RnDecision.decide.recover(rc, RnDecision.Leaked{}, RnRecovery.Leaks{}, Nat.add(RnRecovery.RCfg.leak(rc), x)) == RnDecision.Quits{} : RnDecision.Help}

# LAW rec_repeat_runs_below_cap (H4.8): under any caps, after any note of
# any row, calls that would make fewer than `repeat` rounds in a row with
# the same calls and the same results (before + 1 below the cap) run: the
# recoveries never stop a call that is no repeat
# EXCLUDES: a call that is no repeat redirected or failing the run, a
#   repeat cap one round early
law rec_repeat_runs_below_cap:
  for +rc: RnRecovery.RCfg
  for +before: Nat
  for +k: RnRecovery.Rk
  for +row: Nat
  for fresh: {Nat.is_lt(1n+before, RnRecovery.RCfg.repeat(rc)) == True{} : Bool}
  {RnDecision.decide.recover(rc, RnDecision.Repeats{before}, k, row) == RnDecision.Runs{} : RnDecision.Help}

# LAW rec_repeat_redirects_then_fails (H4.8): under any caps, calls that
# would make `repeat` or more rounds in a row with the same calls and the
# same results never run: after a request whose note is no redirect note
# (any row), such calls, each request carrying the redirect note the help
# before made, get redirect notes 1 to `redirect`, then the run fails;
# after a redirect note of row `redirect` or more they fail the run
# EXCLUDES: a repeat run (the loop the guard stops), a repeat redirected
#   forever, a cap off by one either way, a row that does not start at 1
#   after another note
law rec_repeat_redirects_then_fails:
  for +rc: RnRecovery.RCfg
  for +before: Nat
  for +k: RnRecovery.Rk
  for +row: Nat
  for +x: Nat
  for +rep: {Nat.is_le(RnRecovery.RCfg.repeat(rc), 1n+before) == True{} : Bool}
  for other: {loop_note(k) == False{} : Bool}
  {helps(1n+RnRecovery.RCfg.redirect(rc), rc, RnDecision.Repeats{before}, RnRecovery.Loops{}, RnDecision.decide.recover(rc, RnDecision.Repeats{before}, k, row)) == notes_then_quit(RnRecovery.RCfg.redirect(rc), 0n) : List<&2, RnDecision.Help>} &
  {RnDecision.decide.recover(rc, RnDecision.Repeats{before}, RnRecovery.Loops{}, Nat.add(RnRecovery.RCfg.redirect(rc), x)) == RnDecision.Quits{} : RnDecision.Help}

# LAW rec_redo_retries_with_a_note (H4.7, H4.8): in the recoveries' model,
# the reply a Redo makes (Act.reply, whatever the reply was) is, under any
# limits and from any counts, a noted reply to decide.reply: retried with
# a note while the notes last, else the run fails; so a recovery's retry
# never sends the request again (the note names the next attempt)
# EXCLUDES: a recovery's retry taken as a transient error (the stuck
#   request sent again), a recovery that spends retries
law rec_redo_retries_with_a_note:
  for -pass: RnState.Reply
  for +l: RnDecision.Lim
  for +t: RnDecision.At
  {RnDecision.decide.reply(l, t, RnRecovery.Act.reply(RnRecovery.Redo{}, pass)) == RunModel.then_if(Nat.is_lt(RnDecision.At.notes(t), RnDecision.Lim.notes(l)), RnDecision.DoNote{}, RnDecision.DoFail{}) : RnDecision.Then}

# The recoveries' model (Rec)
# ---------------------------
# LAW rec_leak_rebuilt_is_calls: leaked calls that every parse and name an offered tool are rebuilt:
# the run reads them as the same calls made as tool calls
law rec_leak_rebuilt_is_calls:
  for +rc: RnRecovery.RCfg
  for +h: Nat
  for kept: Bool
  for r: RnRecovery.Rec
  {RnRecovery.Rec.step(rc, RnRecovery.Leak{True{}, h, kept}, r) == RnRecovery.Rec.step(rc, RnRecovery.Ran{h, kept}, r) : RnRecovery.Dec}

# LAW rec_leak_row_starts_at_one (H4.8): in the recoveries' model, under a leak cap of at least
# one note (any other caps), after a request whose note is no leak note
# (any row, any rounds in a row, any last calls' hash), leaked calls that
# were not rebuilt (any hash, kept or not) are retried with leak note 1,
# the rounds in a row and the last calls' hash kept
# EXCLUDES: a leak row that starts at another note than 1, or fails the
#   run at once, after no note or another recovery's note; a row start
#   that drops the rounds in a row or the last hash
law rec_leak_row_starts_at_one:
  for +lg: Nat
  for +lk: Nat
  for +rd: Nat
  for +rp: Nat
  for +h: Nat
  for +kept: Bool
  for +k: RnRecovery.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for other: {leak_note(k) == False{} : Bool}
  {RnRecovery.Rec.step(RnRecovery.RCfg{lg, 1n+lk, rd, rp}, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec{k, row, same, last}) == RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Leaks{}, 1n, same, last}} : RnRecovery.Dec}

# LAW rec_redirect_row_starts_at_one (H4.8): in the recoveries' model, under a redirect cap of
# at least one note (any other caps), after a request whose note is no
# redirect note (any row, any rounds in a row, any last calls' hash),
# calls that would make `repeat` or more rounds in a row (not below the
# repeat cap) never run: they are retried with redirect note 1, the
# rounds in a row and the last calls' hash kept
# EXCLUDES: a repeat row that starts at another note than 1, runs the
#   calls, or fails the run at once, after no note or another recovery's
#   note; a row start that drops the rounds in a row or the last hash
law rec_redirect_row_starts_at_one:
  for +lg: Nat
  for +lk: Nat
  for +rd: Nat
  for +rp: Nat
  for +h: Nat
  for +kept: Bool
  for +k: RnRecovery.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for rep: {RnRecovery.below(RnRecovery.again(same, last, h), rp) == False{} : Bool}
  for other: {loop_note(k) == False{} : Bool}
  {RnRecovery.Rec.step(RnRecovery.RCfg{lg, lk, 1n+rd, rp}, RnRecovery.Ran{h, kept}, RnRecovery.Rec{k, row, same, last}) == RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Loops{}, 1n, same, last}} : RnRecovery.Dec}

# LAW rec_user_breaks_the_row (H4.8): in the recoveries' model, a user
# message (Said) sets the rounds in a row the model counts (Rec.same) to
# none and keeps the note's recovery, its row and the last calls' hash
law rec_user_breaks_the_row:
  for +rc: RnRecovery.RCfg
  for +k: RnRecovery.Rk
  for +row: Nat
  for same: Nat
  for +last: Nat
  {RnRecovery.Dec.r(RnRecovery.Rec.step(rc, RnRecovery.Said{}, RnRecovery.Rec{k, row, same, last})) == RnRecovery.Rec{k, row, 0n, last} : RnRecovery.Rec}

# LAW rec_other_replies_pass (H4.7, H4.8): in the recoveries' model, under any caps, from any
# record, a reply no recovery reads passes on as it is (Pass): a noted
# reply, whose retry carries its own note and no recovery's, ends the row
# of notes and keeps the rounds in a row and the last calls' hash; a user
# message keeps the row of notes and ends the rounds in a row; an answer
# ends both; any other reply keeps the record
# EXCLUDES: a passed reply retried, run or failed; a row of notes that
#   goes on across a noted retry (a recovery's next note counted from a
#   note the request no longer carries); a record changed by a reply that
#   changes nothing
law rec_other_replies_pass:
  for +rc: RnRecovery.RCfg
  for +k: RnRecovery.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  {RnRecovery.Rec.step(rc, RnRecovery.Noted{}, RnRecovery.Rec{k, row, same, last}) == RnRecovery.Dec{RnRecovery.Pass{}, RnRecovery.Rec{RnRecovery.Free{}, 0n, same, last}} : RnRecovery.Dec} &
  {RnRecovery.Rec.step(rc, RnRecovery.Said{}, RnRecovery.Rec{k, row, same, last}) == RnRecovery.Dec{RnRecovery.Pass{}, RnRecovery.Rec{k, row, 0n, last}} : RnRecovery.Dec} &
  {RnRecovery.Rec.step(rc, RnRecovery.Answer{}, RnRecovery.Rec{k, row, same, last}) == RnRecovery.Dec{RnRecovery.Pass{}, RnRecovery.Rec{RnRecovery.Free{}, 0n, 0n, last}} : RnRecovery.Dec} &
  {RnRecovery.Rec.step(rc, RnRecovery.Other{}, RnRecovery.Rec{k, row, same, last}) == RnRecovery.Dec{RnRecovery.Pass{}, RnRecovery.Rec{k, row, same, last}} : RnRecovery.Dec}

# LAW rec_user_message_lets_calls_run (H4.8): in the recoveries' model,
# under a repeat cap past one round, after a user message any calls run
# (with the same hash as the last round's or not, whatever the recoveries
# held before): no call repeats a call made before the user spoke
# EXCLUDES: a row that goes on across a user message (calls the user
#   asked for again redirected as a repeat)
law rec_user_message_lets_calls_run:
  for +rc: RnRecovery.RCfg
  for +h: Nat
  for +kept: Bool
  for r: RnRecovery.Rec
  for two: {Nat.is_lt(1n, RnRecovery.RCfg.repeat(rc)) == True{} : Bool}
  {RnRecovery.Dec.act(RnRecovery.Rec.step(rc, RnRecovery.Ran{h, kept}, RnRecovery.Dec.r(RnRecovery.Rec.step(rc, RnRecovery.Said{}, r)))) == RnRecovery.Exec{} : RnRecovery.Act}

# LAW rec_notes_capped (H4.8): in the recoveries' model, after any replies
# under any caps, the row of the next note is within its recovery's cap
# as Rk.capped bounds it: at most `leak` leak notes, `redirect` redirect
# notes and Stop.empty_cap empty notes, and at most `long` + 1 length
# notes (the ladder's last rung, one thinking level lower, is one more);
# stop_capped_past_the_cap (laws/stop/recover.bend) shows the bound bites
law rec_notes_capped:
  for +rc: RnRecovery.RCfg
  for +os: List<&2, RnRecovery.Out>
  {RnRecovery.Rec.capped(rc, RnRecovery.Rec.run(rc, os)) == True{} : Bool}

# LAW rec_never_runs_a_repeat (H4.8): in the recoveries' model, after any
# replies under any caps, the rounds in a row with the same calls and the
# same results that the model counts (Rec.same) stay below
# max(repeat, 1): stop_repeat_row_counts and stop_repeat_row_restarts
# (laws/stop/recover.bend) show that the count grows by one a kept round
# and restarts at 1 on other calls. This replaces the loop guard of H4.3
# (a run failed after LOOP_ROUNDS such rounds)
law rec_never_runs_a_repeat:
  for +rc: RnRecovery.RCfg
  for +os: List<&2, RnRecovery.Out>
  {RnRecovery.below(RnRecovery.Rec.same(RnRecovery.Rec.run(rc, os)), Nat.max(RnRecovery.RCfg.repeat(rc), 1n)) == True{} : Bool}

# LAW rec_stuck_gets_help: the harness never just watches a stuck model: a stuck reply (a
# length stop the stop walk continues, leaked tool calls, tool calls, a
# reply with no text) always gets
# an act that does something: its calls run (no repeat), a retry with a
# note, an answer, or the end of the run. It is never passed on as it is
law rec_stuck_gets_help:
  for +rc: RnRecovery.RCfg
  for o: RnRecovery.Out
  for r: RnRecovery.Rec
  {Bool.or(Bool.not(RnRecovery.Out.stuck(o)), RnRecovery.Act.helps(RnRecovery.Dec.act(RnRecovery.Rec.step(rc, o, r)))) == True{} : Bool}

# LAW rec_quit_fails: a recovery at its cap fails the run on the model, at once
law rec_quit_fails:
  for +cfg: RnState.Cfg
  for -pass: RnState.Reply
  for +r: Nat
  for +c: Nat
  for +a: Nat
  for +n: Nat
  for +p: Nat
  {RnStep.call(cfg, RnRecovery.Act.reply(RnRecovery.Quit{}, pass), r, c, a, n, p) == RnState.St{RnState.Failed{RnState.Model{}}, r, c, a, n, p} : RnState.St}
