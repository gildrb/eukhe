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

# LAW rec_row_zero_is_no_note (H4.8; R4, R7 of laws/stop.bend): a note's
# row counts the notes of its recovery in a row, so a row of 0 counts
# none: under any caps, any stuck reply (a length stop with any window's
# facts, leaked calls, calls after any rounds in a row, an empty reply),
# after a note of any recovery with row 0 (its own recovery's too), gets
# the help it gets after no note (the first note of its row, whatever the
# other recoveries' caps; laws/stop/recover.bend and the laws above pin
# that help)
# EXCLUDES: a row 0 of the reply's own recovery read as a row at or past
#   its cap (the run failed at the first empty stop, leak, redirect or
#   length stop), as a row other than none, or by another recovery's cap
law rec_row_zero_is_no_note:
  for +rc: RnRecovery.RCfg
  for +s: RnDecision.Stuck
  for +k: RnRecovery.Rk
  {RnDecision.decide.recover(rc, s, k, 0n) == RnDecision.decide.recover(rc, s, RnRecovery.Free{}, 0n) : RnDecision.Help}

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

# the helps the recoveries' model gives a row of the same stuck reply o,
# d its decision on the first: each next reply is read with the record
# the decision before left (Rec.run); a decision that makes no note ends
# the row, and so do `fuel` replies
def rec_helps(fuel: Nat, +rc: RnRecovery.RCfg, +o: RnRecovery.Out, d: RnRecovery.Dec) -> List<&2, RnDecision.Help>:
  match fuel:
    case 0n:
      [RnDecision.Help.of(d)]
    case 1n+f:
      match d:
        case RnRecovery.Dec{a, +r}:
          match a:
            case RnRecovery.Pass{}:
              [RnDecision.Help.of(RnRecovery.Dec{RnRecovery.Pass{}, r})]
            case RnRecovery.Exec{}:
              [RnDecision.Help.of(RnRecovery.Dec{RnRecovery.Exec{}, r})]
            case RnRecovery.Redo{}:
              RnDecision.Help.of(RnRecovery.Dec{RnRecovery.Redo{}, r}) <> rec_helps(f, rc, o, RnRecovery.Rec.step(rc, o, r))
            case RnRecovery.Quit{}:
              [RnDecision.Help.of(RnRecovery.Dec{RnRecovery.Quit{}, r})]
            case RnRecovery.Shrink{}:
              [RnDecision.Help.of(RnRecovery.Dec{RnRecovery.Shrink{}, r})]
            case RnRecovery.Lower{}:
              [RnDecision.Help.of(RnRecovery.Dec{RnRecovery.Lower{}, r})]

# what a record counts of the rounds before: the rounds in a row and the
# last calls' hash, its note left out
def rounds_of(r: RnRecovery.Rec) -> RnRecovery.Rec:
  match r:
    case RnRecovery.Rec{k, row, same, last}:
      RnRecovery.Rec{RnRecovery.Free{}, 0n, same, last}

# the rounds in a row the calls of hash h make after `same` rounds of the
# calls of hash `last`: one more when they are the last round's calls, else
# a new row of one
def rounds.eq(eq: Bool, +same: Nat) -> Nat:
  match eq:
    case True{}:
      1n+same
    case False{}:
      1n

def rounds(+same: Nat, +last: Nat, +h: Nat) -> Nat:
  rounds.eq(Nat.is_eq(last, h), same)

# LAW rec_leak_ladder_ends (H4.8): in the recoveries' model, under any
# caps (`leak` leak notes), leaked calls the harness could not rebuild
# (any hash, kept or not), given again and again after a request whose
# note is no leak note (any row, rounds in a row and last calls' hash),
# each read with the record the reply before left, get leak notes 1 to
# `leak`, then the run fails: markup is never the answer; after a leak
# note of row `leak` or more they fail the run (the rounds a leak note
# keeps: rec_notes_keep_the_rounds)
# EXCLUDES: markup retried forever, run or answered once the leak notes
#   ran out; a row that skips, repeats or restarts a note, or fails the
#   run before the cap, in the model the run reads
law rec_leak_ladder_ends:
  for +rc: RnRecovery.RCfg
  for +h: Nat
  for +kept: Bool
  for +k: RnRecovery.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for +x: Nat
  for other: {leak_note(k) == False{} : Bool}
  {rec_helps(1n+RnRecovery.RCfg.leak(rc), rc, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec.step(rc, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec{k, row, same, last})) == notes_then_quit(RnRecovery.RCfg.leak(rc), 0n) : List<&2, RnDecision.Help>} &
  {RnRecovery.Dec.act(RnRecovery.Rec.step(rc, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec{RnRecovery.Leaks{}, Nat.add(RnRecovery.RCfg.leak(rc), x), same, last})) == RnRecovery.Quit{} : RnRecovery.Act}

# LAW rec_repeat_ladder_ends (H4.8): in the recoveries' model, under any
# caps (`redirect` redirect notes, `repeat` rounds), calls that would make
# `repeat` or more rounds in a row (rounds: one more than the record's
# when they are the last round's calls, else one), given again and again
# after a request whose note is no redirect note (any row), each read
# with the record the reply before left, never run: they get redirect
# notes 1 to `redirect`, then the run fails; after a redirect note of row
# `redirect` or more they fail the run (the rounds a redirect note keeps:
# rec_notes_keep_the_rounds)
# EXCLUDES: a repeat run once the redirect notes ran out (the loop the
#   guard stops, run again on every next identical reply), a repeat
#   redirected forever; a row that skips, repeats or restarts a note in
#   the model the run reads
law rec_repeat_ladder_ends:
  for +rc: RnRecovery.RCfg
  for +h: Nat
  for +kept: Bool
  for +k: RnRecovery.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for +x: Nat
  for +rep: {Nat.is_le(RnRecovery.RCfg.repeat(rc), rounds(same, last, h)) == True{} : Bool}
  for other: {loop_note(k) == False{} : Bool}
  {rec_helps(1n+RnRecovery.RCfg.redirect(rc), rc, RnRecovery.Ran{h, kept}, RnRecovery.Rec.step(rc, RnRecovery.Ran{h, kept}, RnRecovery.Rec{k, row, same, last})) == notes_then_quit(RnRecovery.RCfg.redirect(rc), 0n) : List<&2, RnDecision.Help>} &
  {RnRecovery.Dec.act(RnRecovery.Rec.step(rc, RnRecovery.Ran{h, kept}, RnRecovery.Rec{RnRecovery.Loops{}, Nat.add(RnRecovery.RCfg.redirect(rc), x), same, last})) == RnRecovery.Quit{} : RnRecovery.Act}

# the redirect notes in a row the next request's note makes: its row
# after a redirect note, else none
def redirects(k: RnRecovery.Rk, +row: Nat) -> Nat:
  match k:
    case RnRecovery.Free{}:
      0n
    case RnRecovery.Longs{}:
      0n
    case RnRecovery.Leaks{}:
      0n
    case RnRecovery.Loops{}:
      row
    case RnRecovery.Empties{}:
      0n

# what calls that would make `repeat` or more rounds in a row get, after
# n redirect notes in a row (under: n is below the redirect cap): the next
# redirect note, the rounds in a row and the last calls' hash kept; else
# the failed run, the record as it was
def repeat_help.go(under: Bool, +n: Nat, +k: RnRecovery.Rk, +row: Nat, +same: Nat, +last: Nat) -> RnRecovery.Dec:
  match under:
    case True{}:
      RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Loops{}, 1n+n, same, last}}
    case False{}:
      RnRecovery.Dec{RnRecovery.Quit{}, RnRecovery.Rec{k, row, same, last}}

def repeat_help(+rd: Nat, +k: RnRecovery.Rk, +row: Nat, +same: Nat, +last: Nat) -> RnRecovery.Dec:
  repeat_help.go(Nat.is_lt(redirects(k, row), rd), redirects(k, row), k, row, same, last)

# LAW rec_repeat_never_runs (H4.8): in the recoveries' model, under any
# caps (a redirect cap of 0 included), after any note of any row (any
# rounds in a row, any last calls' hash), calls that would make `repeat`
# or more rounds in a row (rounds: one more than the record's when they
# are the last round's calls, else one), rebuilt leaked calls included,
# never run: while redirect notes are left they get the next redirect
# note; with none left (a redirect note of row `redirect` or more, or a
# redirect cap of 0 after any note) the run fails at once
# EXCLUDES: a repeat run when no redirect note is left (a 5th identical
#   round run under a redirect cap of 0, failing one round late: blind
#   adversary RunAdv22, attack-run-20), whatever the act reads as through
#   Help.of; a repeat redirected past the cap; a row that skips or
#   restarts a note
law rec_repeat_never_runs:
  for +rc: RnRecovery.RCfg
  for +h: Nat
  for +kept: Bool
  for +k: RnRecovery.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for +rep: {Nat.is_le(RnRecovery.RCfg.repeat(rc), rounds(same, last, h)) == True{} : Bool}
  {RnRecovery.Rec.step(rc, RnRecovery.Ran{h, kept}, RnRecovery.Rec{k, row, same, last}) == repeat_help(RnRecovery.RCfg.redirect(rc), k, row, same, last) : RnRecovery.Dec} &
  {RnRecovery.Rec.step(rc, RnRecovery.Leak{True{}, h, kept}, RnRecovery.Rec{k, row, same, last}) == repeat_help(RnRecovery.RCfg.redirect(rc), k, row, same, last) : RnRecovery.Dec}

# LAW rec_help_reads_the_act (H4.8): the help Rust gets of a decision
# (Help.of, which decide.recover and the ladder laws read) is its act:
# calls run, a note of the record's row, the failed run (also for a
# Pass, which no stuck reply gets: rec_stuck_never_passes), a
# compaction, a note of the record's row one level lower
# EXCLUDES: a Help.of that reads the record's recovery (an Exec read as
#   the failed run after a redirect or leak note: the ladder laws then
#   hold while the calls run), or a row other than the record's
law rec_help_reads_the_act:
  for +k: RnRecovery.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  {RnDecision.Help.of(RnRecovery.Dec{RnRecovery.Exec{}, RnRecovery.Rec{k, row, same, last}}) == RnDecision.Runs{} : RnDecision.Help} &
  {RnDecision.Help.of(RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{k, row, same, last}}) == RnDecision.Redoes{row} : RnDecision.Help} &
  {RnDecision.Help.of(RnRecovery.Dec{RnRecovery.Quit{}, RnRecovery.Rec{k, row, same, last}}) == RnDecision.Quits{} : RnDecision.Help} &
  {RnDecision.Help.of(RnRecovery.Dec{RnRecovery.Pass{}, RnRecovery.Rec{k, row, same, last}}) == RnDecision.Quits{} : RnDecision.Help} &
  {RnDecision.Help.of(RnRecovery.Dec{RnRecovery.Shrink{}, RnRecovery.Rec{k, row, same, last}}) == RnDecision.Compacts{} : RnDecision.Help} &
  {RnDecision.Help.of(RnRecovery.Dec{RnRecovery.Lower{}, RnRecovery.Rec{k, row, same, last}}) == RnDecision.Lowers{row} : RnDecision.Help}

# LAW rec_notes_keep_the_rounds (H4.8; R4 of laws/stop.bend): in the
# recoveries' model, under any caps, after any note of any row (any
# rounds in a row, any last calls' hash), the record a stuck reply leaves
# when its calls do not run keeps the rounds in a row and the last calls'
# hash: leaked calls not rebuilt (a leak note or the failed run), calls
# that would make `repeat` or more rounds in a row (a redirect note or
# the failed run), an empty reply (an empty note or the failed run). A
# note is no round: the guard counts the rounds of the calls that ran
# EXCLUDES: a note that resets or bumps the rounds in a row, or forgets
#   the last calls, at any row of its ladder, so that a repeat after it
#   counts from scratch or a fresh call counts as a repeat (blind
#   adversary RunAdv27, attack-run-25: a leak note from row 1 on reset
#   the rounds of calls that were no repeat, and the 5th identical round
#   after it ran)
law rec_notes_keep_the_rounds:
  for +rc: RnRecovery.RCfg
  for +h: Nat
  for +kept: Bool
  for +k: RnRecovery.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  {rounds_of(RnRecovery.Dec.r(RnRecovery.Rec.step(rc, RnRecovery.Leak{False{}, h, kept}, RnRecovery.Rec{k, row, same, last}))) == RnRecovery.Rec{RnRecovery.Free{}, 0n, same, last} : RnRecovery.Rec} &
  ({Nat.is_le(RnRecovery.RCfg.repeat(rc), rounds(same, last, h)) == True{} : Bool} -> {rounds_of(RnRecovery.Dec.r(RnRecovery.Rec.step(rc, RnRecovery.Ran{h, kept}, RnRecovery.Rec{k, row, same, last}))) == RnRecovery.Rec{RnRecovery.Free{}, 0n, same, last} : RnRecovery.Rec}) &
  {rounds_of(RnRecovery.Dec.r(RnRecovery.Rec.step(rc, RnRecovery.Empty{}, RnRecovery.Rec{k, row, same, last}))) == RnRecovery.Rec{RnRecovery.Free{}, 0n, same, last} : RnRecovery.Rec}

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
# reply with no text) always gets an act other than Pass: its calls run,
# a retry with a note, a compaction, a lower level, or the end of the
# run. It is never passed on as it is. That calls run are never a repeat
# is rec_never_runs_a_repeat, not this law
law rec_stuck_gets_help:
  for +rc: RnRecovery.RCfg
  for o: RnRecovery.Out
  for r: RnRecovery.Rec
  {Bool.or(Bool.not(RnRecovery.Out.stuck(o)), RnRecovery.Act.helps(RnRecovery.Dec.act(RnRecovery.Rec.step(rc, o, r)))) == True{} : Bool}

# the act passes the reply on as it is
def passes(a: RnRecovery.Act) -> Bool:
  match a:
    case RnRecovery.Pass{}:
      True{}
    case RnRecovery.Exec{}:
      False{}
    case RnRecovery.Redo{}:
      False{}
    case RnRecovery.Quit{}:
      False{}
    case RnRecovery.Shrink{}:
      False{}
    case RnRecovery.Lower{}:
      False{}

# LAW rec_stuck_never_passes (H4.8): in the recoveries' model, under any
# caps (a cap of 0 included), after any note of any row, a stuck reply is
# never passed on as it is: leaked calls (rebuilt or not, any hash), tool
# calls (any hash, kept or not), a reply with no text and no call, a
# length stop the stop walk continues (any compaction and lower level)
# EXCLUDES: leaked calls, a repeat, an empty reply or a length stop passed
#   on as the answer, at a cap of 0 or past a cap (where the help Rust
#   reads, Help.of, cannot tell a pass from a failed run)
law rec_stuck_never_passes:
  for +rc: RnRecovery.RCfg
  for +k: RnRecovery.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for +rebuilt: Bool
  for +h: Nat
  for +kept: Bool
  for +shrink: Bool
  for +lower: Bool
  {passes(RnRecovery.Dec.act(RnRecovery.Rec.step(rc, RnRecovery.Leak{rebuilt, h, kept}, RnRecovery.Rec{k, row, same, last}))) == False{} : Bool} &
  {passes(RnRecovery.Dec.act(RnRecovery.Rec.step(rc, RnRecovery.Ran{h, kept}, RnRecovery.Rec{k, row, same, last}))) == False{} : Bool} &
  {passes(RnRecovery.Dec.act(RnRecovery.Rec.step(rc, RnRecovery.Empty{}, RnRecovery.Rec{k, row, same, last}))) == False{} : Bool} &
  {passes(RnRecovery.Dec.act(RnRecovery.Rec.step(rc, RnRecovery.Think{shrink, lower}, RnRecovery.Rec{k, row, same, last}))) == False{} : Bool}

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

# What the recoveries' laws read, pinned
# --------------------------------------
# The laws above read the recoveries through tests and measures of the
# code (the fields of the caps, a record and a decision; the rows a
# record counts; Out.stuck, below, again, Rec.capped, Rec.run). Each is
# pinned here, by its constructors or against the requirement's own
# count, so that no law holds because a test it reads says nothing.

# LAW rec_terms_exact (H4.8): the caps, a record and a decision read back
# the fields they were built with; a record counts its row for its own
# recovery only; the rounds in a row of a kept round are the ones it
# makes, a round whose results changed starts a new row of one; a stuck
# reply is leaked calls, tool calls, a reply with no text or a length
# stop the stop walk continues, and no other
# EXCLUDES: a field read from another, or a constant (rec_never_runs_a_repeat
#   and stop_repeat_row_counts then read a constant row), a row read for
#   another recovery, a stuck reply read as not stuck or the other way
#   (rec_stuck_gets_help then holds vacuously)
law rec_terms_exact:
  for +lo: Nat
  for +le: Nat
  for +rd: Nat
  for +rp: Nat
  for +k: RnRecovery.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for +a: RnRecovery.Act
  for +r: RnRecovery.Rec
  for +m: Nat
  for +rb: Bool
  for +h: Nat
  for +kept: Bool
  for +sh: Bool
  for +lw: Bool
  {RnRecovery.RCfg.long(RnRecovery.RCfg{lo, le, rd, rp}) == lo : Nat} &
  {RnRecovery.RCfg.leak(RnRecovery.RCfg{lo, le, rd, rp}) == le : Nat} &
  {RnRecovery.RCfg.redirect(RnRecovery.RCfg{lo, le, rd, rp}) == rd : Nat} &
  {RnRecovery.RCfg.repeat(RnRecovery.RCfg{lo, le, rd, rp}) == rp : Nat} &
  {RnRecovery.Rec.same(RnRecovery.Rec{k, row, same, last}) == same : Nat} &
  {RnRecovery.Dec.act(RnRecovery.Dec{a, r}) == a : RnRecovery.Act} &
  {RnRecovery.Dec.r(RnRecovery.Dec{a, r}) == r : RnRecovery.Rec} &
  {RnRecovery.Rk.longs(RnRecovery.Free{}, row) == 0n : Nat} &
  {RnRecovery.Rk.longs(RnRecovery.Longs{}, row) == row : Nat} &
  {RnRecovery.Rk.longs(RnRecovery.Leaks{}, row) == 0n : Nat} &
  {RnRecovery.Rk.longs(RnRecovery.Loops{}, row) == 0n : Nat} &
  {RnRecovery.Rk.longs(RnRecovery.Empties{}, row) == 0n : Nat} &
  {RnRecovery.Rk.leaks(RnRecovery.Free{}, row) == 0n : Nat} &
  {RnRecovery.Rk.leaks(RnRecovery.Longs{}, row) == 0n : Nat} &
  {RnRecovery.Rk.leaks(RnRecovery.Leaks{}, row) == row : Nat} &
  {RnRecovery.Rk.leaks(RnRecovery.Loops{}, row) == 0n : Nat} &
  {RnRecovery.Rk.leaks(RnRecovery.Empties{}, row) == 0n : Nat} &
  {RnRecovery.Rk.loops(RnRecovery.Free{}, row) == 0n : Nat} &
  {RnRecovery.Rk.loops(RnRecovery.Longs{}, row) == 0n : Nat} &
  {RnRecovery.Rk.loops(RnRecovery.Leaks{}, row) == 0n : Nat} &
  {RnRecovery.Rk.loops(RnRecovery.Loops{}, row) == row : Nat} &
  {RnRecovery.Rk.loops(RnRecovery.Empties{}, row) == 0n : Nat} &
  {RnRecovery.Rk.empties(RnRecovery.Free{}, row) == 0n : Nat} &
  {RnRecovery.Rk.empties(RnRecovery.Longs{}, row) == 0n : Nat} &
  {RnRecovery.Rk.empties(RnRecovery.Leaks{}, row) == 0n : Nat} &
  {RnRecovery.Rk.empties(RnRecovery.Loops{}, row) == 0n : Nat} &
  {RnRecovery.Rk.empties(RnRecovery.Empties{}, row) == row : Nat} &
  {RnRecovery.ran.same(True{}, m) == m : Nat} &
  {RnRecovery.ran.same(False{}, m) == 1n : Nat} &
  {RnRecovery.Out.stuck(RnRecovery.Leak{rb, h, kept}) == True{} : Bool} &
  {RnRecovery.Out.stuck(RnRecovery.Ran{h, kept}) == True{} : Bool} &
  {RnRecovery.Out.stuck(RnRecovery.Noted{}) == False{} : Bool} &
  {RnRecovery.Out.stuck(RnRecovery.Said{}) == False{} : Bool} &
  {RnRecovery.Out.stuck(RnRecovery.Answer{}) == False{} : Bool} &
  {RnRecovery.Out.stuck(RnRecovery.Other{}) == False{} : Bool} &
  {RnRecovery.Out.stuck(RnRecovery.Empty{}) == True{} : Bool} &
  {RnRecovery.Out.stuck(RnRecovery.Think{sh, lw}) == True{} : Bool}

# LAW rec_capped_reads_the_row (H4.8): the cap test rec_notes_capped
# reads (Rec.capped) is the row cap of the record's recovery (Rk.capped),
# and every row within its cap is within it: any row of no recovery, up
# to `long` + 1 length notes, up to `leak` leak notes, up to `redirect`
# redirect notes, up to 3 empty notes (the rows past the cap:
# stop_capped_past_the_cap)
# EXCLUDES: a Rec.capped tied to no row (always true: rec_notes_capped
#   then holds vacuously), a cap that refuses a row within it
law rec_capped_reads_the_row:
  for +rc: RnRecovery.RCfg
  for +k: RnRecovery.Rk
  for +row: Nat
  for +same: Nat
  for +last: Nat
  for +lo: Nat
  for +le: Nat
  for +rd: Nat
  for +rp: Nat
  for +x: Nat
  for +y: Nat
  {RnRecovery.Rec.capped(rc, RnRecovery.Rec{k, row, same, last}) == RnRecovery.Rk.capped(rc, k, row) : Bool} &
  {RnRecovery.Rk.capped(rc, RnRecovery.Free{}, row) == True{} : Bool} &
  {RnRecovery.Rk.capped(RnRecovery.RCfg{Nat.add(x, y), le, rd, rp}, RnRecovery.Longs{}, x) == True{} : Bool} &
  {RnRecovery.Rk.capped(RnRecovery.RCfg{lo, le, rd, rp}, RnRecovery.Longs{}, 1n+lo) == True{} : Bool} &
  {RnRecovery.Rk.capped(RnRecovery.RCfg{lo, Nat.add(x, y), rd, rp}, RnRecovery.Leaks{}, x) == True{} : Bool} &
  {RnRecovery.Rk.capped(RnRecovery.RCfg{lo, le, Nat.add(x, y), rp}, RnRecovery.Loops{}, x) == True{} : Bool} &
  {RnRecovery.Rk.capped(rc, RnRecovery.Empties{}, 0n) == True{} : Bool} &
  {RnRecovery.Rk.capped(rc, RnRecovery.Empties{}, 1n) == True{} : Bool} &
  {RnRecovery.Rk.capped(rc, RnRecovery.Empties{}, 2n) == True{} : Bool} &
  {RnRecovery.Rk.capped(rc, RnRecovery.Empties{}, 3n) == True{} : Bool}

# LAW rec_below_is_less (H4.8): `below`, the test the recoveries' laws
# read for "within a cap", is the order of the naturals
# EXCLUDES: a `below` that is always false (the premises of rec_calls_run,
#   rec_repeat_redirects and stop_repeat_progress_restarts never hold) or
#   always true
law rec_below_is_less:
  for a: Nat
  for b: Nat
  {RnRecovery.below(a, b) == Nat.is_lt(a, b) : Bool}

# LAW rec_again_counts_the_rounds (H4.8): the rounds in a row the code
# counts for calls of hash h after `same` rounds of the calls of hash
# `last` (again) are the rounds the requirement counts (`rounds`): one
# more than `same` when they are the last round's calls, else a new row
# of one
# EXCLUDES: a count that never grows or never restarts (rec_calls_run and
#   stop_repeat_progress_restarts read it in their premises)
law rec_again_counts_the_rounds:
  for +same: Nat
  for +last: Nat
  for +h: Nat
  {RnRecovery.again(same, last, h) == rounds(same, last, h) : Nat}

# LAW rec_run_steps_each_reply (H4.8): the record after any replies
# (Rec.run, which rec_never_runs_a_repeat and rec_notes_capped read)
# starts as a run starts (Rec.init: stop_rec_init_exact) and each reply
# moves it by one step of the recoveries (Rec.step)
# EXCLUDES: a Rec.run that ignores the replies (always the record a run
#   starts with: rec_never_runs_a_repeat and rec_notes_capped then hold
#   vacuously), a reply read twice or skipped
law rec_run_steps_each_reply:
  for +rc: RnRecovery.RCfg
  for +os: List<&2, RnRecovery.Out>
  for +o: RnRecovery.Out
  {RnRecovery.Rec.run(rc, Nil{}) == RnRecovery.Rec.init() : RnRecovery.Rec} &
  {RnRecovery.Rec.run(rc, List.append(&2, RnRecovery.Out, os, o <> Nil{})) == RnRecovery.Dec.r(RnRecovery.Rec.step(rc, o, RnRecovery.Rec.run(rc, os))) : RnRecovery.Rec}
