# eukhe: the laws of area progress_terms: the terms the progress laws read
#
# The model laws of laws/progress.bend (child_*, run_*) state the work
# ledger, the autonomous run's loop and the child watch through the model's
# own terms (`In`, `mem`, `Within`, `Repeats`, `Loops`, `run`, `watch` of
# bend/progress.bend). Fresh adversaries (SpecCheckProgress,
# SpecCheckProgress3) noted that no law pinned them, so a model with
# `In = Empty` passes five of those laws vacuously. Each term is pinned here
# by what it means, never by a copy of its code:
#
# A1: x is an act of xs (`In`, and its Bool `mem`) exactly when xs holds x
#     at some position: xs is a, then x, then b.
# A2: every act of xs is one of s (`Within`): it holds of no acts, of one
#     act exactly when that act is one of s, and of two runs of acts
#     exactly when it holds of each (so of xs exactly when each of its acts
#     is one of s).
# A3: every segment (`Repeats`), every poll (`Loops`) shows only acts of
#     hist exactly when all their acts, run together, are within hist.
# A4: the autonomous run's loop (`run`; H6 of laws/progress.bend): with no
#     continuation, or once stopped, the verdict stays; a steered run goes
#     on like a run that goes on; a continuation with an act the session
#     never did clears the count of stalls; one whose acts are all acts the
#     session did counts one more stall, steers the run when that count is
#     the cap (directors.stallSteps) and stops it once that count reaches
#     twice the cap.
# A5: the child watch (`watch`; H7): with no poll, or once the verdict owes
#     a report or is quiet, it stays; a poll after an act the child never
#     did goes on with a full clock (bend/child.bend `W.fresh`) and the new
#     work as its token; a poll of acts the child did before is looked at
#     (bend/child.bend `look`) 1 + dt ms after the last one with the token
#     unchanged.
#
# Every continuation or poll either holds an act the session never did or
# holds only acts it did: A4 and A5 fix the run's loop and the watch on
# each.

import Base
import ../bend/progress.bend as Pr
import ../bend/child.bend as Ch

# Terms
# -----

# xs holds x at some position: xs is a, then x, then b
def At(+x: Nat, +xs: List<&2, Nat>) -> Type:
  &a: List<&2, Nat> -> &b: List<&2, Nat> -> {xs == List.append(&2, Nat, a, x <> b) : List<&2, Nat>}

# the acts each poll of ps shows, in order
def pt_segs(ps: List<&2, Pr.Peek>) -> List<&2, List<&2, Nat>>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      match p:
        case Pr.Peek{seg, dt}:
          seg <> pt_segs(rest)

# Laws: acts (A1-A3)
# ------------------

# LAW progress_in_at (A1): an act at any position of a list is an act of it,
# for In and for mem
# EXCLUDES: an In that never holds or misses an act past the head, a mem that
#   answers False for an act the list holds (the `news` premises of the
#   progress laws unsatisfiable, the laws vacuous)
law progress_in_at:
  for +a: List<&2, Nat>
  for +x: Nat
  for +b: List<&2, Nat>
  Pr.In(x, List.append(&2, Nat, a, x <> b)) & {Pr.mem(x, List.append(&2, Nat, a, x <> b)) == True{} : Bool}

# LAW progress_in_only_at (A1): an act of a list, for In or for mem, is at
# some position of it
# EXCLUDES: an In or a mem that holds of an act the list does not hold (a mem
#   that is always True makes the `fresh` premises unsatisfiable)
law progress_in_only_at:
  for +x: Nat
  for +xs: List<&2, Nat>
  (Pr.In(x, xs) -> At(x, xs)) & ({Pr.mem(x, xs) == True{} : Bool} -> At(x, xs))

# LAW progress_within_exact (A2): no acts are within any s; one act is within
# s exactly when it is an act of s; two runs of acts, one after the other,
# are within s exactly when each is
# EXCLUDES: a Within that never holds (child_repeat_is_no_work vacuous), one
#   that checks only the first or the last act, one that holds of an act not
#   in s
law progress_within_exact:
  for +x: Nat
  for +a: List<&2, Nat>
  for +b: List<&2, Nat>
  for +s: List<&2, Nat>
  Pr.Within(Nil{}, s) & (((Pr.Within([x], s) -> Pr.In(x, s)) & (Pr.In(x, s) -> Pr.Within([x], s))) & ((Pr.Within(List.append(&2, Nat, a, b), s) -> (Pr.Within(a, s) & Pr.Within(b, s))) & ((Pr.Within(a, s) & Pr.Within(b, s)) -> Pr.Within(List.append(&2, Nat, a, b), s))))

# LAW progress_repeats_flat (A3): segments, and polls, show only acts of hist
# exactly when all their acts, run together, are within hist
# EXCLUDES: a Repeats or Loops that never holds (run_stops_without_progress,
#   child_loop_is_a_stall vacuous), one that checks only the first segment or
#   poll, one that holds of a segment with a new act
law progress_repeats_flat:
  for +segs: List<&2, List<&2, Nat>>
  for +ps: List<&2, Pr.Peek>
  for +hist: List<&2, Nat>
  ((Pr.Repeats(segs, hist) -> Pr.Within(List.concat(&2, Nat, segs), hist)) & (Pr.Within(List.concat(&2, Nat, segs), hist) -> Pr.Repeats(segs, hist))) & ((Pr.Loops(ps, hist) -> Pr.Within(List.concat(&2, Nat, pt_segs(ps)), hist)) & (Pr.Within(List.concat(&2, Nat, pt_segs(ps)), hist) -> Pr.Loops(ps, hist)))

# Laws: the autonomous run's loop (A4)
# ------------------------------------

# LAW progress_run_stays (A4): with no continuation the verdict stays; a
# stopped run stays stopped, with its count, over any continuations
# EXCLUDES: a run that changes its verdict with no continuation, a stopped
#   run that resumes or recounts
law progress_run_stays:
  for +segs: List<&2, List<&2, Nat>>
  for +cap: Nat
  for +hist: List<&2, Nat>
  for +g: Pr.Run
  for +s: Nat
  {Pr.run(Nil{}, cap, hist, g) == g : Pr.Run} & {Pr.run(segs, cap, hist, Pr.Stop{s}) == Pr.Stop{s} : Pr.Run}

# LAW progress_run_new_work_clears (A4): a continuation whose acts include
# one the session never did clears the count of stalls: the run goes on
# from 0 stalls over the rest, the session's acts now with that continuation's
# EXCLUDES: a run that stops or keeps counting on new work, a constant
#   run, a loop that loses the acts it read
law progress_run_new_work_clears:
  for +cap: Nat
  for +s: Nat
  for +hist: List<&2, Nat>
  for +seg: List<&2, Nat>
  for +segs: List<&2, List<&2, Nat>>
  for +x: Nat
  for fresh: {Pr.mem(x, hist) == False{} : Bool}
  for news: Pr.In(x, seg)
  {Pr.run(seg <> segs, cap, hist, Pr.Go{s}) == Pr.run(segs, cap, List.append(&2, Nat, hist, seg), Pr.Go{0n}) : Pr.Run}

# LAW progress_run_repeat_counts (A4): a continuation whose acts are all
# acts the session did counts one more stall; while that count is below
# twice the cap and not the cap the run goes on with it
# EXCLUDES: a repeat that clears or skips the count, a stop before twice
#   the cap, a steer at another count than the cap
law progress_run_repeat_counts:
  for +cap: Nat
  for +s: Nat
  for +hist: List<&2, Nat>
  for +seg: List<&2, Nat>
  for +segs: List<&2, List<&2, Nat>>
  for within: Pr.Within(seg, hist)
  for below: {Nat.is_lt(1n+s, Nat.add(cap, cap)) == True{} : Bool}
  for other: {Nat.is_eq(cap, 1n+s) == False{} : Bool}
  {Pr.run(seg <> segs, cap, hist, Pr.Go{s}) == Pr.run(segs, cap, List.append(&2, Nat, hist, seg), Pr.Go{1n+s}) : Pr.Run}

# LAW progress_run_repeat_steers (A4): a continuation whose acts are all
# acts the session did, its one more stall reaching the cap, steers the
# run: it goes on, steered, with that count, over the continuations that
# follow
# EXCLUDES: a run stopped or left as it was at the cap, a steer at
#   another count
law progress_run_repeat_steers:
  for +s: Nat
  for +hist: List<&2, Nat>
  for +seg: List<&2, Nat>
  for +segs: List<&2, List<&2, Nat>>
  for within: Pr.Within(seg, hist)
  {Pr.run(seg <> segs, 1n+s, hist, Pr.Go{s}) == Pr.run(segs, 1n+s, List.append(&2, Nat, hist, seg), Pr.Steer{1n+s}) : Pr.Run}

# LAW progress_run_steer_goes_on (A4): a steered run is checked at the
# next continuation like a run that goes on with the same count
# EXCLUDES: a steer that stops the run, restarts or freezes its count
law progress_run_steer_goes_on:
  for +cap: Nat
  for +s: Nat
  for +hist: List<&2, Nat>
  for +seg: List<&2, Nat>
  for +segs: List<&2, List<&2, Nat>>
  {Pr.run(seg <> segs, cap, hist, Pr.Steer{s}) == Pr.run(seg <> segs, cap, hist, Pr.Go{s}) : Pr.Run}

# LAW progress_run_repeat_stops (A4): a continuation whose acts are all acts
# the session did, its one more stall reaching twice the cap, stops the
# run at that count, whatever continuations follow
# EXCLUDES: a run that goes on past twice the cap, a stop at another count
law progress_run_repeat_stops:
  for +cap: Nat
  for +s: Nat
  for +hist: List<&2, Nat>
  for +seg: List<&2, Nat>
  for +segs: List<&2, List<&2, Nat>>
  for within: Pr.Within(seg, hist)
  for reach: {Nat.is_le(Nat.add(cap, cap), 1n+s) == True{} : Bool}
  {Pr.run(seg <> segs, cap, hist, Pr.Go{s}) == Pr.Stop{1n+s} : Pr.Run}

# Laws: the child watch (A5)
# --------------------------

# LAW progress_watch_stays (A5): with no poll the verdict stays; a verdict
# that owes a report or is quiet stays over any polls
# EXCLUDES: a watch that changes its verdict with no poll, one that resumes
#   watching a child that owes or is quiet
law progress_watch_stays:
  for +ps: List<&2, Pr.Peek>
  for +cfg: Ch.Cfg
  for +hist: List<&2, Nat>
  for +v: Ch.Next
  for +k: Ch.Report
  {Pr.watch(Nil{}, cfg, hist, v) == v : Ch.Next} & {Pr.watch(ps, cfg, hist, Ch.Owe{k}) == Ch.Owe{k} : Ch.Next} & {Pr.watch(ps, cfg, hist, Ch.Quiet{}) == Ch.Quiet{} : Ch.Next}

# LAW progress_watch_new_work_restarts (A5): a poll after an act the child
# never did, of a watch whose token is the work so far, goes on with a full
# clock and the new work as its token
# EXCLUDES: a watch that ends or keeps counting down on new work, a token
#   that is not the work of the acts so far, a constant watch
law progress_watch_new_work_restarts:
  for +cfg: Ch.Cfg
  for +w: Ch.W
  for +hist: List<&2, Nat>
  for +seg: List<&2, Nat>
  for +dt: Nat
  for +ps: List<&2, Pr.Peek>
  for +x: Nat
  for fresh: {Pr.mem(x, hist) == False{} : Bool}
  for news: Pr.In(x, seg)
  for tok: {Ch.W.tok(w) == Some{Pr.work(hist)} : Maybe<&2, Nat>}
  {Pr.watch(Pr.Peek{seg, dt} <> ps, cfg, hist, Ch.Watch{w}) == Pr.watch(ps, cfg, List.append(&2, Nat, hist, seg), Ch.Watch{Ch.W.fresh(cfg, Some{Pr.work(List.append(&2, Nat, hist, seg))})}) : Ch.Next}

# LAW progress_watch_repeat_keeps_token (A5): a poll whose acts are all acts
# the child did before is looked at 1 + dt ms after the last poll with the
# token unchanged (the work of the acts before it)
# EXCLUDES: a repeated act read as progress (a looping child never stalls),
#   a poll that takes no time or skips the look
law progress_watch_repeat_keeps_token:
  for +cfg: Ch.Cfg
  for +w: Ch.W
  for +hist: List<&2, Nat>
  for +seg: List<&2, Nat>
  for +dt: Nat
  for +ps: List<&2, Pr.Peek>
  for within: Pr.Within(seg, hist)
  {Pr.watch(Pr.Peek{seg, dt} <> ps, cfg, hist, Ch.Watch{w}) == Pr.watch(ps, cfg, List.append(&2, Nat, hist, seg), Ch.look(cfg, w, 1n+dt, Ch.Busy{Some{Pr.work(hist)}})) : Ch.Next}

# the run's loop: a check at each continuation on the acts so far; a
# steered run is checked like one that goes on; a stopped run stays
# stopped
def run_spec(segs: List<&2, List<&2, Nat>>, +cap: Nat, +hist: List<&2, Nat>, g: Pr.Run) -> Pr.Run:
  match segs:
    case Nil{}:
      g
    case +seg <> rest:
      match g:
        case Pr.Go{s}:
          run_spec(rest, cap, List.append(&2, Nat, hist, seg), Pr.check(cap, s, Pr.grew(hist, seg)))
        case Pr.Stop{s}:
          Pr.Stop{s}
        case Pr.Steer{s}:
          run_spec(rest, cap, List.append(&2, Nat, hist, seg), Pr.check(cap, s, Pr.grew(hist, seg)))

# x is one of xs
def mem_spec(+x: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(Nat.is_eq(h, x), mem_spec(x, t))

def stalls_spec(g: Pr.Run) -> Nat:
  match g:
    case Pr.Go{s}:
      s
    case Pr.Stop{s}:
      s
    case Pr.Steer{s}:
      s

def watch_spec.at(+cfg: Ch.Cfg, t: Nat, +dt: Nat, x: Ch.Next) -> Ch.Next:
  match x:
    case Ch.Watch{w}:
      Ch.look(cfg, w, 1n+dt, Ch.Busy{Some{t}})
    case Ch.Owe{k}:
      Ch.Owe{k}
    case Ch.Quiet{}:
      Ch.Quiet{}

# the watch: at each poll, a watching verdict looks again with the work so
# far and one more interval; a verdict that owes or is quiet stays
def watch_spec(ps: List<&2, Pr.Peek>, +cfg: Ch.Cfg, +hist: List<&2, Nat>, x: Ch.Next) -> Ch.Next:
  match ps:
    case Nil{}:
      x
    case p <> rest:
      match p:
        case Pr.Peek{+seg, +dt}:
          watch_spec(rest, cfg, List.append(&2, Nat, hist, seg), watch_spec.at(cfg, Pr.work(List.append(&2, Nat, hist, seg)), dt, x))

# LAW progress_terms_exact: the model's membership, the stall count of a verdict, the run's
# loop and the child watch are what the progress laws read them as
# EXCLUDES: terms that make the run and child laws vacuous or say less than their names
law progress_terms_exact:
  for +x: Nat
  for +xs: List<&2, Nat>
  for +g: Pr.Run
  for +segs: List<&2, List<&2, Nat>>
  for +cap: Nat
  for +hist: List<&2, Nat>
  for +ps: List<&2, Pr.Peek>
  for +cfg: Ch.Cfg
  for +v: Ch.Next
  {Pr.mem(x, xs) == mem_spec(x, xs) : Bool} & {Pr.Run.stalls(g) == stalls_spec(g) : Nat} & {Pr.run(segs, cap, hist, g) == run_spec(segs, cap, hist, g) : Pr.Run} & {Pr.watch(ps, cfg, hist, v) == watch_spec(ps, cfg, hist, v) : Ch.Next}
