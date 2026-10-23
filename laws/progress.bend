# eukhe: the laws of area progress

import Base
import ../bend/child.bend as Ch
import ../bend/ffi_progress.bend as FPr
import ../bend/progress.bend as Pr
import ./base.bend as LawsBase

# ---- progress ----

# LAWS (audit H6, H7, M5, L5): when the harness checks a loop, progress
# is new work, a loop of the same work stops in time, and what the harness
# changes or drops on its own reaches the user. Each law is an open claim
# about the models in bend/progress.bend (and bend/child.bend for the
# subagent watch); PROOF.bend proves them (as Progress.<law>) with the lemmas of
# proof/progress/.

# (H7) A subagent's progress is new work
# --------------------------------------
# The child's progress token is the work of its acts (Pr.work: its
# distinct tool calls with their results, and its accepted progress
# notes), so events alone (streamed deltas, retries, answers) are no
# progress. The watch of bend/child.bend reads the token.

# LAW: acts the session did before add no work: a child that repeats the
# same calls with the same results keeps its token
law child_repeat_is_no_work:
  for +seen: List<&2, Nat>
  for +loop: List<&2, Nat>
  for within: Pr.Within(loop, seen)
  {Pr.work(List.append(&2, Nat, seen, loop)) == Pr.work(seen) : Nat}

# LAW: a child that loops is a stall: polls of a child whose acts since
# the watch last saw progress are all acts it did before, at least as many
# as the ms left on the clock, end the watch (each poll takes 1 ms or more)
law child_loop_is_a_stall:
  for +cfg: Ch.Cfg
  for +w: Ch.W
  for +hist: List<&2, Nat>
  for p: Pr.Peek
  for +ps: List<&2, Pr.Peek>
  for loops: Pr.Loops(p <> ps, hist)
  for tok: {Ch.W.tok(w) == Some{Pr.work(hist)} : Maybe<&2, Nat>}
  for long: {Nat.is_le(Ch.W.left(w), List.length(&2, Pr.Peek, p <> ps)) == True{} : Bool}
  {Ch.Next.watching(Pr.watch(p <> ps, cfg, hist, Ch.Watch{w})) == False{} : Bool}

# LAW: new work is progress: a poll after an act the child never did
# before goes on with a full clock
law child_new_work_is_progress:
  for +cfg: Ch.Cfg
  for +w: Ch.W
  for +e: Nat
  for +seen: List<&2, Nat>
  for +seg: List<&2, Nat>
  for +x: Nat
  for fresh: {Pr.mem(x, seen) == False{} : Bool}
  for news: Pr.In(x, seg)
  for tok: {Ch.W.tok(w) == Some{Pr.work(seen)} : Maybe<&2, Nat>}
  {Ch.look(cfg, w, e, Ch.Busy{Some{Pr.work(List.append(&2, Nat, seen, seg))}}) == Ch.Watch{Ch.W.fresh(cfg, Some{Pr.work(List.append(&2, Nat, seen, seg))})} : Ch.Next}

# (H6) A goal without progress stops
# ----------------------------------
# At each goal continuation the progress check asks whether the work grew
# since the last continuation (Pr.check, cap: directors.stallSteps).

# LAW: continuations in a row whose acts are all acts the session did
# before, at least as many as the cap, stop the goal, whatever count of
# stalls it starts from
law goal_stops_without_progress:
  for +cap: Nat
  for +s: Nat
  for +hist: List<&2, Nat>
  for +seg: List<&2, Nat>
  for +segs: List<&2, List<&2, Nat>>
  for repeats: Pr.Repeats(seg <> segs, hist)
  for long: {Nat.is_le(cap, List.length(&2, List<&2, Nat>, seg <> segs)) == True{} : Bool}
  {Pr.Goal.stopped(Pr.goal(seg <> segs, cap, hist, Pr.Go{s})) == True{} : Bool}

# LAW: a continuation with an act the session never did before clears
# the count: the goal goes on
law goal_progress_continues:
  for +cap: Nat
  for +s: Nat
  for +hist: List<&2, Nat>
  for +seg: List<&2, Nat>
  for +x: Nat
  for fresh: {Pr.mem(x, hist) == False{} : Bool}
  for news: Pr.In(x, seg)
  {Pr.check(cap, s, Pr.grew(hist, seg)) == Pr.Go{0n} : Pr.Goal}

# The check the Rust goal loop runs (bend/progress.bend `judge`): it
# compares the ledger's counts, and holds the count of stalls below t
# (t = 10^14 - 1, the largest Nat the core's wire carries). Every law
# holds for every t.

# LAW: the first check of a run or a goal starts the count
law goal_first_check_starts:
  for +t: Nat
  for +cap: Nat
  for +work: Nat
  {Pr.judge(t, cap, None{}, work) == Pr.Go{0n} : Pr.Goal}

# LAW: below t, a later check is the progress check on whether the
# work's count grew
law goal_judge_is_check:
  for +t: Nat
  for +cap: Nat
  for +s: Nat
  for +w: Nat
  for +work: Nat
  for below: {Nat.is_lt(s, t) == True{} : Bool}
  {Pr.judge(t, cap, Some{Pr.Prior{s, w}}, work) == Pr.check(cap, s, Nat.is_lt(w, work)) : Pr.Goal}

# LAW: the count grew exactly when the session did new work, so the goal
# laws above hold for the counts the Rust loop compares
law goal_judge_counts_work:
  for +hist: List<&2, Nat>
  for +seg: List<&2, Nat>
  {Nat.is_lt(Pr.work(hist), Pr.work(List.append(&2, Nat, hist, seg))) == Pr.grew(hist, seg) : Bool}

# LAW: the count of stalls stays within t
# EXCLUDES: a count past the compiled core's Nat range (the process stops)
law goal_judge_held:
  for +u: Nat
  for +cap: Nat
  for p: Maybe<&2, Pr.Prior>
  for +work: Nat
  {Nat.is_le(Pr.Goal.stalls(Pr.judge(1n+u, cap, p, work)), 1n+u) == True{} : Bool}

# LAW: a count at t stops a goal with a cap within t that did no new work
# EXCLUDES: a held count that never reaches the cap
law goal_judge_top_stops:
  for +u: Nat
  for +cap: Nat
  for +w: Nat
  for +work: Nat
  for fits: {Nat.is_le(cap, 1n+u) == True{} : Bool}
  for same: {Nat.is_lt(w, work) == False{} : Bool}
  {Pr.judge(1n+u, cap, Some{Pr.Prior{1n+u, w}}, work) == Pr.Stop{1n+u} : Pr.Goal}

# ---- core_w6 ----

# LAWS: the entries of the compiled Bend core for the child task, the jobs,
# the goal's progress check and the hand-back (bend/ffi_child.bend,
# bend/ffi_job.bend, bend/ffi_progress.bend, bend/ffi_sandbox.bend). Each
# entry, on the request Rust writes (`put_req`, every number within the
# wire), answers the encoding of the model's decision: the codec loses,
# invents and reorders nothing, and the Rust rule is the proven model.

def wire_prior_fits(p: Maybe<&2, Pr.Prior>) -> Bool:
  match p:
    case None{}:
      True{}
    case Some{x}:
      match x:
        case Pr.Prior{s, w}:
          Bool.and(LawsBase.wire_fits(s), LawsBase.wire_fits(w))

# LAW: the progress entry answers the goal's check
law goal_entry:
  for +t: Nat
  for +cap: Nat
  for +p: Maybe<&2, Pr.Prior>
  for +work: Nat
  for ht: {LawsBase.wire_fits(t) == True{} : Bool}
  for hc: {LawsBase.wire_fits(cap) == True{} : Bool}
  for hp: {wire_prior_fits(p) == True{} : Bool}
  for hw: {LawsBase.wire_fits(work) == True{} : Bool}
  {FPr.ffi(FPr.put_req(t, cap, p, work)) == FPr.put_goal(Pr.judge(t, cap, p, work), "") : String}
