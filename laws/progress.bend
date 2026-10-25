# eukhe: the laws of area progress

import Base
import ../bend/child.bend as Ch
import ../bend/ffi_progress.bend as FPr
import ../bend/wire.bend as Wr
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

# LAW child_repeat_is_no_work: acts the session did before add no work: a child that repeats the
# same calls with the same results keeps its token
law child_repeat_is_no_work:
  for +seen: List<&2, Nat>
  for +loop: List<&2, Nat>
  for within: Pr.Within(loop, seen)
  {Pr.work(List.append(&2, Nat, seen, loop)) == Pr.work(seen) : Nat}

# LAW child_loop_is_a_stall: a child that loops is a stall: polls of a child whose acts since
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

# LAW child_new_work_is_progress: new work is progress: a poll after an act the child never did
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

# LAW goal_stops_without_progress: continuations in a row whose acts are all acts the session did
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

# LAW goal_stopped_exact: a verdict is stopped exactly when it is Stop, whatever its count
# EXCLUDES: a constant Goal.stopped (goal_stops_without_progress would then
#   say nothing about the goal loop)
law goal_stopped_exact:
  for +s: Nat
  {[Pr.Goal.stopped(Pr.Go{s}), Pr.Goal.stopped(Pr.Stop{s})] == [False{}, True{}] : List<&2, Bool>}

# LAW goal_progress_continues: a continuation with an act the session never did before clears
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

# LAW goal_first_check_starts: the first check of a run or a goal starts the count
law goal_first_check_starts:
  for +t: Nat
  for +cap: Nat
  for +work: Nat
  {Pr.judge(t, cap, None{}, work) == Pr.Go{0n} : Pr.Goal}

# LAW goal_judge_is_check: below t, a later check is the progress check on whether the
# work's count grew
law goal_judge_is_check:
  for +t: Nat
  for +cap: Nat
  for +s: Nat
  for +w: Nat
  for +work: Nat
  for below: {Nat.is_lt(s, t) == True{} : Bool}
  {Pr.judge(t, cap, Some{Pr.Prior{s, w}}, work) == Pr.check(cap, s, Nat.is_lt(w, work)) : Pr.Goal}

# LAW goal_judge_counts_work: the count grew exactly when the session did new work, so the goal
# laws above hold for the counts the Rust loop compares
law goal_judge_counts_work:
  for +hist: List<&2, Nat>
  for +seg: List<&2, Nat>
  {Nat.is_lt(Pr.work(hist), Pr.work(List.append(&2, Nat, hist, seg))) == Pr.grew(hist, seg) : Bool}

# LAW goal_judge_held: the count of stalls stays within t
# EXCLUDES: a count past the compiled core's Nat range (the process stops)
law goal_judge_held:
  for +u: Nat
  for +cap: Nat
  for p: Maybe<&2, Pr.Prior>
  for +work: Nat
  {Nat.is_le(Pr.Goal.stalls(Pr.judge(1n+u, cap, p, work)), 1n+u) == True{} : Bool}

# LAW goal_judge_top_stops: a count at t stops a goal with a cap within t that did no new work
# EXCLUDES: a held count that never reaches the cap
law goal_judge_top_stops:
  for +u: Nat
  for +cap: Nat
  for +w: Nat
  for +work: Nat
  for fits: {Nat.is_le(cap, 1n+u) == True{} : Bool}
  for same: {Nat.is_lt(w, work) == False{} : Bool}
  {Pr.judge(1n+u, cap, Some{Pr.Prior{1n+u, w}}, work) == Pr.Stop{1n+u} : Pr.Goal}

# the stalls the check counts on from: s, held below t (t - 1 when s
# reaches t; 0 when t is 0)
def gj_pred(t: Nat) -> Nat:
  match t:
    case 0n:
      0n
    case 1n+u:
      u

def gj_held.at(below: Bool, s: Nat, +t: Nat) -> Nat:
  match below:
    case True{}:
      s
    case False{}:
      gj_pred(t)

def gj_held(+t: Nat, +s: Nat) -> Nat:
  gj_held.at(Nat.is_lt(s, t), s, t)

# one more continuation with no new work after n of them: the goal stops
# when the count reaches the cap
def gj_stall.at(stop: Bool, n: Nat) -> Pr.Goal:
  match stop:
    case True{}:
      Pr.Stop{n}
    case False{}:
      Pr.Go{n}

def gj_stall(+cap: Nat, +n: Nat) -> Pr.Goal:
  gj_stall.at(Nat.is_le(cap, 1n+n), 1n+n)

def gj_grew(grew: Bool, +cap: Nat, +n: Nat) -> Pr.Goal:
  match grew:
    case True{}:
      Pr.Go{0n}
    case False{}:
      gj_stall(cap, n)

# the goal's check: the first one starts the count; a later one clears it
# when the work grew, else counts one more stall on the prior's (held below
# t) and stops at the cap
def gj_spec(+t: Nat, +cap: Nat, p: Maybe<&2, Pr.Prior>, +work: Nat) -> Pr.Goal:
  match p:
    case None{}:
      Pr.Go{0n}
    case Some{x}:
      match x:
        case Pr.Prior{+s, w}:
          gj_grew(Nat.is_lt(w, work), cap, gj_held(t, s))

# LAW goal_judge_exact: the check is exactly the goal's check: the first one starts the
# count; a later one goes on with no stalls when the work's count grew,
# else with one more stall than the prior's (held below t), and stops
# when that count reaches the cap
# EXCLUDES: a goal stopped before the cap (or after it), a count that
#   grows by more or less than one, a stall count kept or cleared on the
#   wrong side, a prior past t read as another count
law goal_judge_exact:
  for +t: Nat
  for +cap: Nat
  for +p: Maybe<&2, Pr.Prior>
  for +work: Nat
  {Pr.judge(t, cap, p, work) == gj_spec(t, cap, p, work) : Pr.Goal}

# x occurs in xs
def wd_in(+x: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(Nat.is_eq(h, x), wd_in(x, t))

def wd_one(old: Bool) -> Nat:
  match old:
    case True{}:
      0n
    case False{}:
      1n

# the acts of xs that did not occur before them (before: the acts read
# earlier, in reading order)
def wd_new(xs: List<&2, Nat>, +before: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case +h <> t:
      Nat.add(wd_one(wd_in(h, before)), wd_new(t, List.append(&2, Nat, before, [h])))

# LAW work_counts_distinct: the work of a session is the number of its distinct acts: each
# act counts once, at its first occurrence
# EXCLUDES: a work that starts above 0, grows by more than one for a new
#   act, counts a repeat, or scales or caps the count (the progress laws
#   above only say a repeat adds nothing and a new act adds something)
law work_counts_distinct:
  for +xs: List<&2, Nat>
  {Pr.work(xs) == wd_new(xs, Nil{}) : Nat}

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

# LAW goal_entry: the progress entry answers the goal's check
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

# ---- the goal's check: spelled requests (bend/ffi_progress.bend, id 15) ----
#
# LAWS: the check Rust asks at each goal continuation
# (crates/eukhe-core/src/durable/goals/state.rs `stall_check`), on requests
# spelled from the primitives of bend/wire.bend (not the entry's own
# encoders), read by the laws' own reader; and the check after the prior
# the goal loop compares with (bend/ffi_work.bend `ffi`, laws/work.bend).
#
# G1: the check answers, on every request Rust spells whose numbers fit the
#     wire, the spelling of `judge`; any other input answers exactly the
#     error form "progress: malformed request".
# G2: the check compares with the last check only when that one was of the
#     same run and the same goal (`compared`); else it starts the count.

# a request of the check: the bound of the count, the cap, the prior check,
# the work now
type gs.Req is Data:
  gs.Req{t: Nat, cap: Nat, p: Maybe<&2, Pr.Prior>, work: Nat}

def gs_spell_prior(p: Maybe<&2, Pr.Prior>, rest: String) -> String:
  match p:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      match x:
        case Pr.Prior{s, w}:
          Wr.put_nat(1n, Wr.put_nat(s, Wr.put_nat(w, rest)))

# the request Rust writes (goals/state.rs `judge`)
def gs_spell_req(q: gs.Req) -> String:
  match q:
    case gs.Req{t, cap, p, work}:
      Wr.put_nat(t, Wr.put_nat(cap, gs_spell_prior(p, Wr.put_nat(work, ""))))

def gs_spell_goal(g: Pr.Goal) -> String:
  match g:
    case Pr.Go{s}:
      Wr.put_nat(0n, Wr.put_nat(s, ""))
    case Pr.Stop{s}:
      Wr.put_nat(1n, Wr.put_nat(s, ""))

# the reply Rust reads: the check's verdict
def gs_answer(q: gs.Req) -> String:
  match q:
    case gs.Req{t, cap, p, work}:
      gs_spell_goal(Pr.judge(t, cap, p, work))

# every number of q fits the wire
def gs_fits(q: gs.Req) -> Bool:
  match q:
    case gs.Req{t, cap, p, work}:
      Bool.and(LawsBase.wire_fits(t), Bool.and(LawsBase.wire_fits(cap), Bool.and(wire_prior_fits(p), LawsBase.wire_fits(work))))

def gs_read_prior.w(+s: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Pr.Prior>>:
  match r:
    case Wr.Got{w, rest}:
      Wr.Got{Some{Pr.Prior{s, w}}, rest}
    case Wr.Bad{}:
      Wr.Bad{}

def gs_read_prior.s(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Pr.Prior>>:
  match r:
    case Wr.Got{+s, rest}:
      gs_read_prior.w(s, Wr.get_nat(rest))
    case Wr.Bad{}:
      Wr.Bad{}

def gs_read_prior.tag(n: Nat, s: String) -> Wr.Dec<Maybe<&2, Pr.Prior>>:
  match n:
    case 0n:
      Wr.Got{None{}, s}
    case 1n:
      gs_read_prior.s(Wr.get_nat(s))
    case 2n+q:
      Wr.Bad{}

def gs_read_prior.go(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Pr.Prior>>:
  match r:
    case Wr.Got{n, s}:
      gs_read_prior.tag(n, s)
    case Wr.Bad{}:
      Wr.Bad{}

def gs_read.end(whole: Bool, q: gs.Req) -> Maybe<&2, gs.Req>:
  match whole:
    case True{}:
      Some{q}
    case False{}:
      None{}

def gs_read.work(+t: Nat, +cap: Nat, p: Maybe<&2, Pr.Prior>, r: Wr.Dec<Nat>) -> Maybe<&2, gs.Req>:
  match r:
    case Wr.Got{work, s}:
      gs_read.end(Wr.end(s), gs.Req{t, cap, p, work})
    case Wr.Bad{}:
      None{}

def gs_read.prior(+t: Nat, +cap: Nat, r: Wr.Dec<Maybe<&2, Pr.Prior>>) -> Maybe<&2, gs.Req>:
  match r:
    case Wr.Got{p, s}:
      gs_read.work(t, cap, p, Wr.get_nat(s))
    case Wr.Bad{}:
      None{}

def gs_read.cap(+t: Nat, r: Wr.Dec<Nat>) -> Maybe<&2, gs.Req>:
  match r:
    case Wr.Got{+cap, s}:
      gs_read.prior(t, cap, gs_read_prior.go(Wr.get_nat(s)))
    case Wr.Bad{}:
      None{}

def gs_read.t(r: Wr.Dec<Nat>) -> Maybe<&2, gs.Req>:
  match r:
    case Wr.Got{+t, s}:
      gs_read.cap(t, Wr.get_nat(s))
    case Wr.Bad{}:
      None{}

# the request s is, when s is exactly one request
def gs_read(s: String) -> Maybe<&2, gs.Req>:
  gs_read.t(Wr.get_nat(s))

def gc_same(b: Bool, +t: Nat, +cap: Nat, +s: Nat, +w: Nat, +work: Nat) -> Pr.Goal:
  match b:
    case True{}:
      Pr.judge(t, cap, Some{Pr.Prior{s, w}}, work)
    case False{}:
      Pr.Go{0n}

# the goal's check after the last check m: the check against m's stalls
# and work when m was of the same run and the same goal (G2), else a check
# that starts the count
def gc_spec(+t: Nat, +cap: Nat, m: Maybe<&2, Pr.Last>, +work: Nat) -> Pr.Goal:
  match m:
    case None{}:
      Pr.Go{0n}
    case Some{x}:
      match x:
        case Pr.Last{r, g, s, w}:
          gc_same(Bool.and(r, g), t, cap, s, w, work)

# LAW goal_entry_answers (G1): on every request Rust spells whose numbers fit the wire, the
# check answers the spelling of the model's verdict
# EXCLUDES: a codec that loses, reorders or misreads the bound, the cap,
#   the prior or the work, or answers in another spelling
law goal_entry_answers:
  for +q: gs.Req
  for h: {gs_fits(q) == True{} : Bool}
  {FPr.ffi(gs_spell_req(q)) == gs_answer(q) : String}

# LAW goal_entry_malformed_exact (G1): every input that is not exactly one request (the
# laws' reader) answers exactly the error form 'E ' then "progress:
# malformed request"
# EXCLUDES: a default verdict for malformed input, a guessed field, an
#   unknown tag read as a known one, input left over ignored, another error
#   text
law goal_entry_malformed_exact:
  for +s: String
  for no: {gs_read(s) == None{} : Maybe<&2, gs.Req>}
  {FPr.ffi(s) == SCon{'E', SCon{' ', "progress: malformed request"}} : String}

# LAW goal_entry_example (G1): anchor: the requests Rust sends (with a bound of 100: Rust
# sends 10^14 - 1, which the proven kernel cannot unfold; below the bound the answer does
# not depend on it, goal_judge_exact): a first
# check; a later one with no new work at the cap; one with new work; an
# unknown prior tag; input left over
# EXCLUDES: another spelling of the requests or the replies Rust reads
law goal_entry_example:
  {[FPr.ffi("100,3,0,5,"), FPr.ffi("100,3,1,2,5,5,"), FPr.ffi("100,3,1,2,5,6,"), FPr.ffi("100,3,2,5,"), FPr.ffi("100,3,0,5,x")] == ["0,0,", "1,3,", "0,0,", Wr.err("progress: malformed request"), Wr.err("progress: malformed request")] : List<&2, String>}

# LAW goal_req_fits_example: witness: requests that fit the wire exist, with and without a
# prior (goal_entry_answers is not vacuous)
law goal_req_fits_example:
  {[gs_fits(gs.Req{5n, 3n, None{}, 5n}), gs_fits(gs.Req{5n, 3n, Some{Pr.Prior{2n, 5n}}, 5n})] == [True{}, True{}] : List<&2, Bool>}

# LAW goal_compared_check (G2): the prior the work entry's call answers (`compared`), then
# the check, is the goal's check: against the last check's stalls and work
# when it was of the same run and the same goal, else a check that starts
# the count; with goal_judge_is_check, below the bound that is the
# progress check on whether the work's count grew
# EXCLUDES: a check that compares with another run's or goal's work, or
#   restarts the count of the same run and goal
law goal_compared_check:
  for +t: Nat
  for +cap: Nat
  for +m: Maybe<&2, Pr.Last>
  for +work: Nat
  {Pr.judge(t, cap, Pr.compared(m), work) == gc_spec(t, cap, m, work) : Pr.Goal}
