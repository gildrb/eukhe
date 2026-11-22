# eukhe: the laws of area progress

import Base
import ../bend/child.bend as Ch
import ../bend/ffi_progress.bend as FPr
import ../bend/wire.bend as Wr
import ../bend/progress.bend as Pr
import ./base.bend as LawsBase

# ---- progress ----

# LAWS: when the harness checks a loop, progress is new work, and a loop of
# the same work stops in time. Each law is an open claim about the models in
# bend/progress.bend (and bend/child.bend for the subagent watch) or about
# the entry bend/ffi_progress.bend; PROOF.bend proves them (as
# Progress.<law>) with the lemmas of proof/progress/.
#
# Requirements (Rust: the autonomous run's stall check in eukhe-core
# (`autonomous.rs`); children/work.rs `WorkLedger`;
# crates/eukhe-daemon/src/worker/run_outcome.rs; regression test "a stall
# steers once then ends not done"):
#
# H6: an autonomous run whose continuations do no new work is steered
#     once, then ends: each continuation with no new work counts one stall
#     more, a continuation with new work clears the count; when the count
#     reaches the cap (directors.stallSteps) the harness steers the run (it
#     goes on with a continuation that asks for another approach), between
#     the cap and twice the cap it goes on, and at twice the cap (the cap
#     again with no new work since the steer) the run stops: it ends not
#     done, never waiting on a person (owner's decision: no state only a
#     user's resume can move); the first check of a run starts the count;
#     the count is held within the wire's bound t.
#       auto_stops_without_progress, auto_progress_continues,
#       auto_entry_first_check, auto_entry_new_work, auto_entry_stall_goes,
#       auto_entry_stall_steers, auto_entry_stall_stops, auto_judge_held,
#       auto_judge_exact
# H7: a subagent's (and an autonomous run's) progress is new work: the
#     work is the number of distinct acts; an act done before adds none, a
#     new act adds one; a child that loops stalls; new work refreshes its
#     clock.
#       work_counts_new_acts, child_repeat_is_no_work, auto_new_act_counts,
#       child_loop_is_a_stall, child_new_work_is_progress
# G1: the check answers, on every request Rust spells whose numbers fit the
#     wire, the spelling of its verdict; any other input answers exactly the
#     error form "progress: malformed request".
#       auto_entry, auto_entry_first_check, auto_entry_new_work,
#       auto_entry_stall_goes, auto_entry_stall_steers, auto_entry_stall_stops,
#       auto_entry_reads_only_requests, auto_entry_example
# G2: the check compares with the last check only when that one was of the
#     same run; else it starts the count. The work entry answers that prior
#     or none (laws/work.bend prior_entry_answers); a request with no prior
#     starts the count (auto_entry_first_check).
#       auto_compared_check
#
# M5 and L5, cited here before, are not this area's requirements (what the
# harness substitutes or fails to load reaches the user): M5 is stated in
# laws/aux_fallback/model.bend, L5 in laws/skill_load.bend.

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

# (H6) An autonomous run without progress is steered, then stops
# --------------------------------------------------------------
# At each continuation of an autonomous run the progress check asks
# whether the work grew since the last continuation (Pr.check, cap:
# directors.stallSteps).

# LAW auto_stops_without_progress (H6): continuations in a row whose acts are all acts the
# session did before, at least twice as many as the cap, stop the run (the
# verdict is Stop, with some count), whatever count of stalls it starts
# from: the steer at the cap does not keep it going forever
# EXCLUDES: a run loop that never stops on repeated work, or stops later
#   than twice the cap
law auto_stops_without_progress:
  for +cap: Nat
  for +s: Nat
  for +hist: List<&2, Nat>
  for +seg: List<&2, Nat>
  for +segs: List<&2, List<&2, Nat>>
  for repeats: Pr.Repeats(seg <> segs, hist)
  for long: {Nat.is_le(Nat.add(cap, cap), List.length(&2, List<&2, Nat>, seg <> segs)) == True{} : Bool}
  exs n: Nat
  {Pr.run(seg <> segs, cap, hist, Pr.Go{s}) == Pr.Stop{n} : Pr.Run}

# LAW auto_progress_continues: a continuation with an act the session never did before clears
# the count: the run goes on
law auto_progress_continues:
  for +cap: Nat
  for +s: Nat
  for +hist: List<&2, Nat>
  for +seg: List<&2, Nat>
  for +x: Nat
  for fresh: {Pr.mem(x, hist) == False{} : Bool}
  for news: Pr.In(x, seg)
  {Pr.check(cap, s, Pr.grew(hist, seg)) == Pr.Go{0n} : Pr.Run}

# LAW work_counts_new_acts (H7): a session with no act has no work, and an act the session
# never did before adds exactly one to its work (with child_repeat_is_no_work,
# an act it did before adds none: the work is the number of its distinct
# acts)
# EXCLUDES: a work that starts above 0, grows by more or less than one for
#   a new act, or scales or caps the count
law work_counts_new_acts:
  for +xs: List<&2, Nat>
  for +x: Nat
  for fresh: {Pr.mem(x, xs) == False{} : Bool}
  {Pr.work(Nil{}) == 0n : Nat} & {Pr.work(List.append(&2, Nat, xs, [x])) == 1n+Pr.work(xs) : Nat}

# LAW auto_new_act_counts (H6, H7): the counts the Rust run loop compares grow on new work:
# after acts with one the session never did before, the work's count is
# more than it was (with child_repeat_is_no_work: it stays when every act
# was done before)
# EXCLUDES: a count that misses new work, so the run loop counts a stall
#   for a continuation that did new work
law auto_new_act_counts:
  for +hist: List<&2, Nat>
  for +seg: List<&2, Nat>
  for +x: Nat
  for fresh: {Pr.mem(x, hist) == False{} : Bool}
  for news: Pr.In(x, seg)
  {Nat.is_lt(Pr.work(hist), Pr.work(List.append(&2, Nat, hist, seg))) == True{} : Bool}

# The check the Rust run loop runs (bend/progress.bend `judge`): it
# compares the ledger's counts, and holds the count of stalls within t
# (t = 10^14 - 1, the largest Nat the core's wire carries). Every law
# holds for every t.

# LAW auto_judge_held: the count of stalls stays within t
# EXCLUDES: a count past the compiled core's Nat range (the process stops)
law auto_judge_held:
  for +u: Nat
  for +cap: Nat
  for p: Maybe<&2, Pr.Prior>
  for +work: Nat
  {Nat.is_le(Pr.Run.stalls(Pr.judge(1n+u, cap, p, work)), 1n+u) == True{} : Bool}

# ---- core_w6 ----

# LAWS: the entries of the compiled Bend core for the child task, the jobs,
# the autonomous run's progress check and the hand-back
# (bend/ffi_child.bend, bend/ffi_job.bend, bend/ffi_progress.bend,
# bend/ffi_sandbox.bend). Each entry, on the request Rust writes
# (`put_req`, every number within the wire), answers the encoding of the
# model's decision: the codec loses, invents and reorders nothing, and the
# Rust rule is the proven model.

def wire_prior_fits(p: Maybe<&2, Pr.Prior>) -> Bool:
  match p:
    case None{}:
      True{}
    case Some{x}:
      match x:
        case Pr.Prior{s, w}:
          Bool.and(LawsBase.wire_fits(s), LawsBase.wire_fits(w))

# LAW auto_entry: the progress entry answers the run's check
law auto_entry:
  for +t: Nat
  for +cap: Nat
  for +p: Maybe<&2, Pr.Prior>
  for +work: Nat
  for ht: {LawsBase.wire_fits(t) == True{} : Bool}
  for hc: {LawsBase.wire_fits(cap) == True{} : Bool}
  for hp: {wire_prior_fits(p) == True{} : Bool}
  for hw: {LawsBase.wire_fits(work) == True{} : Bool}
  {FPr.ffi(FPr.put_req(t, cap, p, work)) == FPr.put_run(Pr.judge(t, cap, p, work), "") : String}

# ---- the run's check: spelled requests (bend/ffi_progress.bend, id 15) ----
#
# The request Rust writes at each continuation of an autonomous run (its
# stall check), spelled here from the grammar of crates/eukhe-bend/WIRE.md
# (a record is its fields in order; a Nat its decimal digits, then ','; a
# Maybe '0,' for None, '1,' then the value) with the wire primitives: the
# bound t, the cap, the prior check Maybe<{stalls, work}>, the work now.
# The reply Rust reads: a constructor of the verdict, tag 0 for Go, 1 for
# Stop and 2 for Steer (WIRE.md: a constructor is its index), then its
# count of stalls.

# a request of the check: the bound of the count, the cap, the prior check,
# the work now
type gs.Req is Data:
  gs.Req{t: Nat, cap: Nat, p: Maybe<&2, Pr.Prior>, work: Nat}

# a Maybe of the prior's two Nats, then rest
def gs_spell_prior(p: Maybe<&2, Pr.Prior>, rest: String) -> String:
  match p:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      match x:
        case Pr.Prior{s, w}:
          Wr.put_nat(1n, Wr.put_nat(s, Wr.put_nat(w, rest)))

# the whole request: t, cap, prior, work
def gs_spell_req(q: gs.Req) -> String:
  match q:
    case gs.Req{t, cap, p, work}:
      Wr.put_nat(t, Wr.put_nat(cap, gs_spell_prior(p, Wr.put_nat(work, ""))))

# the whole reply: the verdict's tag (0 Go, 1 Stop, 2 Steer), then its stalls
def gs_reply(tag: Nat, stalls: Nat) -> String:
  Wr.put_nat(tag, Wr.put_nat(stalls, ""))

# every number of q fits the wire
def gs_fits(q: gs.Req) -> Bool:
  match q:
    case gs.Req{t, cap, p, work}:
      Bool.and(LawsBase.wire_fits(t), Bool.and(LawsBase.wire_fits(cap), Bool.and(wire_prior_fits(p), LawsBase.wire_fits(work))))

# LAW auto_entry_first_check (H6, G1, G2): a request with no prior check (the first check of
# a run, or one after a check of another run) answers Go with no stall:
# the count starts, whatever the bound, the cap and the work
# EXCLUDES: a first check that stops or steers the run, or starts the
#   count above 0
law auto_entry_first_check:
  for +t: Nat
  for +cap: Nat
  for +work: Nat
  for h: {gs_fits(gs.Req{t, cap, None{}, work}) == True{} : Bool}
  {FPr.ffi(gs_spell_req(gs.Req{t, cap, None{}, work})) == gs_reply(0n, 0n) : String}

# LAW auto_entry_new_work (H6, G1): a request whose work's count is more than the prior
# check's answers Go with no stall: new work clears the count, whatever the
# prior's stalls, the bound and the cap
# EXCLUDES: a count kept, or a run steered or stopped, after a
#   continuation that did new work
law auto_entry_new_work:
  for +t: Nat
  for +cap: Nat
  for +s: Nat
  for +w: Nat
  for +work: Nat
  for h: {gs_fits(gs.Req{t, cap, Some{Pr.Prior{s, w}}, work}) == True{} : Bool}
  for grew: {Nat.is_lt(w, work) == True{} : Bool}
  {FPr.ffi(gs_spell_req(gs.Req{t, cap, Some{Pr.Prior{s, w}}, work})) == gs_reply(0n, 0n) : String}

# LAW auto_entry_stall_goes (H6, G1): a request whose work's count is not more than the
# prior check's, with the prior's stalls s below the bound t, 1 + s below
# twice the cap and not the cap, answers Go with 1 + s stalls: one more
# stall, and the run goes on (before the steer, and after it until twice
# the cap)
# EXCLUDES: a count that grows by more or less than one, a run stopped
#   before twice the cap, a steer at another count than the cap
law auto_entry_stall_goes:
  for +t: Nat
  for +cap: Nat
  for +s: Nat
  for +w: Nat
  for +work: Nat
  for h: {gs_fits(gs.Req{t, cap, Some{Pr.Prior{s, w}}, work}) == True{} : Bool}
  for same: {Nat.is_lt(w, work) == False{} : Bool}
  for below: {Nat.is_lt(s, t) == True{} : Bool}
  for under: {Nat.is_lt(1n+s, Nat.add(cap, cap)) == True{} : Bool}
  for other: {Nat.is_eq(cap, 1n+s) == False{} : Bool}
  {FPr.ffi(gs_spell_req(gs.Req{t, cap, Some{Pr.Prior{s, w}}, work})) == gs_reply(0n, 1n+s) : String}

# LAW auto_entry_stall_steers (H6, G1): a request whose work's count is not more than the
# prior check's, with the prior's stalls s below the bound t and 1 + s the
# cap, answers Steer with 1 + s stalls: the count reaching the cap steers
# the run (it goes on, asked for another approach), it never stops it
# EXCLUDES: a run stopped or paused at the cap, a cap reached with no
#   steer, a steer with another count
law auto_entry_stall_steers:
  for +t: Nat
  for +s: Nat
  for +w: Nat
  for +work: Nat
  for h: {gs_fits(gs.Req{t, 1n+s, Some{Pr.Prior{s, w}}, work}) == True{} : Bool}
  for same: {Nat.is_lt(w, work) == False{} : Bool}
  for below: {Nat.is_lt(s, t) == True{} : Bool}
  {FPr.ffi(gs_spell_req(gs.Req{t, 1n+s, Some{Pr.Prior{s, w}}, work})) == gs_reply(2n, 1n+s) : String}

# LAW auto_entry_stall_stops (H6, G1): a request whose work's count is not more than the
# prior check's, with the prior's stalls s below the bound t and 1 + s at
# least twice the cap, answers Stop with 1 + s stalls: the run stops at
# twice the cap (the cap again with no new work since the steer)
# EXCLUDES: a run that goes on past twice the cap, a stop with another
#   count
law auto_entry_stall_stops:
  for +t: Nat
  for +cap: Nat
  for +s: Nat
  for +w: Nat
  for +work: Nat
  for h: {gs_fits(gs.Req{t, cap, Some{Pr.Prior{s, w}}, work}) == True{} : Bool}
  for same: {Nat.is_lt(w, work) == False{} : Bool}
  for below: {Nat.is_lt(s, t) == True{} : Bool}
  for reached: {Nat.is_le(Nat.add(cap, cap), 1n+s) == True{} : Bool}
  {FPr.ffi(gs_spell_req(gs.Req{t, cap, Some{Pr.Prior{s, w}}, work})) == gs_reply(1n, 1n+s) : String}

# LAW auto_entry_reads_only_requests (G1): every answer other than exactly the error form
# 'E progress: malformed request' answers a request: the input is the
# spelling of a request whose numbers fit the wire (the laws above then pin
# the answer)
# EXCLUDES: a default verdict for malformed input, a guessed field, an
#   unknown prior tag read as a known one, input left over ignored, another
#   error text
law auto_entry_reads_only_requests:
  for +s: String
  for other: {String.eq(FPr.ffi(s), Wr.err("progress: malformed request")) == False{} : Bool}
  exs q: gs.Req
  {(s, gs_fits(q)) == (gs_spell_req(q), True{}) : String & Bool}

# LAW auto_entry_example (G1): anchor: the requests Rust sends (with a bound of 100: Rust
# sends 10^14 - 1, which the proven kernel cannot unfold; below the bound the answer does
# not depend on it: auto_entry_stall_goes, auto_entry_stall_steers,
# auto_entry_stall_stops): a first check; later ones with no new work at
# the cap, past it and at twice the cap; one with new work; an unknown
# prior tag; input left over
# EXCLUDES: another spelling of the requests or the replies Rust reads
law auto_entry_example:
  {[FPr.ffi("100,3,0,5,"), FPr.ffi("100,3,1,2,5,5,"), FPr.ffi("100,3,1,3,5,5,"), FPr.ffi("100,3,1,5,5,5,"), FPr.ffi("100,3,1,2,5,6,"), FPr.ffi("100,3,2,5,"), FPr.ffi("100,3,0,5,x")] == ["0,0,", "2,3,", "0,4,", "1,6,", "0,0,", Wr.err("progress: malformed request"), Wr.err("progress: malformed request")] : List<&2, String>}

# LAW auto_req_fits_example: witness: requests that fit the wire exist, with and without a
# prior (the auto_entry_* laws are not vacuous)
law auto_req_fits_example:
  {[gs_fits(gs.Req{5n, 3n, None{}, 5n}), gs_fits(gs.Req{5n, 3n, Some{Pr.Prior{2n, 5n}}, 5n})] == [True{}, True{}] : List<&2, Bool>}

# one more continuation with no new work after n of them: the run is
# steered when the count reaches the cap and stops when it reaches twice
# the cap
def gj_stall.go(steer: Bool, n: Nat) -> Pr.Run:
  match steer:
    case True{}:
      Pr.Steer{n}
    case False{}:
      Pr.Go{n}

def gj_stall.at(stop: Bool, steer: Bool, n: Nat) -> Pr.Run:
  match stop:
    case True{}:
      Pr.Stop{n}
    case False{}:
      gj_stall.go(steer, n)

def gj_stall(+cap: Nat, +n: Nat) -> Pr.Run:
  gj_stall.at(Nat.is_le(Nat.add(cap, cap), 1n+n), Nat.is_eq(cap, 1n+n), 1n+n)

def gj_grew(grew: Bool, +cap: Nat, +n: Nat) -> Pr.Run:
  match grew:
    case True{}:
      Pr.Go{0n}
    case False{}:
      gj_stall(cap, n)

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

# the run's check: the first one starts the count; a later one clears it
# when the work grew, else counts one more stall on the prior's (held below
# t), steers at the cap and stops at twice the cap
def gj_spec(+t: Nat, +cap: Nat, p: Maybe<&2, Pr.Prior>, +work: Nat) -> Pr.Run:
  match p:
    case None{}:
      Pr.Go{0n}
    case Some{x}:
      match x:
        case Pr.Prior{+s, w}:
          gj_grew(Nat.is_lt(w, work), cap, gj_held(t, s))

# LAW auto_judge_exact: the check is exactly the run's check: the first one starts the
# count; a later one goes on with no stalls when the work's count grew,
# else with one more stall than the prior's (held below t), steered when
# that count is the cap and stopped when it reaches twice the cap
# EXCLUDES: a run steered or stopped at another count, a count that
#   grows by more or less than one, a stall count kept or cleared on the
#   wrong side, a prior past t read as another count
law auto_judge_exact:
  for +t: Nat
  for +cap: Nat
  for +p: Maybe<&2, Pr.Prior>
  for +work: Nat
  {Pr.judge(t, cap, p, work) == gj_spec(t, cap, p, work) : Pr.Run}

def gc_same(b: Bool, +t: Nat, +cap: Nat, +s: Nat, +w: Nat, +work: Nat) -> Pr.Run:
  match b:
    case True{}:
      Pr.judge(t, cap, Some{Pr.Prior{s, w}}, work)
    case False{}:
      Pr.Go{0n}

# the run's check after the last check m: the check against m's stalls and
# work when m was of the same run (G2), else a check that starts the count
def gc_spec(+t: Nat, +cap: Nat, m: Maybe<&2, Pr.Last>, +work: Nat) -> Pr.Run:
  match m:
    case None{}:
      Pr.Go{0n}
    case Some{x}:
      match x:
        case Pr.Last{r, s, w}:
          gc_same(r, t, cap, s, w, work)

# LAW auto_compared_check (G2): the prior the work entry's call answers (`compared`), then
# the check, is the run's check: against the last check's stalls and work
# when it was of the same run, else a check that starts the count; with
# auto_judge_exact, below the bound that is the progress check on whether
# the work's count grew
# EXCLUDES: a check that compares with another run's work, or restarts
#   the count of the same run
law auto_compared_check:
  for +t: Nat
  for +cap: Nat
  for +m: Maybe<&2, Pr.Last>
  for +work: Nat
  {Pr.judge(t, cap, Pr.compared(m), work) == gc_spec(t, cap, m, work) : Pr.Run}
