# eukhe: the laws of area supervise
#
# The restart budget (bend/supervise.bend `decide`; Rust
# `restart_budget::decide` asks the entry bend/ffi_supervise.bend once per
# worker failure, with the ages it kept and the gap since the last failure)
# A1  A failure g ms after the last one ages every earlier failure by g
#     ms. The new ages are this failure at age 0, then every earlier age
#     still inside the window of w ms once aged (g + age < w), in their
#     order; the failures the budget counts are exactly these ages. The
#     count the caller holds never changes the decision (Rust sends none).
#     Laws: restart_window_empty, restart_window_inside,
#     restart_window_outside and restart_window_append (together they fix
#     the new ages of every history), restart_counts_ages,
#     restart_decide_ignores_count.
# A2  The verdict on a failure with n failures counted: past k failures
#     the worker is given up; else it relaunches after base * 2^min(n - 1,
#     7) ms, at most max ms. Law: restart_decide_verdict.
# A3  Over a run of failures (gaps oldest first, from no failure) the
#     failures counted at the last one are it and every earlier failure
#     whose distance to it (the sum of the gaps after that failure) is under
#     the window. Law: restart_failures_recent.
# A4  (D1) A crash loop is given up: a failure followed by k more, all
#     within a span under the window, gives the worker up, whatever came
#     before. Laws: restart_gives_up, restart_span_exact (the span is the
#     sum of the gaps).
# R1  Every request Rust writes (`restart_budget::decide_call`: the four
#     configuration Nats, the ages' count then each age, the gap; every
#     number within the wire) gets the model's decision (Su.decide, which
#     the laws for A1 and A2 pin) spelled as Rust reads it: the new ages'
#     count then each age, then the verdict's tag (Relaunch 0 with its
#     failure count and pause, GiveUp 1 with its failure count). Law:
#     restart_ffi_answers_spelled.
# R2  Any other input answers exactly the error form: "supervise: input
#     left over" when a whole request is followed by more input, else
#     "supervise: malformed request". Laws: restart_ffi_left_over_spelled,
#     restart_ffi_malformed_unless_request.

import Base
import ../bend/ffi_supervise.bend as FS
import ../bend/supervise.bend as Su
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# ---- supervisor ----

# (D1) Supervisor
# ---------------
# The supervisor, its workers, a lost supervisor, a daemon replacement,
# the attaches after a restart. The models are
# bend/supervise.bend (the restart budget and the timeouts),
# bend/revive.bend (busy evidence and the revival veto), bend/orphan.bend
# (a lost supervisor's worker), bend/launcher.bend (the idle shutdown and
# adoption), bend/replace.bend (the launcher's replacement verdict) and
# bend/notice.bend (the kernel restore notices a view shows); the restart
# budget, the timeouts
# (laws/timeouts.bend), the revival veto (laws/revive.bend), the orphan
# exit and the replacement verdict run as their models (the compiled
# core). Every input is free: any configuration, any
# gaps between failures, any run length, any events and operations in any
# order, any builds.

# LAW restart_gives_up: a crash loop is given up. After any earlier failures, a failure
# followed by k more failures, all inside the window, gives the worker up
law restart_gives_up:
  for +c: Su.Cfg
  for +pre: List<&2, Nat>
  for +g: Nat
  for +gs: List<&2, Nat>
  for many: {List.length(&2, Nat, gs) == Su.Cfg.k(c) : Nat}
  for fast: {Nat.is_lt(Su.span(gs), Su.Cfg.w(c)) == True{} : Bool}
  {Su.gives_up(Su.verdict(c, Su.failures(c, List.append(&2, Nat, pre, g <> gs)))) == True{} : Bool}

# The window (A1)
# ---------------

# the new ages after a failure g ms after the last one, from the ages a
# (the state as the entry builds it: the ages and their count)
def restart_new_ages(+c: Su.Cfg, +a: List<&2, Nat>, +g: Nat) -> List<&2, Nat>:
  Su.St.ages(Su.Decision.st(Su.decide(c, Su.St{a, List.length(&2, Nat, a)}, g)))

# LAW restart_window_empty: a failure with no earlier failure in the window keeps only
# itself, at age 0
# EXCLUDES: a new failure not recorded, recorded at another age, or twice
law restart_window_empty:
  for +c: Su.Cfg
  for +g: Nat
  {restart_new_ages(c, Nil{}, g) == [0n] : List<&2, Nat>}

# LAW restart_window_inside: an earlier failure of age a that is still inside the window g ms
# later (g + a < w) is kept, g ms older, behind the new failure at age 0
# EXCLUDES: a young failure dropped, an age that does not grow by the gap,
#   the new failure behind the old one
law restart_window_inside:
  for +c: Su.Cfg
  for +a: Nat
  for +g: Nat
  for inside: {Nat.is_lt(Nat.add(g, a), Su.Cfg.w(c)) == True{} : Bool}
  {restart_new_ages(c, [a], g) == [0n, Nat.add(g, a)] : List<&2, Nat>}

# LAW restart_window_outside: an earlier failure that reaches the window g ms later
# (g + a >= w) is forgotten: only the new failure stays
# EXCLUDES: an old failure kept (a crash rare enough counted forever), a
#   failure exactly at the window's edge kept
law restart_window_outside:
  for +c: Su.Cfg
  for +a: Nat
  for +g: Nat
  for outside: {Nat.is_lt(Nat.add(g, a), Su.Cfg.w(c)) == False{} : Bool}
  {restart_new_ages(c, [a], g) == [0n] : List<&2, Nat>}

# LAW restart_window_append: each earlier age is kept or dropped on its own, in place: the
# ages kept from xs ++ ys are those kept from xs, then those kept from ys
# (with the three laws above this fixes the new ages of every history)
# EXCLUDES: a reordered history, a cap on the ages kept, a decision on one
#   age that depends on the others
law restart_window_append:
  for +c: Su.Cfg
  for +xs: List<&2, Nat>
  for +ys: List<&2, Nat>
  for +g: Nat
  for +p: List<&2, Nat>
  for +q: List<&2, Nat>
  for hp: {restart_new_ages(c, xs, g) == 0n <> p : List<&2, Nat>}
  for hq: {restart_new_ages(c, ys, g) == 0n <> q : List<&2, Nat>}
  {restart_new_ages(c, List.append(&2, Nat, xs, ys), g) == 0n <> List.append(&2, Nat, p, q) : List<&2, Nat>}

# LAW restart_counts_ages: the failures the budget counts after a failure are exactly the
# ages it keeps, from any state
# EXCLUDES: a count that drifts from the ages (a failure counted twice or
#   not at all, a stale count carried over)
law restart_counts_ages:
  for +c: Su.Cfg
  for +s: Su.St
  for +g: Nat
  {Su.St.n(Su.Decision.st(Su.decide(c, s, g))) == List.length(&2, Nat, Su.St.ages(Su.Decision.st(Su.decide(c, s, g)))) : Nat}

# LAW restart_decide_ignores_count: the decision depends on the ages only: the count the
# caller holds (Rust sends none; the entry passes the ages' length) never
# changes it
# EXCLUDES: a decision that reads a stale count instead of the ages
law restart_decide_ignores_count:
  for +c: Su.Cfg
  for +a: List<&2, Nat>
  for +n: Nat
  for +m: Nat
  for +g: Nat
  {Su.decide(c, Su.St{a, n}, g) == Su.decide(c, Su.St{a, m}, g) : Su.Decision}

# The verdict (A2)
# ----------------

# 2 to the e
def restart_pow2(e: Nat) -> Nat:
  match e:
    case 0n:
      1n
    case 1n+p:
      Nat.mul(2n, restart_pow2(p))

# the verdict on the n-th failure in the window: past k failures the
# worker is given up; else it relaunches after base * 2^min(n - 1, 7) ms,
# at most max ms
def restart_verdict_put(over: Bool, +c: Su.Cfg, +n: Nat) -> Su.Verdict:
  match over:
    case True{}:
      Su.GiveUp{n}
    case False{}:
      match c:
        case Su.Cfg{k, w, b, m}:
          Su.Relaunch{n, Nat.min(Nat.mul(restart_pow2(Nat.min(Nat.sub(n, 1n), 7n)), b), m)}

# LAW restart_decide_verdict: the verdict on a failure, from the failures the decided
# budget counts (n): give up past k failures, else relaunch after
# base * 2^min(n - 1, 7) ms, at most max ms
# EXCLUDES: a give-up at k failures or a relaunch past them, a verdict on
#   another count than the budget's, a pause that does not double, passes
#   its cap or doubles past 7 times
law restart_decide_verdict:
  for +c: Su.Cfg
  for +s: Su.St
  for +g: Nat
  {Su.Decision.verdict(Su.decide(c, s, g)) == restart_verdict_put(Nat.is_lt(Su.Cfg.k(c), Su.St.n(Su.Decision.st(Su.decide(c, s, g)))), c, Su.St.n(Su.Decision.st(Su.decide(c, s, g)))) : Su.Verdict}

# A run of failures (A3, A4)
# --------------------------

# the time the gaps gs span: their sum
def restart_sum(gs: List<&2, Nat>) -> Nat:
  match gs:
    case Nil{}:
      0n
    case g <> rest:
      Nat.add(g, restart_sum(rest))

def restart_inside.put(b: Bool, r: Nat) -> Nat:
  match b:
    case True{}:
      1n+r
    case False{}:
      r

# the earlier failures still inside the window w at the last failure, for
# the gaps gs after the first of them: a failure followed by the gaps
# g <> rest is g + sum(rest) ms before the last one
def restart_inside(+w: Nat, gs: List<&2, Nat>) -> Nat:
  match gs:
    case Nil{}:
      0n
    case +g <> +rest:
      restart_inside.put(Nat.is_lt(restart_sum(g <> rest), w), restart_inside(w, rest))

# the failures counted at the last failure of the gaps gs (oldest first):
# none for no failure, else the last one and the earlier ones inside the
# window
def restart_recent(+w: Nat, gs: List<&2, Nat>) -> Nat:
  match gs:
    case Nil{}:
      0n
    case g <> rest:
      1n+restart_inside(w, rest)

# LAW restart_failures_recent: over any run of failures from no failure, the failures counted
# at the last one are it and each earlier failure whose distance to it (the
# sum of the gaps after that failure) is under the window
# EXCLUDES: an old failure never forgotten (failures = length), a failure
#   forgotten while still inside the window, a failure that leaves the
#   window and comes back, a count off by one
law restart_failures_recent:
  for +c: Su.Cfg
  for +gs: List<&2, Nat>
  {Su.failures(c, gs) == restart_recent(Su.Cfg.w(c), gs) : Nat}

# LAW restart_span_exact: the time a run of failures spans is the sum of its gaps
# EXCLUDES: a span that drops, doubles or caps a gap, a span past every
#   window (restart_gives_up's premise `fast` then never holds)
law restart_span_exact:
  for +gs: List<&2, Nat>
  {Su.span(gs) == restart_sum(gs) : Nat}

# The restart-budget entry of the compiled core (bend/ffi_supervise.bend)
# -----------------------------------------------------------------------

# LAW restart_wire_req: the entry's request decoder reads back what the entry's own request
# encoder writes (a configuration, ages and a gap whose numbers fit the
# wire), the rest untouched. That the entry reads the bytes Rust writes is
# restart_ffi_answers_spelled (spelled from the wire primitives)
# EXCLUDES: a configuration field, age or gap that the entry's encoder and
#   decoder disagree on
law restart_wire_req:
  for +k: Nat
  for hk: {LawsBase.wire_fits(k) == True{} : Bool}
  for +w: Nat
  for hw: {LawsBase.wire_fits(w) == True{} : Bool}
  for +b: Nat
  for hb: {LawsBase.wire_fits(b) == True{} : Bool}
  for +m: Nat
  for hm: {LawsBase.wire_fits(m) == True{} : Bool}
  for +ages: List<&2, Nat>
  for hs: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ages)), LawsBase.wire_nats_fit(ages)) == True{} : Bool}
  for +g: Nat
  for hg: {LawsBase.wire_fits(g) == True{} : Bool}
  for rest: String
  {FS.get_req(FS.put_req(FS.Req{Su.Cfg{k, w, b, m}, ages, g}, rest)) == Wr.Got{FS.Req{Su.Cfg{k, w, b, m}, ages, g}, rest} : Wr.Dec<FS.Req>}

# LAW restart_wire_reply_relaunch: the Bend reply decoder (FS.get_reply) reads back every
# relaunch reply the entry writes. Rust parses replies with its own reader
# (restart_budget.rs decide_call); the bytes it reads are pinned by
# restart_ffi_answers_spelled
# EXCLUDES: a relaunch reply that loses an age, the failure count or the
#   pause, or reads back as a give-up
law restart_wire_reply_relaunch:
  for +ages: List<&2, Nat>
  for hs: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ages)), LawsBase.wire_nats_fit(ages)) == True{} : Bool}
  for +f: Nat
  for hf: {LawsBase.wire_fits(f) == True{} : Bool}
  for +p: Nat
  for hp: {LawsBase.wire_fits(p) == True{} : Bool}
  for rest: String
  {FS.get_reply(FS.put_reply(FS.Reply{ages, Su.Relaunch{f, p}}, rest)) == Wr.Got{FS.Reply{ages, Su.Relaunch{f, p}}, rest} : Wr.Dec<FS.Reply>}

# LAW restart_wire_reply_give_up: the Bend reply decoder reads back every give-up reply the
# entry writes (Rust's own reader: see restart_wire_reply_relaunch)
# EXCLUDES: a give-up reply that reads back as a relaunch or loses its
#   failure count
law restart_wire_reply_give_up:
  for +ages: List<&2, Nat>
  for hs: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ages)), LawsBase.wire_nats_fit(ages)) == True{} : Bool}
  for +f: Nat
  for hf: {LawsBase.wire_fits(f) == True{} : Bool}
  for rest: String
  {FS.get_reply(FS.put_reply(FS.Reply{ages, Su.GiveUp{f}}, rest)) == Wr.Got{FS.Reply{ages, Su.GiveUp{f}}, rest} : Wr.Dec<FS.Reply>}

# The restart-budget entry, spelled (R1, R2)
# ------------------------------------------
# The spellers below are built from the wire primitives of bend/wire.bend
# only, never from the entry's put_*/get_*.

# the configuration: give up after k, the window w, the base pause b, the
# longest pause m
def rs_spell_cfg(c: Su.Cfg, rest: String) -> String:
  match c:
    case Su.Cfg{k, w, b, m}:
      Wr.put_nat(k, Wr.put_nat(w, Wr.put_nat(b, Wr.put_nat(m, rest))))

# the request q as Rust writes it, then rest: the configuration, the ages
# (their count, then each), the gap
def rs_spell_req(q: FS.Req, rest: String) -> String:
  match q:
    case FS.Req{c, a, g}:
      rs_spell_cfg(c, LawsBase.wire_spell_nats(a, Wr.put_nat(g, rest)))

def rs_cfg_fits(c: Su.Cfg) -> Bool:
  match c:
    case Su.Cfg{k, w, b, m}:
      Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(w), Bool.and(LawsBase.wire_fits(b), LawsBase.wire_fits(m))))

# every number of a request fits the wire
def rs_req_fits(q: FS.Req) -> Bool:
  match q:
    case FS.Req{c, +a, g}:
      Bool.and(rs_cfg_fits(c), Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, a)), LawsBase.wire_nats_fit(a)), LawsBase.wire_fits(g)))

# a verdict: Relaunch 0 (failure count, pause), GiveUp 1 (failure count)
def rs_spell_verdict(v: Su.Verdict, rest: String) -> String:
  match v:
    case Su.Relaunch{f, b}:
      Wr.put_nat(0n, Wr.put_nat(f, Wr.put_nat(b, rest)))
    case Su.GiveUp{f}:
      Wr.put_nat(1n, Wr.put_nat(f, rest))

# a decision as Rust reads it: the new ages (count, then each), the verdict
def rs_spell_decision(d: Su.Decision) -> String:
  match d:
    case Su.Decision{s, v}:
      LawsBase.wire_spell_nats(Su.St.ages(s), rs_spell_verdict(v, ""))

# the model's decision on q, spelled: the state is the ages and their count
def rs_spell_answer(q: FS.Req) -> String:
  match q:
    case FS.Req{c, +a, g}:
      rs_spell_decision(Su.decide(c, Su.St{a, List.length(&2, Nat, a)}, g))

def rs_malformed() -> String:
  Wr.err("supervise: malformed request")

def rs_left_over() -> String:
  Wr.err("supervise: input left over")

# LAW restart_ffi_answers_spelled: every request Rust writes (every number within the wire) gets the spelled model decision
# EXCLUDES: a request Rust writes refused or misread, a reply spelled
#   another way than Rust reads it
law restart_ffi_answers_spelled:
  for +q: FS.Req
  for fits: {rs_req_fits(q) == True{} : Bool}
  {FS.ffi(rs_spell_req(q, "")) == rs_spell_answer(q) : String}

# LAW restart_ffi_left_over_spelled: a request Rust writes followed by more input gets exactly "supervise: input left over"
# EXCLUDES: trailing bytes ignored or read as part of the request, the
#   malformed error for them
law restart_ffi_left_over_spelled:
  for +q: FS.Req
  for +more: String
  for fits: {rs_req_fits(q) == True{} : Bool}
  for some: {String.is_empty(more) == False{} : Bool}
  {FS.ffi(rs_spell_req(q, more)) == rs_left_over() : String}

# LAW restart_ffi_malformed_unless_request: every answer but the error form "supervise:
# malformed request" comes from an input that begins with a request Rust
# writes (spelled from the wire primitives, every number within the wire);
# with the two laws above this fixes the answer to every input
# EXCLUDES: a decoder that accepts a missing, extra or reordered field, a
#   list shorter than its count, or a number past the wire, and answers it
#   (a default decision or the left-over error instead of the malformed one)
law restart_ffi_malformed_unless_request:
  for +s: String
  for other: {String.eq(FS.ffi(s), rs_malformed()) == False{} : Bool}
  exs q: FS.Req
  exs rest: String
  {(s, rs_req_fits(q)) == (rs_spell_req(q, rest), True{}) : String & Bool}

# LAW restart_ffi_tags_example: anchor: the bytes Rust sends and reads: a failure 3 ms after two
# failures (ages 5 and 98) with give-up after 2 in a 100 ms window, base pause 10, cap 50: the old
# age 98 leaves the window, the second failure relaunches after 20 ms; the same with give-up after
# 1: given up at 2 failures; a third failure whose 40 ms pause is capped at 15; no input, a missing
# gap, a list shorter than its count, and left-over input
# EXCLUDES: another spelling of a request or a reply, a swapped verdict
#   tag, the error texts swapped
law restart_ffi_tags_example:
  {[FS.ffi("2,100,10,50,2,5,98,3,"), FS.ffi("1,100,10,50,2,5,98,3,"), FS.ffi("9,100,10,15,2,5,6,1,"), FS.ffi(""), FS.ffi("2,100,10,50,0,"), FS.ffi("2,100,10,50,2,5,3,"), FS.ffi("2,100,10,50,0,3,x")] == ["2,0,8,0,2,20,", "2,0,8,1,2,", "3,0,6,7,0,3,15,", "E supervise: malformed request", "E supervise: malformed request", "E supervise: malformed request", "E supervise: input left over"] : List<&2, String>}

# LAW restart_ffi_pause_example: anchor: the entry on hand-computed inputs (field order of
# restart_budget.rs decide_call): an age that leaves the window, a third
# failure that doubles the pause twice, the same failure given up with
# k = 2, a pause capped at max; a cut request and input left over are
# refused
# EXCLUDES: a pause that doubles once per failure counted from 0, a cap
#   applied before the doubling stops
law restart_ffi_pause_example:
  {[FS.ffi("3,10,2,9,1,4,6,"), FS.ffi("3,10,2,9,2,1,2,1,"), FS.ffi("2,10,2,9,2,1,2,1,"), FS.ffi("5,10,4,9,2,1,2,1,"), FS.ffi("3,10,2,9,1,"), FS.ffi("3,10,2,9,0,6,x")] == ["1,0,0,1,2,", "3,0,2,3,0,3,8,", "3,0,2,3,1,3,", "3,0,2,3,0,3,9,", Wr.err("supervise: malformed request"), Wr.err("supervise: input left over")] : List<&2, String>}
