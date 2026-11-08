# eukhe: the laws of area supervise

import Base
import ../bend/ffi_supervise.bend as FS
import ../bend/supervise.bend as Su
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# ---- supervisor ----

# (D1) Supervisor
# ---------------
# The supervisor, its workers, a lost supervisor, a its workers, a lost supervisor, a
# daemon replacement, the attaches after a restart. The models are
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

# the ages a failure g ms after the last one keeps (each g ms older), in
# order: those still inside the window of w ms
def restart_window_put(b: Bool, a: Nat, r: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      a <> r
    case False{}:
      r

def restart_window(+w: Nat, +g: Nat, ages: List<&2, Nat>) -> List<&2, Nat>:
  match ages:
    case Nil{}:
      Nil{}
    case +a <> t:
      restart_window_put(Nat.is_lt(Nat.add(g, a), w), Nat.add(g, a), restart_window(w, g, t))

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

# LAW restart_decide_window: a failure keeps exactly the ages still inside the window (each one
# g ms older, in order), adds itself at age 0 in front, and counts the
# failures it keeps
# EXCLUDES: a dropped young failure, a kept old one, a failure counted
# twice or not at all, a reordered history, an age that does not grow
law restart_decide_window:
  for +c: Su.Cfg
  for +s: Su.St
  for +g: Nat
  {Su.Decision.st(Su.decide(c, s, g)) == Su.St{0n <> restart_window(Su.Cfg.w(c), g, Su.St.ages(s)), 1n+List.length(&2, Nat, restart_window(Su.Cfg.w(c), g, Su.St.ages(s)))} : Su.St}

# LAW restart_decide_verdict: the verdict on a failure: give up past k failures in the window,
# else relaunch after the doubling pause, capped at max
# EXCLUDES: a give-up at k failures or a relaunch past them, a wrong
# failure count, a pause that does not double, passes its cap or doubles
# past 7 times
law restart_decide_verdict:
  for +c: Su.Cfg
  for +s: Su.St
  for +g: Nat
  {Su.Decision.verdict(Su.decide(c, s, g)) == restart_verdict_put(Nat.is_lt(Su.Cfg.k(c), 1n+List.length(&2, Nat, restart_window(Su.Cfg.w(c), g, Su.St.ages(s)))), c, 1n+List.length(&2, Nat, restart_window(Su.Cfg.w(c), g, Su.St.ages(s)))) : Su.Verdict}

# the budget after a failure g ms after the last one, from s: the failure
# at age 0, then the ages still inside the window (each g ms older), and
# the failures it keeps
def restart_step(+c: Su.Cfg, s: Su.St, +g: Nat) -> Su.St:
  match c:
    case Su.Cfg{k, +w, b, m}:
      match s:
        case Su.St{a, n}:
          +kept = restart_window(w, g, a)
          Su.St{0n <> kept, 1n+List.length(&2, Nat, kept)}

# the budget after the failures with the gaps gs (oldest first), from s:
# one step per failure, in order
def restart_go(+c: Su.Cfg, gs: List<&2, Nat>, s: Su.St) -> Su.St:
  match gs:
    case Nil{}:
      s
    case +g <> rest:
      restart_go(c, rest, restart_step(c, s, g))

# the failures a budget counts in the window at its last failure
def restart_count(s: Su.St) -> Nat:
  match s:
    case Su.St{a, n}:
      n

# the failures in the window at the last failure of gs, from no failure
def restart_failures(+c: Su.Cfg, gs: List<&2, Nat>) -> Nat:
  restart_count(restart_go(c, gs, Su.St{Nil{}, 0n}))

# the time the gaps gs span: their sum
def restart_sum(gs: List<&2, Nat>) -> Nat:
  match gs:
    case Nil{}:
      0n
    case g <> rest:
      Nat.add(g, restart_sum(rest))

# LAW restart_go_exact: the budget after any failures, from any budget, is the decided
# step (restart_decide_window) folded over their gaps in order
# EXCLUDES: a run that skips, repeats or reorders a failure, keeps a failure
#   that left the window, or forgets one still inside it
law restart_go_exact:
  for +c: Su.Cfg
  for +gs: List<&2, Nat>
  for +s: Su.St
  {Su.go(c, gs, s) == restart_go(c, gs, s) : Su.St}

# LAW restart_failures_exact: the failures counted at the last of any failures are exactly
# those still inside the window, from no failure
# EXCLUDES: failures(c, gs) = length(gs) (an old failure never forgotten:
#   restart_gives_up still holds), a count off by one, a count from
#   another start
law restart_failures_exact:
  for +c: Su.Cfg
  for +gs: List<&2, Nat>
  {Su.failures(c, gs) == restart_failures(c, gs) : Nat}

# LAW restart_span_exact: the time a run of failures spans is the sum of its gaps
# EXCLUDES: a span that drops, doubles or caps a gap, a span past every
#   window (restart_gives_up's premise `fast` then never holds)
law restart_span_exact:
  for +gs: List<&2, Nat>
  {Su.span(gs) == restart_sum(gs) : Nat}

# The restart-budget entry of the compiled core (bend/ffi_supervise.bend)

# LAW restart_wire_req: the entry reads back every request Rust writes: a configuration,
# ages and a gap that fit the wire; the rest is untouched
# EXCLUDES: a misread or reordered configuration field, age or gap
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

# LAW restart_wire_reply_relaunch: Rust reads back every relaunch reply the entry writes
# EXCLUDES: a misread age, failure count or pause, a verdict read as another
law restart_wire_reply_relaunch:
  for +ages: List<&2, Nat>
  for hs: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ages)), LawsBase.wire_nats_fit(ages)) == True{} : Bool}
  for +f: Nat
  for hf: {LawsBase.wire_fits(f) == True{} : Bool}
  for +p: Nat
  for hp: {LawsBase.wire_fits(p) == True{} : Bool}
  for rest: String
  {FS.get_reply(FS.put_reply(FS.Reply{ages, Su.Relaunch{f, p}}, rest)) == Wr.Got{FS.Reply{ages, Su.Relaunch{f, p}}, rest} : Wr.Dec<FS.Reply>}

# LAW restart_wire_reply_give_up: and every give-up reply
# EXCLUDES: a give-up read as a relaunch, a misread failure count
law restart_wire_reply_give_up:
  for +ages: List<&2, Nat>
  for hs: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ages)), LawsBase.wire_nats_fit(ages)) == True{} : Bool}
  for +f: Nat
  for hf: {LawsBase.wire_fits(f) == True{} : Bool}
  for rest: String
  {FS.get_reply(FS.put_reply(FS.Reply{ages, Su.GiveUp{f}}, rest)) == Wr.Got{FS.Reply{ages, Su.GiveUp{f}}, rest} : Wr.Dec<FS.Reply>}

# LAW restart_ffi_decides: on a whole request the entry answers the model's decision: the
# budget's new ages and the verdict (Su.decide)
# EXCLUDES: an entry that answers anything but the model's decision
law restart_ffi_decides:
  for +s: String
  for +c: Su.Cfg
  for +ages: List<&2, Nat>
  for +g: Nat
  for h: {FS.get_req(s) == Wr.Got{FS.Req{c, ages, g}, ""} : Wr.Dec<FS.Req>}
  {FS.ffi(s) == FS.put_reply(FS.Reply{Su.St.ages(Su.Decision.st(Su.decide(c, Su.St{ages, List.length(&2, Nat, ages)}, g))), Su.Decision.verdict(Su.decide(c, Su.St{ages, List.length(&2, Nat, ages)}, g))}, "") : String}

# LAW restart_ffi_malformed: a malformed request answers the error form, never a verdict
# EXCLUDES: a default verdict on garbage
law restart_ffi_malformed:
  for +s: String
  for h: {FS.get_req(s) == Wr.Bad{} : Wr.Dec<FS.Req>}
  {FS.ffi(s) == Wr.err("supervise: malformed request") : String}

# LAW restart_ffi_left_over: a request with input after it answers the error form
# EXCLUDES: a verdict on a request with trailing garbage
law restart_ffi_left_over:
  for +s: String
  for +q: FS.Req
  for +r: String
  for h: {FS.get_req(s) == Wr.Got{q, r} : Wr.Dec<FS.Req>}
  for ne: {String.is_empty(r) == False{} : Bool}
  {FS.ffi(s) == Wr.err("supervise: input left over") : String}

# The restart-budget entry, spelled
# ---------------------------------
# R1: every request Rust writes (`restart_budget::decide_call`: the four
#     configuration Nats, the ages' count then each age, the gap; every
#     number within the wire) gets the model's decision (Su.decide, which
#     restart_decide_window and restart_decide_verdict pin) spelled as Rust
#     reads it: the new ages' count then each age, then the verdict's tag
#     (Relaunch 0 with its failure count and pause, GiveUp 1 with its
#     failure count).
# R2: any other input answers exactly the error form: "supervise: input
#     left over" when a whole request is followed by more input, else
#     "supervise: malformed request".
# The spellers and the reader below are built from the wire primitives
# of bend/wire.bend only, never from the entry's put_*/get_*.

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

# Reader: the requests, read with the wire primitives

def rs_read_req.gap(c: Su.Cfg, a: List<&2, Nat>, r: Wr.Dec<Nat>) -> Wr.Dec<FS.Req>:
  match r:
    case Wr.Got{g, s}:
      Wr.Got{FS.Req{c, a, g}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def rs_read_req.ages(c: Su.Cfg, r: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<FS.Req>:
  match r:
    case Wr.Got{a, s}:
      rs_read_req.gap(c, a, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def rs_read_req.m(k: Nat, w: Nat, b: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FS.Req>:
  match r:
    case Wr.Got{m, s}:
      rs_read_req.ages(Su.Cfg{k, w, b, m}, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case Wr.Bad{}:
      Wr.Bad{}

def rs_read_req.b(k: Nat, w: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FS.Req>:
  match r:
    case Wr.Got{b, s}:
      rs_read_req.m(k, w, b, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def rs_read_req.w(k: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FS.Req>:
  match r:
    case Wr.Got{w, s}:
      rs_read_req.b(k, w, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def rs_read_req.k(r: Wr.Dec<Nat>) -> Wr.Dec<FS.Req>:
  match r:
    case Wr.Got{k, s}:
      rs_read_req.w(k, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

# the request s starts with, and what follows it
def rs_read_req(s: String) -> Wr.Dec<FS.Req>:
  rs_read_req.k(Wr.get_nat(s))

def rs_spec.end(whole: Bool, q: FS.Req) -> String:
  match whole:
    case True{}:
      rs_spell_answer(q)
    case False{}:
      rs_left_over()

def rs_spec.run(r: Wr.Dec<FS.Req>) -> String:
  match r:
    case Wr.Got{q, s}:
      rs_spec.end(Wr.end(s), q)
    case Wr.Bad{}:
      rs_malformed()

# the reply to s: the model's decision on the request s is exactly; the
# left-over error when more input follows a whole request; else the
# malformed error
def rs_spec(s: String) -> String:
  rs_spec.run(rs_read_req(s))

# LAW restart_ffi_exact_spec: on every input the entry answers the spelled decision on the request the input is exactly, "supervise: input left over" when more input follows a whole request, and "supervise: malformed request" on any other input
# EXCLUDES: a reply tag, field order or age list that drifts from the
#   bytes Rust reads, a request field misread or reordered, a default for
#   malformed input, the two error texts swapped or reworded, input left
#   over ignored
law restart_ffi_exact_spec:
  for +s: String
  {FS.ffi(s) == rs_spec(s) : String}

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

# LAW restart_ffi_tags_example: anchor: the bytes Rust sends and reads: a failure 3 ms after two
# failures (ages 5 and 98) with give-up after 2 in a 100 ms window, base pause 10, cap 50: the old
# age 98 leaves the window, the second failure relaunches after 20 ms; the same with give-up after
# 1: given up at 2 failures; a third failure whose 40 ms pause is capped at 15; no input, a missing
# gap, a list shorter than its count, and left-over input
# EXCLUDES: another spelling of a request or a reply, a swapped verdict
#   tag, the error texts swapped
law restart_ffi_tags_example:
  {[FS.ffi("2,100,10,50,2,5,98,3,"), FS.ffi("1,100,10,50,2,5,98,3,"), FS.ffi("9,100,10,15,2,5,6,1,"), FS.ffi(""), FS.ffi("2,100,10,50,0,"), FS.ffi("2,100,10,50,2,5,3,"), FS.ffi("2,100,10,50,0,3,x")] == ["2,0,8,0,2,20,", "2,0,8,1,2,", "3,0,6,7,0,3,15,", "E supervise: malformed request", "E supervise: malformed request", "E supervise: malformed request", "E supervise: input left over"] : List<&2, String>}

# The whole restart-budget entry, every input
# -------------------------------------------
# The request and the reply as the wire grammar of WIRE.md, read and
# spelled with the wire primitives alone (never the entry's own codec),
# and the decision as the spec above states it (restart_window,
# restart_verdict_put; never the model's code):
#   request  k, w, base, max; the ages (a count, then each age); the gap
#   reply    the new ages (a count, then each); the verdict: 0, then the
#            failure count and the pause (a relaunch) | 1, then the
#            failure count (a give-up)
# A request that cannot be read answers "supervise: malformed request"; a
# request with input after it answers "supervise: input left over".

def sv_read.gap(c: Su.Cfg, a: List<&2, Nat>, r: Wr.Dec<Nat>) -> Wr.Dec<FS.Req>:
  match r:
    case Wr.Got{g, s}:
      Wr.Got{FS.Req{c, a, g}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def sv_read.ages(c: Su.Cfg, r: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<FS.Req>:
  match r:
    case Wr.Got{a, s}:
      sv_read.gap(c, a, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def sv_read.m(k: Nat, w: Nat, b: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FS.Req>:
  match r:
    case Wr.Got{m, s}:
      sv_read.ages(Su.Cfg{k, w, b, m}, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case Wr.Bad{}:
      Wr.Bad{}

def sv_read.b(k: Nat, w: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FS.Req>:
  match r:
    case Wr.Got{b, s}:
      sv_read.m(k, w, b, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def sv_read.w(k: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FS.Req>:
  match r:
    case Wr.Got{w, s}:
      sv_read.b(k, w, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def sv_read.k(r: Wr.Dec<Nat>) -> Wr.Dec<FS.Req>:
  match r:
    case Wr.Got{k, s}:
      sv_read.w(k, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

# the request at the head of s, and the input after it
def sv_read(s: String) -> Wr.Dec<FS.Req>:
  sv_read.k(Wr.get_nat(s))

# a verdict on the wire: 0, the failure count, the pause | 1, the count
def sv_verdict(v: Su.Verdict, rest: String) -> String:
  match v:
    case Su.Relaunch{f, b}:
      Wr.put_nat(0n, Wr.put_nat(f, Wr.put_nat(b, rest)))
    case Su.GiveUp{f}:
      Wr.put_nat(1n, Wr.put_nat(f, rest))

# the reply to a request: the failure at age 0, then the ages still inside
# the window (each g ms older); the verdict on the failures it keeps
def sv_reply(q: FS.Req) -> String:
  match q:
    case FS.Req{c, ages, +g}:
      match c:
        case Su.Cfg{+k, +w, +b, +m}:
          +kept = restart_window(w, g, ages)
          +n = {1n+List.length(&2, Nat, kept) : Nat}
          Wr.put_list(~Nat, ~Wr.put_nat, 0n <> kept, sv_verdict(restart_verdict_put(Nat.is_lt(k, n), Su.Cfg{k, w, b, m}, n), ""))

def sv_entry.of(d: Wr.Dec<FS.Req>) -> String:
  match d:
    case Wr.Got{q, r}:
      match r:
        case SNil{}:
          sv_reply(q)
        case SCon{c, t}:
          Wr.err("supervise: input left over")
    case Wr.Bad{}:
      Wr.err("supervise: malformed request")

# the entry's answer to s
def sv_entry(s: String) -> String:
  sv_entry.of(sv_read(s))

# LAW restart_ffi_exact: for every input, the entry answers exactly: on a request (as the wire
# primitives read it) with nothing after it, the new ages (this failure at
# 0, then the ages still inside the window, each g ms older) and the
# verdict (give up past k failures in the window, else relaunch after the
# doubling pause capped at max); on a request with input after it, the
# error form "supervise: input left over"; on any other input, the error
# form "supervise: malformed request"
# EXCLUDES: a misread or reordered field, a verdict tag read as another, a
#   decision on garbage or on a request with input after it, another error
#   text, a codec of the entry wrong both ways (the spec never calls it)
law restart_ffi_exact:
  for +s: String
  {FS.ffi(s) == sv_entry(s) : String}

# LAW restart_ffi_exact_example: anchor: the strings Rust writes and the replies it reads: an
# age that leaves the window, a third failure that doubles the pause twice,
# the same failure given up with k = 2, a pause capped at max; a cut request
# and input left over are refused
# EXCLUDES: a field order other than Rust's, a vacuous restart_ffi_exact
law restart_ffi_exact_example:
  {[sv_entry("3,10,2,9,1,4,6,"), sv_entry("3,10,2,9,2,1,2,1,"), sv_entry("2,10,2,9,2,1,2,1,"), sv_entry("5,10,4,9,2,1,2,1,"), sv_entry("3,10,2,9,1,"), sv_entry("3,10,2,9,0,6,x")] == ["1,0,0,1,2,", "3,0,2,3,0,3,8,", "3,0,2,3,1,3,", "3,0,2,3,0,3,9,", Wr.err("supervise: malformed request"), Wr.err("supervise: input left over")] : List<&2, String>}

# LAW timeouts_ordered: every timeout comes after the timeouts it waits for (Su.Tm.ordered
# lists them), whatever the base values
law timeouts_ordered:
  for +t: Su.Tm
  {Su.Tm.ordered(t) == True{} : Bool}

# the order the timeouts keep, from the base values: each derived value
# covers the ones it waits for (the header of bend/supervise.bend Tm.ordered)
def tm_ordered_spec(t: Su.Tm) -> Bool:
  match t:
    case Su.Tm{snap, host, kstep, kterm, kverify, harness, wterm, wverify, +margin, +refresh, boot, +relaunch, +startup, +check, slack, +k, +bmax, +loop, +qanswer}:
      +td = Nat.add(Nat.add(Nat.add(Nat.add(snap, host), Nat.mul(3n, kstep)), kterm), kverify)
      +sg = Nat.add(td, harness)
      +dr = Nat.add(Nat.add(sg, wterm), wverify)
      +seen = Nat.add(Nat.add(relaunch, startup), check)
      +step = Nat.add(bmax, loop)
      # the stop grace covers the kernel teardown
      Bool.and(Nat.is_le(td, sg),
        # the launcher's wait covers the supervisor's drain
        Bool.and(Nat.is_le(dr, Nat.add(dr, margin)),
          # a parent's kill covers the kill route's grace and the child's drain
          Bool.and(Nat.is_le(Nat.add(sg, dr), Nat.add(Nat.add(sg, dr), margin)),
            # a lost worker sees the relaunched supervisor before it exits
            Bool.and(Nat.is_le(seen, Nat.add(seen, slack)),
              # busy evidence outlives one refresh
              Bool.and(Nat.is_le(refresh, Nat.add(refresh, boot)),
                # a quiesced gate stays closed past the answer phase
                Bool.and(Nat.is_le(qanswer, Nat.add(qanswer, sg)),
                  # the restart window holds the give-up count of loop steps
                  Nat.is_le(Nat.mul(k, step), Nat.mul(1n+k, step))))))))

# LAW timeouts_ordered_exact: the order timeouts_ordered proves is exactly the header's
# comparisons over the base values: the stop grace covers the teardown, the
# launcher's wait the drain, a child kill the kill route's grace and the
# child's drain, the lost window the relaunch, start and check, the max age
# a refresh, the quiesce hold the answer phase, the restart window k loop
# steps; for every base values
# EXCLUDES: Tm.ordered checking fewer, other or weaker comparisons than the
#   header's (timeouts_ordered would then prove an order nobody stated);
#   being True for every t, ordered = True is the same function, and this
#   law makes timeouts_ordered read as these comparisons
law timeouts_ordered_exact:
  for +t: Su.Tm
  {Su.Tm.ordered(t) == tm_ordered_spec(t) : Bool}
