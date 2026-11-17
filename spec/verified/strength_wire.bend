# verified (spec): the wire of the strength entry (bend/ffi_strength.bend)
# as the laws of area strength (laws/strength.bend, section entry) read
# it: the requests and replies spelled with the wire primitives only
# (bend/wire.bend; their round trips: laws/wire.bend), what fits the wire,
# and the reader of a request. Slots and actors are spelled as the verify
# entry spells them (spec/verified/verify_wire.bend). A spec: the shipped
# code never calls it.

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/ffi_strength.bend as FS
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ./verify_wire.bend as SW

# Spellers: a request as Rust writes it
# -------------------------------------

# the tag of verify's label: 0 verified, 1 failed, 2 unverified, 3 passed
def w_vlabel(l: V.Label) -> Nat:
  match l:
    case V.Verified{}:
      0n
    case V.Failed{}:
      1n
    case V.Unverified{}:
      2n
    case V.Passed{}:
      3n

# a bar: 0 exempt; 1 waived; 2 needs and the percent
def w_bar(b: St.Bar, rest: String) -> String:
  match b:
    case St.Exempt{}:
      Wr.put_nat(0n, rest)
    case St.Waived{}:
      Wr.put_nat(1n, rest)
    case St.Needs{pct}:
      Wr.put_nat(2n, Wr.put_nat(pct, rest))

# a mark: 0 unmeasured; 1 measured, the breaks caught, run and planned,
# the state
def w_mark(m: St.Mark, rest: String) -> String:
  match m:
    case St.Unmeasured{}:
      Wr.put_nat(0n, rest)
    case St.Measured{c, n, p, at}:
      Wr.put_nat(1n, Wr.put_nat(c, Wr.put_nat(n, Wr.put_nat(p, Wr.put_nat(at, rest)))))

# a gauge: the bar, then the mark
def w_gauge(g: St.Gauge, rest: String) -> String:
  match g:
    case St.Gauge{b, m}:
      w_bar(b, w_mark(m, rest))

def w_gauges(gs: List<&2, St.Gauge>, rest: String) -> String:
  Wr.put_list(~St.Gauge, ~w_gauge, gs, rest)

# a request, then rest
def w_req(q: FS.Req, rest: String) -> String:
  match q:
    case FS.QSettle{l, now, gs}:
      Wr.put_nat(0n, Wr.put_nat(w_vlabel(l), Wr.put_nat(now, w_gauges(gs, rest))))
    case FS.QLabel{l, now, gs}:
      Wr.put_nat(1n, Wr.put_nat(w_vlabel(l), Wr.put_nat(now, w_gauges(gs, rest))))
    case FS.QExit{base, now, slots, gs}:
      Wr.put_nat(2n, Wr.put_nat(base, Wr.put_nat(now, SW.w_slots(slots, w_gauges(gs, rest)))))
    case FS.QRecord{who, i, m, gs}:
      Wr.put_nat(3n, Wr.put_nat(SW.w_actor(who), Wr.put_nat(i, w_mark(m, w_gauges(gs, rest)))))
    case FS.QStrength{now, g}:
      Wr.put_nat(4n, Wr.put_nat(now, w_gauge(g, rest)))

# Spellers: the reply, as Rust reads it
# -------------------------------------

# the tag of a label: 0 verified, 1 failed, 2 unverified, 3 passed, 4 not
# certified
def w_label(l: St.Label) -> Nat:
  match l:
    case St.Verified{}:
      0n
    case St.Failed{}:
      1n
    case St.Unverified{}:
      2n
    case St.Passed{}:
      3n
    case St.Uncertified{}:
      4n

# a step: 0 measure and the index; 1 end and the label
def w_step(x: St.Step) -> String:
  match x:
    case St.Measure{i}:
      Wr.put_nat(0n, Wr.put_nat(i, ""))
    case St.End{l}:
      Wr.put_nat(1n, Wr.put_nat(w_label(l), ""))

# the tag of a strength: 0 strong, 1 weak, 2 unshown, 3 free
def w_strength(x: St.Strength) -> Nat:
  match x:
    case St.Strong{}:
      0n
    case St.Weak{}:
      1n
    case St.Unshown{}:
      2n
    case St.Free{}:
      3n

def w_recorded(r: Bool & List<&2, St.Gauge>) -> String:
  (ok, gs) = r
  Wr.put_bool(ok, w_gauges(gs, ""))

# the reply to a request: the model's decision, spelled as Rust reads it.
# The decisions are the model's (bend/strength.bend), each pinned by the
# laws of laws/strength.bend: settle by the laws of K4, label by
# strength_label_is_spec, exit by strength_exit_is_spec, record by the
# laws of K5, strength by strength_grade_is_spec.
def w_reply(q: FS.Req) -> String:
  match q:
    case FS.QSettle{l, now, gs}:
      w_step(St.settle(l, now, gs))
    case FS.QLabel{l, now, gs}:
      Wr.put_nat(w_label(St.label(l, now, gs)), "")
    case FS.QExit{base, now, slots, gs}:
      Wr.put_nat(St.exit(base, now, slots, gs), "")
    case FS.QRecord{who, i, m, gs}:
      w_recorded(St.record(who, i, m, gs))
    case FS.QStrength{now, g}:
      Wr.put_nat(w_strength(St.strength(now, g)), "")

# Bounds: every number of a request fits the wire
# -----------------------------------------------

def fit_bar(b: St.Bar) -> Bool:
  match b:
    case St.Exempt{}:
      True{}
    case St.Waived{}:
      True{}
    case St.Needs{pct}:
      LawsBase.wire_fits(pct)

def fit_mark(m: St.Mark) -> Bool:
  match m:
    case St.Unmeasured{}:
      True{}
    case St.Measured{c, n, p, at}:
      Bool.and(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(p), LawsBase.wire_fits(at))))

def fit_gauge(g: St.Gauge) -> Bool:
  match g:
    case St.Gauge{b, m}:
      Bool.and(fit_bar(b), fit_mark(m))

def fit_gauges.items(gs: List<&2, St.Gauge>) -> Bool:
  match gs:
    case Nil{}:
      True{}
    case Con{g, t}:
      Bool.and(fit_gauge(g), fit_gauges.items(t))

# the count of the gauges and every gauge fit the wire
def fit_gauges(+gs: List<&2, St.Gauge>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, St.Gauge, gs)), fit_gauges.items(gs))

def fit_req(q: FS.Req) -> Bool:
  match q:
    case FS.QSettle{l, now, gs}:
      Bool.and(LawsBase.wire_fits(now), fit_gauges(gs))
    case FS.QLabel{l, now, gs}:
      Bool.and(LawsBase.wire_fits(now), fit_gauges(gs))
    case FS.QExit{base, now, slots, gs}:
      Bool.and(LawsBase.wire_fits(base), Bool.and(LawsBase.wire_fits(now), Bool.and(SW.fit_slots(slots), fit_gauges(gs))))
    case FS.QRecord{who, i, m, gs}:
      Bool.and(LawsBase.wire_fits(i), Bool.and(fit_mark(m), fit_gauges(gs)))
    case FS.QStrength{now, g}:
      Bool.and(LawsBase.wire_fits(now), fit_gauge(g))

# The reader: the request an input spells, read with the wire's decoders
# ----------------------------------------------------------------------

def r_vlabel(r: Wr.Dec<Nat>) -> Wr.Dec<V.Label>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{V.Verified{}, s}
        case 1n:
          Wr.Got{V.Failed{}, s}
        case 2n:
          Wr.Got{V.Unverified{}, s}
        case 3n:
          Wr.Got{V.Passed{}, s}
        case 4n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_bar.pct(r: Wr.Dec<Nat>) -> Wr.Dec<St.Bar>:
  match r:
    case Wr.Got{pct, s}:
      Wr.Got{St.Needs{pct}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_bar(r: Wr.Dec<Nat>) -> Wr.Dec<St.Bar>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{St.Exempt{}, s}
        case 1n:
          Wr.Got{St.Waived{}, s}
        case 2n:
          r_bar.pct(Wr.get_nat(s))
        case 3n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_mark.at(c: Nat, n: Nat, p: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<St.Mark>:
  match r:
    case Wr.Got{at, s}:
      Wr.Got{St.Measured{c, n, p, at}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_mark.planned(c: Nat, n: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<St.Mark>:
  match r:
    case Wr.Got{p, s}:
      r_mark.at(c, n, p, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_mark.ran(c: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<St.Mark>:
  match r:
    case Wr.Got{n, s}:
      r_mark.planned(c, n, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_mark.caught(r: Wr.Dec<Nat>) -> Wr.Dec<St.Mark>:
  match r:
    case Wr.Got{c, s}:
      r_mark.ran(c, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_mark(r: Wr.Dec<Nat>) -> Wr.Dec<St.Mark>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{St.Unmeasured{}, s}
        case 1n:
          r_mark.caught(Wr.get_nat(s))
        case 2n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_gauge.mark(b: St.Bar, r: Wr.Dec<St.Mark>) -> Wr.Dec<St.Gauge>:
  match r:
    case Wr.Got{m, s}:
      Wr.Got{St.Gauge{b, m}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_gauge.bar(r: Wr.Dec<St.Bar>) -> Wr.Dec<St.Gauge>:
  match r:
    case Wr.Got{b, s}:
      r_gauge.mark(b, r_mark(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def r_gauge(s: String) -> Wr.Dec<St.Gauge>:
  r_gauge.bar(r_bar(Wr.get_nat(s)))

def r_gauges(s: String) -> Wr.Dec<List<&2, St.Gauge>>:
  Wr.get_list(~St.Gauge, ~r_gauge, s)

def r_req.settle_gs(l: V.Label, now: Nat, r: Wr.Dec<List<&2, St.Gauge>>) -> Wr.Dec<FS.Req>:
  match r:
    case Wr.Got{gs, s}:
      Wr.Got{FS.QSettle{l, now, gs}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.settle_now(l: V.Label, r: Wr.Dec<Nat>) -> Wr.Dec<FS.Req>:
  match r:
    case Wr.Got{now, s}:
      r_req.settle_gs(l, now, r_gauges(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.settle(r: Wr.Dec<V.Label>) -> Wr.Dec<FS.Req>:
  match r:
    case Wr.Got{l, s}:
      r_req.settle_now(l, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.label_gs(l: V.Label, now: Nat, r: Wr.Dec<List<&2, St.Gauge>>) -> Wr.Dec<FS.Req>:
  match r:
    case Wr.Got{gs, s}:
      Wr.Got{FS.QLabel{l, now, gs}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.label_now(l: V.Label, r: Wr.Dec<Nat>) -> Wr.Dec<FS.Req>:
  match r:
    case Wr.Got{now, s}:
      r_req.label_gs(l, now, r_gauges(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.label(r: Wr.Dec<V.Label>) -> Wr.Dec<FS.Req>:
  match r:
    case Wr.Got{l, s}:
      r_req.label_now(l, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.exit_gs(base: Nat, now: Nat, slots: List<&2, V.Slot>, r: Wr.Dec<List<&2, St.Gauge>>) -> Wr.Dec<FS.Req>:
  match r:
    case Wr.Got{gs, s}:
      Wr.Got{FS.QExit{base, now, slots, gs}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.exit_slots(base: Nat, now: Nat, r: Wr.Dec<List<&2, V.Slot>>) -> Wr.Dec<FS.Req>:
  match r:
    case Wr.Got{slots, s}:
      r_req.exit_gs(base, now, slots, r_gauges(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.exit_now(base: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FS.Req>:
  match r:
    case Wr.Got{now, s}:
      r_req.exit_slots(base, now, SW.r_slots(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.exit(r: Wr.Dec<Nat>) -> Wr.Dec<FS.Req>:
  match r:
    case Wr.Got{base, s}:
      r_req.exit_now(base, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.record_gs(who: V.Actor, i: Nat, m: St.Mark, r: Wr.Dec<List<&2, St.Gauge>>) -> Wr.Dec<FS.Req>:
  match r:
    case Wr.Got{gs, s}:
      Wr.Got{FS.QRecord{who, i, m, gs}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.record_mark(who: V.Actor, i: Nat, r: Wr.Dec<St.Mark>) -> Wr.Dec<FS.Req>:
  match r:
    case Wr.Got{m, s}:
      r_req.record_gs(who, i, m, r_gauges(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.record_i(who: V.Actor, r: Wr.Dec<Nat>) -> Wr.Dec<FS.Req>:
  match r:
    case Wr.Got{i, s}:
      r_req.record_mark(who, i, r_mark(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.record(r: Wr.Dec<V.Actor>) -> Wr.Dec<FS.Req>:
  match r:
    case Wr.Got{who, s}:
      r_req.record_i(who, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.strength_g(now: Nat, r: Wr.Dec<St.Gauge>) -> Wr.Dec<FS.Req>:
  match r:
    case Wr.Got{g, s}:
      Wr.Got{FS.QStrength{now, g}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.strength(r: Wr.Dec<Nat>) -> Wr.Dec<FS.Req>:
  match r:
    case Wr.Got{now, s}:
      r_req.strength_g(now, r_gauge(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req(r: Wr.Dec<Nat>) -> Wr.Dec<FS.Req>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          r_req.settle(r_vlabel(Wr.get_nat(s)))
        case 1n:
          r_req.label(r_vlabel(Wr.get_nat(s)))
        case 2n:
          r_req.exit(Wr.get_nat(s))
        case 3n:
          r_req.record(SW.r_actor(Wr.get_nat(s)))
        case 4n:
          r_req.strength(Wr.get_nat(s))
        case 5n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_whole.end(b: Bool, q: FS.Req) -> Maybe<&2, FS.Req>:
  match b:
    case True{}:
      Some{q}
    case False{}:
      None{}

def r_whole(r: Wr.Dec<FS.Req>) -> Maybe<&2, FS.Req>:
  match r:
    case Wr.Got{q, s}:
      r_whole.end(Wr.end(s), q)
    case Wr.Bad{}:
      None{}

# the request s spells whole, with nothing after it
def read(s: String) -> Maybe<&2, FS.Req>:
  r_whole(r_req(Wr.get_nat(s)))
