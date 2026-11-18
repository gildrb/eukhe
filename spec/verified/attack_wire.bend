# verified (spec): the wire of the attack entry (bend/ffi_attack.bend) as
# the laws of area attack (laws/attack.bend, section entry) read it: the
# requests and replies spelled with the wire primitives only
# (bend/wire.bend; their round trips: laws/wire.bend), what fits the wire,
# and the reader of a request. Verify's label and the gauges are spelled
# as the strength entry spells them (spec/verified/strength_wire.bend),
# the slots as the verify entry does (spec/verified/verify_wire.bend). A
# spec: the shipped code never calls it.

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/attack.bend as At
import ../../bend/ffi_attack.bend as FA
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ./verify_wire.bend as SVW
import ./strength_wire.bend as SSW

# Spellers: a request as Rust writes it
# -------------------------------------

# the judge's verdict: 0 none; 1 and whether it agrees
def w_agrees(m: Maybe<&2, Bool>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{yes}:
      Wr.put_nat(1n, Wr.put_bool(yes, rest))

# what running an attack showed: ran, passes, differs, then the verdict
def w_run(r: At.Run, rest: String) -> String:
  match r:
    case At.Run{ran, passes, differs, agrees}:
      Wr.put_bool(ran, Wr.put_bool(passes, Wr.put_bool(differs, w_agrees(agrees, rest))))

# the tag of an outcome: 0 survived, 1 clean, 2 unrun
def w_outcome(o: At.Outcome) -> Nat:
  match o:
    case At.Survived{}:
      0n
    case At.Clean{}:
      1n
    case At.Unrun{}:
      2n

# an outcome, then rest
def w_outcome_s(o: At.Outcome, rest: String) -> String:
  Wr.put_nat(w_outcome(o), rest)

def w_outcomes(os: List<&2, At.Outcome>, rest: String) -> String:
  Wr.put_list(~At.Outcome, ~w_outcome_s, os, rest)

# a request, then rest
def w_req(q: FA.Req, rest: String) -> String:
  match q:
    case FA.QOutcome{r}:
      Wr.put_nat(0n, w_run(r, rest))
    case FA.QLabel{l, now, gs, os}:
      Wr.put_nat(1n, Wr.put_nat(SSW.w_vlabel(l), Wr.put_nat(now, SSW.w_gauges(gs, w_outcomes(os, rest)))))
    case FA.QExit{base, now, slots, gs, os}:
      Wr.put_nat(2n, Wr.put_nat(base, Wr.put_nat(now, SVW.w_slots(slots, SSW.w_gauges(gs, w_outcomes(os, rest))))))

# Spellers: the reply, as Rust reads it
# -------------------------------------

# the reply to a request: the model's decision, spelled as Rust reads it
# (the label as the strength entry spells it). The decisions are the
# model's (bend/attack.bend), each pinned by the laws of laws/attack.bend:
# outcome by attack_outcome_is_spec, label by attack_label_is_spec, exit
# by attack_exit_is_spec.
def w_reply(q: FA.Req) -> String:
  match q:
    case FA.QOutcome{r}:
      Wr.put_nat(w_outcome(At.outcome(r)), "")
    case FA.QLabel{l, now, gs, os}:
      Wr.put_nat(SSW.w_label(At.label(l, now, gs, os)), "")
    case FA.QExit{base, now, slots, gs, os}:
      Wr.put_nat(At.exit(base, now, slots, gs, os), "")

# Bounds: every number of a request fits the wire
# -----------------------------------------------

# the count of the outcomes fits the wire (each tag is below 3)
def fit_outcomes(+os: List<&2, At.Outcome>) -> Bool:
  LawsBase.wire_fits(List.length(&2, At.Outcome, os))

def fit_req(q: FA.Req) -> Bool:
  match q:
    case FA.QOutcome{r}:
      True{}
    case FA.QLabel{l, now, gs, os}:
      Bool.and(LawsBase.wire_fits(now), Bool.and(SSW.fit_gauges(gs), fit_outcomes(os)))
    case FA.QExit{base, now, slots, gs, os}:
      Bool.and(LawsBase.wire_fits(base), Bool.and(LawsBase.wire_fits(now), Bool.and(SVW.fit_slots(slots), Bool.and(SSW.fit_gauges(gs), fit_outcomes(os)))))

# The reader: the request an input spells, read with the wire's decoders
# ----------------------------------------------------------------------

def r_outcome.tag(r: Wr.Dec<Nat>) -> Wr.Dec<At.Outcome>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{At.Survived{}, s}
        case 1n:
          Wr.Got{At.Clean{}, s}
        case 2n:
          Wr.Got{At.Unrun{}, s}
        case 3n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_outcome(s: String) -> Wr.Dec<At.Outcome>:
  r_outcome.tag(Wr.get_nat(s))

def r_outcomes(s: String) -> Wr.Dec<List<&2, At.Outcome>>:
  Wr.get_list(~At.Outcome, ~r_outcome, s)

def r_agrees.yes(r: Wr.Dec<Bool>) -> Wr.Dec<Maybe<&2, Bool>>:
  match r:
    case Wr.Got{yes, s}:
      Wr.Got{Some{yes}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_agrees(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Bool>>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{None{}, s}
        case 1n:
          r_agrees.yes(Wr.get_bool(s))
        case 2n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.outcome_agrees(ran: Bool, passes: Bool, differs: Bool, r: Wr.Dec<Maybe<&2, Bool>>) -> Wr.Dec<FA.Req>:
  match r:
    case Wr.Got{agrees, s}:
      Wr.Got{FA.QOutcome{At.Run{ran, passes, differs, agrees}}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.outcome_differs(ran: Bool, passes: Bool, r: Wr.Dec<Bool>) -> Wr.Dec<FA.Req>:
  match r:
    case Wr.Got{differs, s}:
      r_req.outcome_agrees(ran, passes, differs, r_agrees(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.outcome_passes(ran: Bool, r: Wr.Dec<Bool>) -> Wr.Dec<FA.Req>:
  match r:
    case Wr.Got{passes, s}:
      r_req.outcome_differs(ran, passes, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.outcome(r: Wr.Dec<Bool>) -> Wr.Dec<FA.Req>:
  match r:
    case Wr.Got{ran, s}:
      r_req.outcome_passes(ran, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.label_os(l: V.Label, now: Nat, gs: List<&2, St.Gauge>, r: Wr.Dec<List<&2, At.Outcome>>) -> Wr.Dec<FA.Req>:
  match r:
    case Wr.Got{os, s}:
      Wr.Got{FA.QLabel{l, now, gs, os}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.label_gs(l: V.Label, now: Nat, r: Wr.Dec<List<&2, St.Gauge>>) -> Wr.Dec<FA.Req>:
  match r:
    case Wr.Got{gs, s}:
      r_req.label_os(l, now, gs, r_outcomes(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.label_now(l: V.Label, r: Wr.Dec<Nat>) -> Wr.Dec<FA.Req>:
  match r:
    case Wr.Got{now, s}:
      r_req.label_gs(l, now, SSW.r_gauges(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.label(r: Wr.Dec<V.Label>) -> Wr.Dec<FA.Req>:
  match r:
    case Wr.Got{l, s}:
      r_req.label_now(l, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.exit_os(base: Nat, now: Nat, slots: List<&2, V.Slot>, gs: List<&2, St.Gauge>, r: Wr.Dec<List<&2, At.Outcome>>) -> Wr.Dec<FA.Req>:
  match r:
    case Wr.Got{os, s}:
      Wr.Got{FA.QExit{base, now, slots, gs, os}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.exit_gs(base: Nat, now: Nat, slots: List<&2, V.Slot>, r: Wr.Dec<List<&2, St.Gauge>>) -> Wr.Dec<FA.Req>:
  match r:
    case Wr.Got{gs, s}:
      r_req.exit_os(base, now, slots, gs, r_outcomes(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.exit_slots(base: Nat, now: Nat, r: Wr.Dec<List<&2, V.Slot>>) -> Wr.Dec<FA.Req>:
  match r:
    case Wr.Got{slots, s}:
      r_req.exit_gs(base, now, slots, SSW.r_gauges(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.exit_now(base: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FA.Req>:
  match r:
    case Wr.Got{now, s}:
      r_req.exit_slots(base, now, SVW.r_slots(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req.exit(r: Wr.Dec<Nat>) -> Wr.Dec<FA.Req>:
  match r:
    case Wr.Got{base, s}:
      r_req.exit_now(base, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def r_req(r: Wr.Dec<Nat>) -> Wr.Dec<FA.Req>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          r_req.outcome(Wr.get_bool(s))
        case 1n:
          r_req.label(SSW.r_vlabel(Wr.get_nat(s)))
        case 2n:
          r_req.exit(Wr.get_nat(s))
        case 3n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def r_whole.end(b: Bool, q: FA.Req) -> Maybe<&2, FA.Req>:
  match b:
    case True{}:
      Some{q}
    case False{}:
      None{}

def r_whole(r: Wr.Dec<FA.Req>) -> Maybe<&2, FA.Req>:
  match r:
    case Wr.Got{q, s}:
      r_whole.end(Wr.end(s), q)
    case Wr.Bad{}:
      None{}

# the request s spells whole, with nothing after it
def read(s: String) -> Maybe<&2, FA.Req>:
  r_whole(r_req(Wr.get_nat(s)))
