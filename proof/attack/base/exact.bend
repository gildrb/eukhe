# eukhe: lemmas of the entry proofs of area attack (bend/ffi_attack.bend):
# the request decoder answers Got{q, rest} only for an input that is the
# spelling of q before rest, every number and count within the wire
# (axe.req). Per decoder, a predicate on its answer (what it says about its
# input), carried stage by stage; verify's label, the gauges and the slots
# by the strength entry's lemmas (SX), the outcomes item by item. No answer
# of the entry to a request opens with 'E' (axe.answer_ok).

import Base
import ../../../bend/verify.bend as V
import ../../../bend/strength.bend as St
import ../../../bend/attack.bend as At
import ../../../bend/ffi_verify.bend as FV
import ../../../bend/ffi_strength.bend as FS
import ../../../bend/ffi_attack.bend as FA
import ../../../bend/wire.bend as Wr
import ../../../spec/verified/verify_wire.bend as SVW
import ../../../spec/verified/strength_wire.bend as SSW
import ../../../spec/verified/attack_wire.bend as SAW
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../../wire/wire_list_reads_items.bend as PWireListReadsItems
import ../../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../../strength/base/exact.bend as SX
import ./entry.bend as LE

# Tags: the judge's verdict, an outcome
# -------------------------------------

# what the verdict reader's answer says about its input s
def axe.AgP(s: String, d: Wr.Dec<Maybe<&2, Bool>>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == SAW.w_agrees(m, r) : String}
    case Wr.Bad{}:
      Unit

def axe.agrees_yes(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Bool>, bp: SX.sx.BP(s1, d)) -> axe.AgP(s, FA.get_agrees.yes(d)):
  match d:
    case Wr.Got{+y, +r}:
      SX.sx.ext(z => Wr.put_nat(1n, z), s, s1, Wr.put_bool(y, r), pre, bp)
    case Wr.Bad{}:
      Unit{}

def axe.agrees_of(t: Nat, -s: String, +s1: String, pre: {s == Wr.put_nat(t, s1) : String}) -> axe.AgP(s, FA.get_agrees(Wr.Got{t, s1})):
  match t:
    case 0n:
      pre
    case 1n:
      axe.agrees_yes(s, s1, pre, Wr.get_bool(s1), SX.sx.bool(s1))
    case 2n+u:
      Unit{}

def axe.agrees_tag(-s: String, d: Wr.Dec<Nat>, np: SX.sx.NP(s, d)) -> axe.AgP(s, FA.get_agrees(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = np
      axe.agrees_of(t, s, s1, e)
    case Wr.Bad{}:
      Unit{}

# the verdict reader accepts only 0, or 1 then T or F
def axe.agrees(+s: String) -> axe.AgP(s, FA.get_agrees(Wr.get_nat(s))):
  axe.agrees_tag(s, Wr.get_nat(s), SX.sx.nat(s))

# what the outcome reader's answer says about its input s
def axe.OP(s: String, d: Wr.Dec<At.Outcome>) -> Type:
  match d:
    case Wr.Got{o, r}:
      {s == SAW.w_outcome_s(o, r) : String}
    case Wr.Bad{}:
      Unit

def axe.outcome_of(t: Nat, -s: String, +s1: String, pre: {s == Wr.put_nat(t, s1) : String}) -> axe.OP(s, FA.get_outcome.tag(Wr.Got{t, s1})):
  match t:
    case 0n:
      pre
    case 1n:
      pre
    case 2n:
      pre
    case 3n+u:
      Unit{}

def axe.outcome_tag(-s: String, d: Wr.Dec<Nat>, np: SX.sx.NP(s, d)) -> axe.OP(s, FA.get_outcome.tag(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = np
      axe.outcome_of(t, s, s1, e)
    case Wr.Bad{}:
      Unit{}

# the outcome reader accepts only the tags 0, 1, 2
def axe.outcome(+s: String) -> axe.OP(s, FA.get_outcome(s)):
  axe.outcome_tag(s, Wr.get_nat(s), SX.sx.nat(s))

# Lists: outcomes
# ----------------

# what the item reader's answer says about its input s (k items)
def axe.OIP(s: String, k: Nat, d: Wr.Dec<List<&2, At.Outcome>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == LE.ae.items(xs, r) : String} & {List.length(&2, At.Outcome, xs) == k : Nat}
    case Wr.Bad{}:
      Unit

def axe.out_at(+s: String, -d: Wr.Dec<At.Outcome>, ed: {FA.get_outcome(s) == d : Wr.Dec<At.Outcome>}) -> axe.OP(s, d):
  %ed : axe.OP(s, _)
  axe.outcome(s)

# an item before items read
def axe.out_cons(-s: String, +c: At.Outcome, +r1: String, -k: Nat, d: Wr.Dec<List<&2, At.Outcome>>, ih: axe.OIP(r1, k, d), cp: axe.OP(s, Wr.Got{c, r1})) -> axe.OIP(s, 1n+k, LawsBase.wire_items.cons(At.Outcome, c, d)):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e2) = ih
      (SX.sx.ext(z => SAW.w_outcome_s(c, z), s, r1, LE.ae.items(xs, r), cp, e1), Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, At.Outcome, xs), k, e2))
    case Wr.Bad{}:
      Unit{}

# mm + 1 items, the first read from s as cur
def axe.out_items(mm: Nat, cur: Wr.Dec<At.Outcome>, +s: String, er: {FA.get_outcome(s) == cur : Wr.Dec<At.Outcome>}) -> axe.OIP(s, 1n+mm, LawsBase.wire_items.then(At.Outcome, cur, r => LawsBase.wire_items(~At.Outcome, ~FA.get_outcome, mm, r))):
  match mm cur:
    case 0n Wr.Got{+c, +r1}:
      axe.out_cons(s, c, r1, 0n, Wr.Got{Nil{}, r1}, ({==}, {==}), axe.out_at(s, Wr.Got{c, r1}, er))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+c, +r1}:
      axe.out_cons(s, c, r1, 1n+k, LawsBase.wire_items.then(At.Outcome, FA.get_outcome(r1), r => LawsBase.wire_items(~At.Outcome, ~FA.get_outcome, k, r)), axe.out_items(k, FA.get_outcome(r1), r1, {==}), axe.out_at(s, Wr.Got{c, r1}, er))
    case 1n++k Wr.Bad{}:
      Unit{}

def axe.out_items_of(k: Nat, +s: String) -> axe.OIP(s, k, LawsBase.wire_items(~At.Outcome, ~FA.get_outcome, k, s)):
  match k:
    case 0n:
      ({==}, {==})
    case 1n+mm:
      axe.out_items(mm, FA.get_outcome(s), s, {==})

# what the list reader's answer says about its input s
def axe.OLP(s: String, d: Wr.Dec<List<&2, At.Outcome>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == SAW.w_outcomes(xs, r) : String} & {SAW.fit_outcomes(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def axe.out_list(-s: String, +k: Nat, +s1: String, en: {s == Wr.put_nat(k, s1) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, d: Wr.Dec<List<&2, At.Outcome>>, ip: axe.OIP(s1, k, d)) -> axe.OLP(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e2) = ip
      +ln = e2
      +n = List.length(&2, At.Outcome, xs)
      +w = LE.ae.items(xs, r)
      +es = SX.sx.ext(z => Wr.put_nat(k, z), s, s1, w, en, e1)
      +el = Equal.cong(Nat, String, z => Wr.put_nat(z, w), k, n, Equal.sym(Nat, n, k, ln))
      +ew = Equal.sym(String, SAW.w_outcomes(xs, r), Wr.put_nat(n, w), LE.ae.w_outcomes(xs, r))
      +fl = Equal.trans(Bool, LawsBase.wire_fits(n), LawsBase.wire_fits(k), True{}, Equal.cong(Nat, Bool, z => LawsBase.wire_fits(z), n, k, ln), fk)
      (Equal.trans(String, s, Wr.put_nat(n, w), SAW.w_outcomes(xs, r), Equal.trans(String, s, Wr.put_nat(k, w), Wr.put_nat(n, w), es, el), ew), fl)
    case Wr.Bad{}:
      Unit{}

def axe.out_count(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> axe.OLP(s, LawsBase.wire_read_list.count(~At.Outcome, ~FA.get_outcome, d)):
  match d:
    case Wr.Got{+k, +s1}:
      +e = ed
      axe.out_list(s, k, s1, Wire.wire_nat_exact(s, k, s1, e), Wire.wire_nat_decoded_fits(s, k, s1, e), LawsBase.wire_items(~At.Outcome, ~FA.get_outcome, k, s1), axe.out_items_of(k, s1))
    case Wr.Bad{}:
      Unit{}

# the list reader accepts only a spelled list that fits
def axe.outcomes(+s: String) -> axe.OLP(s, Wr.get_list(~At.Outcome, ~FA.get_outcome, s)):
  %Equal.sym(Wr.Dec<List<&2, At.Outcome>>, Wr.get_list(~At.Outcome, ~FA.get_outcome, s), LawsBase.wire_read_list(~At.Outcome, ~FA.get_outcome, s), Wire.wire_list_reads_items(~At.Outcome, ~FA.get_outcome, s)) : axe.OLP(s, _)
  axe.out_count(s, Wr.get_nat(s), {==})

# Requests
# --------

# what the request reader's answer says about its input s
def axe.QP(s: String, d: Wr.Dec<FA.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == SAW.w_req(q, r) : String} & {SAW.fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# 0: an attack's run
def axe.out_agrees(-s: String, +ran: Bool, +passes: Bool, +differs: Bool, +s4: String, pre: {s == Wr.put_nat(0n, Wr.put_bool(ran, Wr.put_bool(passes, Wr.put_bool(differs, s4)))) : String}, d: Wr.Dec<Maybe<&2, Bool>>, ap: axe.AgP(s4, d)) -> axe.QP(s, FA.get_req.outcome_agrees(ran, passes, differs, d)):
  match d:
    case Wr.Got{+ag, +r}:
      (SX.sx.ext(z => Wr.put_nat(0n, Wr.put_bool(ran, Wr.put_bool(passes, Wr.put_bool(differs, z)))), s, s4, SAW.w_agrees(ag, r), pre, ap), {==})
    case Wr.Bad{}:
      Unit{}

def axe.out_differs(-s: String, +ran: Bool, +passes: Bool, +s3: String, pre: {s == Wr.put_nat(0n, Wr.put_bool(ran, Wr.put_bool(passes, s3))) : String}, d: Wr.Dec<Bool>, bp: SX.sx.BP(s3, d)) -> axe.QP(s, FA.get_req.outcome_differs(ran, passes, d)):
  match d:
    case Wr.Got{+differs, +s4}:
      axe.out_agrees(s, ran, passes, differs, s4, SX.sx.ext(z => Wr.put_nat(0n, Wr.put_bool(ran, Wr.put_bool(passes, z))), s, s3, Wr.put_bool(differs, s4), pre, bp), FA.get_agrees(Wr.get_nat(s4)), axe.agrees(s4))
    case Wr.Bad{}:
      Unit{}

def axe.out_passes(-s: String, +ran: Bool, +s2: String, pre: {s == Wr.put_nat(0n, Wr.put_bool(ran, s2)) : String}, d: Wr.Dec<Bool>, bp: SX.sx.BP(s2, d)) -> axe.QP(s, FA.get_req.outcome_passes(ran, d)):
  match d:
    case Wr.Got{+passes, +s3}:
      axe.out_differs(s, ran, passes, s3, SX.sx.ext(z => Wr.put_nat(0n, Wr.put_bool(ran, z)), s, s2, Wr.put_bool(passes, s3), pre, bp), Wr.get_bool(s3), SX.sx.bool(s3))
    case Wr.Bad{}:
      Unit{}

def axe.out_ran(-s: String, +s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Bool>, bp: SX.sx.BP(s1, d)) -> axe.QP(s, FA.get_req.outcome(d)):
  match d:
    case Wr.Got{+ran, +s2}:
      axe.out_passes(s, ran, s2, SX.sx.ext(z => Wr.put_nat(0n, z), s, s1, Wr.put_bool(ran, s2), pre, bp), Wr.get_bool(s2), SX.sx.bool(s2))
    case Wr.Bad{}:
      Unit{}

# 1: the label
def axe.lab_os(-s: String, +l: V.Label, +now: Nat, +gs: List<&2, St.Gauge>, +s4: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(SSW.w_vlabel(l), Wr.put_nat(now, SSW.w_gauges(gs, s4)))) : String}, fnow: {LawsBase.wire_fits(now) == True{} : Bool}, fgs: {SSW.fit_gauges(gs) == True{} : Bool}, d: Wr.Dec<List<&2, At.Outcome>>, op: axe.OLP(s4, d)) -> axe.QP(s, FA.get_req.label_os(l, now, gs, d)):
  match d:
    case Wr.Got{+os, +r}:
      (e, f) = op
      (SX.sx.ext(z => Wr.put_nat(1n, Wr.put_nat(SSW.w_vlabel(l), Wr.put_nat(now, SSW.w_gauges(gs, z)))), s, s4, SAW.w_outcomes(os, r), pre, e), SX.sx.and_t(LawsBase.wire_fits(now), Bool.and(SSW.fit_gauges(gs), SAW.fit_outcomes(os)), fnow, SX.sx.and_t(SSW.fit_gauges(gs), SAW.fit_outcomes(os), fgs, f)))
    case Wr.Bad{}:
      Unit{}

def axe.lab_gs(-s: String, +l: V.Label, +now: Nat, +s3: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(SSW.w_vlabel(l), Wr.put_nat(now, s3))) : String}, fnow: {LawsBase.wire_fits(now) == True{} : Bool}, d: Wr.Dec<List<&2, St.Gauge>>, gp: SX.sx.GLP(s3, d)) -> axe.QP(s, FA.get_req.label_gs(l, now, d)):
  match d:
    case Wr.Got{+gs, +s4}:
      (e, f) = gp
      axe.lab_os(s, l, now, gs, s4, SX.sx.ext(z => Wr.put_nat(1n, Wr.put_nat(SSW.w_vlabel(l), Wr.put_nat(now, z))), s, s3, SSW.w_gauges(gs, s4), pre, e), fnow, f, FA.get_outcomes(s4), axe.outcomes(s4))
    case Wr.Bad{}:
      Unit{}

def axe.lab_now(-s: String, +l: V.Label, +s2: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(SSW.w_vlabel(l), s2)) : String}, d: Wr.Dec<Nat>, np: SX.sx.NP(s2, d)) -> axe.QP(s, FA.get_req.label_now(l, d)):
  match d:
    case Wr.Got{+now, +s3}:
      (e, f) = np
      axe.lab_gs(s, l, now, s3, SX.sx.ext(z => Wr.put_nat(1n, Wr.put_nat(SSW.w_vlabel(l), z)), s, s2, Wr.put_nat(now, s3), pre, e), f, FS.get_gauges(s3), SX.sx.gauges(s3))
    case Wr.Bad{}:
      Unit{}

def axe.lab_l(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<V.Label>, lp: SX.sx.LbP(s1, d)) -> axe.QP(s, FA.get_req.label(d)):
  match d:
    case Wr.Got{+l, +s2}:
      axe.lab_now(s, l, s2, SX.sx.ext(z => Wr.put_nat(1n, z), s, s1, Wr.put_nat(SSW.w_vlabel(l), s2), pre, lp), Wr.get_nat(s2), SX.sx.nat(s2))
    case Wr.Bad{}:
      Unit{}

# 2: the exit code
def axe.ex_os(-s: String, +base: Nat, +now: Nat, +slots: List<&2, V.Slot>, +gs: List<&2, St.Gauge>, +s5: String, pre: {s == Wr.put_nat(2n, Wr.put_nat(base, Wr.put_nat(now, SVW.w_slots(slots, SSW.w_gauges(gs, s5))))) : String}, fb: {LawsBase.wire_fits(base) == True{} : Bool}, fnow: {LawsBase.wire_fits(now) == True{} : Bool}, fsl: {SVW.fit_slots(slots) == True{} : Bool}, fgs: {SSW.fit_gauges(gs) == True{} : Bool}, d: Wr.Dec<List<&2, At.Outcome>>, op: axe.OLP(s5, d)) -> axe.QP(s, FA.get_req.exit_os(base, now, slots, gs, d)):
  match d:
    case Wr.Got{+os, +r}:
      (e, f) = op
      +fo = SX.sx.and_t(SSW.fit_gauges(gs), SAW.fit_outcomes(os), fgs, f)
      +fs = SX.sx.and_t(SVW.fit_slots(slots), Bool.and(SSW.fit_gauges(gs), SAW.fit_outcomes(os)), fsl, fo)
      +fn = SX.sx.and_t(LawsBase.wire_fits(now), Bool.and(SVW.fit_slots(slots), Bool.and(SSW.fit_gauges(gs), SAW.fit_outcomes(os))), fnow, fs)
      (SX.sx.ext(z => Wr.put_nat(2n, Wr.put_nat(base, Wr.put_nat(now, SVW.w_slots(slots, SSW.w_gauges(gs, z))))), s, s5, SAW.w_outcomes(os, r), pre, e), SX.sx.and_t(LawsBase.wire_fits(base), Bool.and(LawsBase.wire_fits(now), Bool.and(SVW.fit_slots(slots), Bool.and(SSW.fit_gauges(gs), SAW.fit_outcomes(os)))), fb, fn))
    case Wr.Bad{}:
      Unit{}

def axe.ex_gs(-s: String, +base: Nat, +now: Nat, +slots: List<&2, V.Slot>, +s4: String, pre: {s == Wr.put_nat(2n, Wr.put_nat(base, Wr.put_nat(now, SVW.w_slots(slots, s4)))) : String}, fb: {LawsBase.wire_fits(base) == True{} : Bool}, fnow: {LawsBase.wire_fits(now) == True{} : Bool}, fsl: {SVW.fit_slots(slots) == True{} : Bool}, d: Wr.Dec<List<&2, St.Gauge>>, gp: SX.sx.GLP(s4, d)) -> axe.QP(s, FA.get_req.exit_gs(base, now, slots, d)):
  match d:
    case Wr.Got{+gs, +s5}:
      (e, f) = gp
      axe.ex_os(s, base, now, slots, gs, s5, SX.sx.ext(z => Wr.put_nat(2n, Wr.put_nat(base, Wr.put_nat(now, SVW.w_slots(slots, z)))), s, s4, SSW.w_gauges(gs, s5), pre, e), fb, fnow, fsl, f, FA.get_outcomes(s5), axe.outcomes(s5))
    case Wr.Bad{}:
      Unit{}

def axe.ex_slots(-s: String, +base: Nat, +now: Nat, +s3: String, pre: {s == Wr.put_nat(2n, Wr.put_nat(base, Wr.put_nat(now, s3))) : String}, fb: {LawsBase.wire_fits(base) == True{} : Bool}, fnow: {LawsBase.wire_fits(now) == True{} : Bool}, d: Wr.Dec<List<&2, V.Slot>>, sp: SX.sx.SLP(s3, d)) -> axe.QP(s, FA.get_req.exit_slots(base, now, d)):
  match d:
    case Wr.Got{+slots, +s4}:
      (e, f) = sp
      axe.ex_gs(s, base, now, slots, s4, SX.sx.ext(z => Wr.put_nat(2n, Wr.put_nat(base, Wr.put_nat(now, z))), s, s3, SVW.w_slots(slots, s4), pre, e), fb, fnow, f, FS.get_gauges(s4), SX.sx.gauges(s4))
    case Wr.Bad{}:
      Unit{}

def axe.ex_now(-s: String, +base: Nat, +s2: String, pre: {s == Wr.put_nat(2n, Wr.put_nat(base, s2)) : String}, fb: {LawsBase.wire_fits(base) == True{} : Bool}, d: Wr.Dec<Nat>, np: SX.sx.NP(s2, d)) -> axe.QP(s, FA.get_req.exit_now(base, d)):
  match d:
    case Wr.Got{+now, +s3}:
      (e, f) = np
      axe.ex_slots(s, base, now, s3, SX.sx.ext(z => Wr.put_nat(2n, Wr.put_nat(base, z)), s, s2, Wr.put_nat(now, s3), pre, e), fb, f, FV.get_slots(s3), SX.sx.slots(s3))
    case Wr.Bad{}:
      Unit{}

def axe.ex_base(-s: String, +s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Nat>, np: SX.sx.NP(s1, d)) -> axe.QP(s, FA.get_req.exit(d)):
  match d:
    case Wr.Got{+base, +s2}:
      (e, f) = np
      axe.ex_now(s, base, s2, SX.sx.ext(z => Wr.put_nat(2n, z), s, s1, Wr.put_nat(base, s2), pre, e), f, Wr.get_nat(s2), SX.sx.nat(s2))
    case Wr.Bad{}:
      Unit{}

def axe.req_of(t: Nat, -s: String, +s1: String, pre: {s == Wr.put_nat(t, s1) : String}) -> axe.QP(s, FA.get_req(Wr.Got{t, s1})):
  match t:
    case 0n:
      axe.out_ran(s, s1, pre, Wr.get_bool(s1), SX.sx.bool(s1))
    case 1n:
      axe.lab_l(s, s1, pre, FS.get_vlabel(Wr.get_nat(s1)), SX.sx.vlabel_tag(s1, Wr.get_nat(s1), SX.sx.nat(s1)))
    case 2n:
      axe.ex_base(s, s1, pre, Wr.get_nat(s1), SX.sx.nat(s1))
    case 3n+u:
      Unit{}

def axe.req_tag(-s: String, d: Wr.Dec<Nat>, np: SX.sx.NP(s, d)) -> axe.QP(s, FA.get_req(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = np
      axe.req_of(t, s, s1, e)
    case Wr.Bad{}:
      Unit{}

# the request reader accepts only a spelled request that fits, before the
# rest of the input
def axe.req(+s: String) -> axe.QP(s, FA.get_req(Wr.get_nat(s))):
  axe.req_tag(s, Wr.get_nat(s), SX.sx.nat(s))

# The answer
# ----------

def axe.reply_ok(q: FA.Req) -> {LawsBase.wire_opens_err(SAW.w_reply(q)) == False{} : Bool}:
  match q:
    case FA.QOutcome{r}:
      Wire.wire_nat_not_err(SAW.w_outcome(At.outcome(r)), "")
    case FA.QLabel{l, now, gs, os}:
      Wire.wire_nat_not_err(SSW.w_label(At.label(l, now, gs, os)), "")
    case FA.QExit{base, now, slots, gs, os}:
      Wire.wire_nat_not_err(At.exit(base, now, slots, gs, os), "")

# the entry's answer to a request never opens with 'E'
def axe.answer_ok(+q: FA.Req) -> {LawsBase.wire_opens_err(FA.answer(q)) == False{} : Bool}:
  %Equal.sym(String, FA.answer(q), SAW.w_reply(q), LE.ae.answer(q)) : {LawsBase.wire_opens_err(_) == False{} : Bool}
  axe.reply_ok(q)
