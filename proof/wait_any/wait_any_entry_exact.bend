# eukhe: the proof of LAW wait_any_entry_exact
#
# PROOF: each decoder stage of bend/ffi_wait_any.bend answers Got{x,
# rest} only for an input that is the grammar's spelling of x before
# rest, with every Nat of x within the wire (wx.*: a predicate per decoder
# answer, carried stage by stage with wire_nat_exact, wire_bool_exact,
# wire_list_exact and wire_nat_decoded_fits; a target, phase or event
# read is the code SpW spells for it: wx.tg, wx.ph, wx.ev). The entry
# answers a value only for a request read whole with nothing left: that
# input is the spelled request (wx.top).

import Base
import ../../bend/wait_any.bend as Wa
import ../../bend/ffi_wait_any.bend as FWa
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/wait_any.bend as WaitAny
import ../../spec/durable/wait_any_wire.bend as SpW
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../wire/wire_list_exact.bend as PWireListExact
import ../wire_ffi/base.bend as LWF
import ../base/staging.bend as LStg
import ./base.bend as LW

# what a decoder answer says about the input s
def wx.RP(s: String, d: Wr.Dec<FWa.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == SpW.w_req(q, r) : String} & {SpW.fit(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# s is f(a) and a is b: s is f(b)
def wx.then(-s: String, -f: String -> String, -a: String, -b: String, pre: {s == f(a) : String}, e: {a == b : String}) -> {s == f(b) : String}:
  Equal.trans(String, s, f(a), f(b), pre, Equal.cong(String, String, f, a, b, e))

# s is f(a) and the codes a are b: s is f(b)
def wx.then_ns(-s: String, -f: List<&2, Nat> -> String, -a: List<&2, Nat>, -b: List<&2, Nat>, pre: {s == f(a) : String}, e: {a == b : List<&2, Nat>}) -> {s == f(b) : String}:
  Equal.trans(String, s, f(a), f(b), pre, Equal.cong(List<&2, Nat>, String, f, a, b, e))

# s is f(a) and the code a is b: s is f(b)
def wx.then_n(-s: String, -f: Nat -> String, -a: Nat, -b: Nat, pre: {s == f(a) : String}, e: {a == b : Nat}) -> {s == f(b) : String}:
  Equal.trans(String, s, f(a), f(b), pre, Equal.cong(Nat, String, f, a, b, e))

def wx.and_l(a: Bool, b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

# Codes read
# ----------

def wx.TG(n: Nat, m: Maybe<&2, Wa.Tgt>) -> Type:
  match m:
    case Some{x}:
      {n == SpW.c_tgt(x) : Nat}
    case None{}:
      Unit

def wx.tg(n: Nat) -> wx.TG(n, FWa.tgt_of(n)):
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n+k:
      Unit{}

def wx.TC(ns: List<&2, Nat>, m: Maybe<&2, List<&2, Wa.Tgt>>) -> Type:
  match m:
    case Some{xs}:
      {ns == SpW.c_tgts(xs) : List<&2, Nat>}
    case None{}:
      Unit

def wx.tc_cons(+n: Nat, +rest: List<&2, Nat>, a: Maybe<&2, Wa.Tgt>, ta: wx.TG(n, a), r: Maybe<&2, List<&2, Wa.Tgt>>, tr: wx.TC(rest, r)) -> wx.TC(n <> rest, FWa.tgts.cons(a, r)):
  match a:
    case Some{x}:
      match r:
        case Some{xs}:
          %ta : {n <> rest == _ <> SpW.c_tgts(xs) : List<&2, Nat>}
          %tr : {n <> rest == n <> _ : List<&2, Nat>}
          {==}
        case None{}:
          Unit{}
    case None{}:
      Unit{}

# targets read are the targets whose codes ns are
def wx.tc(ns: List<&2, Nat>) -> wx.TC(ns, FWa.tgts(ns)):
  match ns:
    case Nil{}:
      {==}
    case Con{+n, +rest}:
      wx.tc_cons(n, rest, FWa.tgt_of(n), wx.tg(n), FWa.tgts(rest), wx.tc(rest))

def wx.PH(n: Nat, m: Maybe<&2, Wa.Phase>) -> Type:
  match m:
    case Some{x}:
      {n == SpW.c_phase(x) : Nat}
    case None{}:
      Unit

def wx.ph(n: Nat) -> wx.PH(n, FWa.phase_of(n)):
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n+k:
      Unit{}

def wx.EV(n: Nat, m: Maybe<&2, Wa.Ev>) -> Type:
  match m:
    case Some{x}:
      {n == SpW.c_ev(x) : Nat}
    case None{}:
      Unit

def wx.ev(n: Nat) -> wx.EV(n, FWa.ev_of(n)):
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n+k:
      Unit{}

# the codes ns of targets xs: as many targets as codes, so the count fits
def wx.len_fits(+ns: List<&2, Nat>, +xs: List<&2, Wa.Tgt>, e: {ns == SpW.c_tgts(xs) : List<&2, Nat>}, f: {LawsBase.wire_fits(List.length(&2, Nat, ns)) == True{} : Bool}) -> {LawsBase.wire_fits(List.length(&2, Wa.Tgt, xs)) == True{} : Bool}:
  +len = Equal.trans(Nat, List.length(&2, Wa.Tgt, xs), List.length(&2, Nat, SpW.c_tgts(xs)), List.length(&2, Nat, ns), Equal.sym(Nat, List.length(&2, Nat, SpW.c_tgts(xs)), List.length(&2, Wa.Tgt, xs), LW.wa.tgts_len(xs)), Equal.cong(List<&2, Nat>, Nat, z => List.length(&2, Nat, z), SpW.c_tgts(xs), ns, Equal.sym(List<&2, Nat>, ns, SpW.c_tgts(xs), e)))
  Equal.trans(Bool, LawsBase.wire_fits(List.length(&2, Wa.Tgt, xs)), LawsBase.wire_fits(List.length(&2, Nat, ns)), True{}, Equal.cong(Nat, Bool, z => LawsBase.wire_fits(z), List.length(&2, Wa.Tgt, xs), List.length(&2, Nat, ns), len), f)

# A poll
# ------

def wx.P1(n: Bool, s: String) -> String:
  Wr.put_nat(0n, Wr.put_bool(n, s))

def wx.P2(n: Bool, c: Bool, s: String) -> String:
  Wr.put_nat(0n, Wr.put_bool(n, Wr.put_bool(c, s)))

def wx.P3(n: Bool, c: Bool, l: Bool, s: String) -> String:
  Wr.put_nat(0n, Wr.put_bool(n, Wr.put_bool(c, Wr.put_bool(l, s))))

def wx.poll.ok(-s: String, +n: Bool, +c: Bool, +l: Bool, +ns: List<&2, Nat>, +s5: String, pre: {s == wx.P3(n, c, l, Wr.put_list(~Nat, ~Wr.put_nat, ns, s5)) : String}, fns: {LawsBase.wire_fits(List.length(&2, Nat, ns)) == True{} : Bool}, m: Maybe<&2, List<&2, Wa.Tgt>>, tc: wx.TC(ns, m), t2: wx.TC(ns, m)) -> wx.RP(s, FWa.get_poll.ok(n, c, l, m, s5)):
  match m:
    case Some{+xs}:
      (wx.then_ns(s, z => wx.P3(n, c, l, Wr.put_list(~Nat, ~Wr.put_nat, z, s5)), ns, SpW.c_tgts(xs), pre, tc), wx.len_fits(ns, xs, t2, fns))
    case None{}:
      Unit{}

def wx.poll.ts(-s: String, +n: Bool, +c: Bool, +l: Bool, +s4: String, pre: {s == wx.P3(n, c, l, s4) : String}, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s4) == d : Wr.Dec<List<&2, Nat>>}) -> wx.RP(s, FWa.get_poll.ts(n, c, l, d)):
  match d:
    case Wr.Got{+ns, +s5}:
      +e2 = ed
      +fits = LWF.wrb.nats_fit(s4, ns, s5, e2)
      wx.poll.ok(s, n, c, l, ns, s5, wx.then(s, z => wx.P3(n, c, l, z), s4, Wr.put_list(~Nat, ~Wr.put_nat, ns, s5), pre, Wire.wire_list_exact(s4, ns, s5, e2)), wx.and_l(LawsBase.wire_fits(List.length(&2, Nat, ns)), LawsBase.wire_nats_fit(ns), fits), FWa.tgts(ns), wx.tc(ns), wx.tc(ns))
    case Wr.Bad{}:
      Unit{}

def wx.poll.late(-s: String, +n: Bool, +c: Bool, +s3: String, pre: {s == wx.P2(n, c, s3) : String}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s3) == d : Wr.Dec<Bool>}) -> wx.RP(s, FWa.get_poll.late(n, c, d)):
  match d:
    case Wr.Got{+l, +s4}:
      wx.poll.ts(s, n, c, l, s4, wx.then(s, z => wx.P2(n, c, z), s3, Wr.put_bool(l, s4), pre, Wire.wire_bool_exact(s3, l, s4, ed)), Wr.get_list(~Nat, ~Wr.get_nat, s4), {==})
    case Wr.Bad{}:
      Unit{}

def wx.poll.cancel(-s: String, +n: Bool, +s2: String, pre: {s == wx.P1(n, s2) : String}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s2) == d : Wr.Dec<Bool>}) -> wx.RP(s, FWa.get_poll.cancel(n, d)):
  match d:
    case Wr.Got{+c, +s3}:
      wx.poll.late(s, n, c, s3, wx.then(s, z => wx.P1(n, z), s2, Wr.put_bool(c, s3), pre, Wire.wire_bool_exact(s2, c, s3, ed)), Wr.get_bool(s3), {==})
    case Wr.Bad{}:
      Unit{}

def wx.poll(-s: String, +s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s1) == d : Wr.Dec<Bool>}) -> wx.RP(s, FWa.get_poll(d)):
  match d:
    case Wr.Got{+n, +s2}:
      wx.poll.cancel(s, n, s2, wx.then(s, z => Wr.put_nat(0n, z), s1, Wr.put_bool(n, s2), pre, Wire.wire_bool_exact(s1, n, s2, ed)), Wr.get_bool(s2), {==})
    case Wr.Bad{}:
      Unit{}

# A step
# ------

def wx.S1(k: Bool, s: String) -> String:
  Wr.put_nat(1n, Wr.put_bool(k, s))

def wx.S2(k: Bool, w: Nat, s: String) -> String:
  Wr.put_nat(1n, Wr.put_bool(k, Wr.put_nat(w, s)))

def wx.S3(k: Bool, w: Nat, p: Nat, s: String) -> String:
  Wr.put_nat(1n, Wr.put_bool(k, Wr.put_nat(w, Wr.put_nat(p, s))))

def wx.S4(k: Bool, w: Nat, p: Nat, e: Nat, s: String) -> String:
  Wr.put_nat(1n, Wr.put_bool(k, Wr.put_nat(w, Wr.put_nat(p, Wr.put_nat(e, s)))))

def wx.step.ok(-s: String, +k: Bool, +w: Nat, +p: Nat, +e: Nat, +s5: String, pre: {s == wx.S4(k, w, p, e, s5) : String}, fw: {LawsBase.wire_fits(w) == True{} : Bool}, mp: Maybe<&2, Wa.Phase>, tp: wx.PH(p, mp), me: Maybe<&2, Wa.Ev>, te: wx.EV(e, me)) -> wx.RP(s, FWa.get_step.ok(k, w, mp, me, s5)):
  match mp:
    case Some{+ph}:
      match me:
        case Some{+ev}:
          +e1 = wx.then_n(s, z => wx.S4(k, w, z, e, s5), p, SpW.c_phase(ph), pre, tp)
          (wx.then_n(s, z => wx.S4(k, w, SpW.c_phase(ph), z, s5), e, SpW.c_ev(ev), e1, te), fw)
        case None{}:
          Unit{}
    case None{}:
      Unit{}

def wx.step.ev(-s: String, +k: Bool, +w: Nat, +p: Nat, +s4: String, pre: {s == wx.S3(k, w, p, s4) : String}, fw: {LawsBase.wire_fits(w) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s4) == d : Wr.Dec<Nat>}) -> wx.RP(s, FWa.get_step.ev(k, w, p, d)):
  match d:
    case Wr.Got{+e, +s5}:
      wx.step.ok(s, k, w, p, e, s5, wx.then(s, z => wx.S3(k, w, p, z), s4, Wr.put_nat(e, s5), pre, Wire.wire_nat_exact(s4, e, s5, ed)), fw, FWa.phase_of(p), wx.ph(p), FWa.ev_of(e), wx.ev(e))
    case Wr.Bad{}:
      Unit{}

def wx.step.phase(-s: String, +k: Bool, +w: Nat, +s3: String, pre: {s == wx.S2(k, w, s3) : String}, fw: {LawsBase.wire_fits(w) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s3) == d : Wr.Dec<Nat>}) -> wx.RP(s, FWa.get_step.phase(k, w, d)):
  match d:
    case Wr.Got{+p, +s4}:
      wx.step.ev(s, k, w, p, s4, wx.then(s, z => wx.S2(k, w, z), s3, Wr.put_nat(p, s4), pre, Wire.wire_nat_exact(s3, p, s4, ed)), fw, Wr.get_nat(s4), {==})
    case Wr.Bad{}:
      Unit{}

def wx.step.watchers(-s: String, +k: Bool, +s2: String, pre: {s == wx.S1(k, s2) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}) -> wx.RP(s, FWa.get_step.watchers(k, d)):
  match d:
    case Wr.Got{+w, +s3}:
      +e2 = ed
      wx.step.phase(s, k, w, s3, wx.then(s, z => wx.S1(k, z), s2, Wr.put_nat(w, s3), pre, Wire.wire_nat_exact(s2, w, s3, e2)), Wire.wire_nat_decoded_fits(s2, w, s3, e2), Wr.get_nat(s3), {==})
    case Wr.Bad{}:
      Unit{}

def wx.step(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s1) == d : Wr.Dec<Bool>}) -> wx.RP(s, FWa.get_step(d)):
  match d:
    case Wr.Got{+k, +s2}:
      wx.step.watchers(s, k, s2, wx.then(s, z => Wr.put_nat(1n, z), s1, Wr.put_bool(k, s2), pre, Wire.wire_bool_exact(s1, k, s2, ed)), Wr.get_nat(s2), {==})
    case Wr.Bad{}:
      Unit{}

# A timeout
# ---------

def wx.secs(-s: String, +s2: String, pre: {s == Wr.put_nat(2n, Wr.put_nat(1n, s2)) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}) -> wx.RP(s, FWa.get_timeout.ms(d)):
  match d:
    case Wr.Got{+t, +s3}:
      +e2 = ed
      (wx.then(s, z => Wr.put_nat(2n, Wr.put_nat(1n, z)), s2, Wr.put_nat(t, s3), pre, Wire.wire_nat_exact(s2, t, s3, e2)), Wire.wire_nat_decoded_fits(s2, t, s3, e2))
    case Wr.Bad{}:
      Unit{}

def wx.timeout(-s: String, +s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> wx.RP(s, FWa.get_timeout(d)):
  match d:
    case Wr.Got{+t, +s2}:
      match t:
        case 0n:
          (wx.then(s, z => Wr.put_nat(2n, z), s1, Wr.put_nat(0n, s2), pre, Wire.wire_nat_exact(s1, 0n, s2, ed)), {==})
        case 1n:
          wx.secs(s, s2, wx.then(s, z => Wr.put_nat(2n, z), s1, Wr.put_nat(1n, s2), pre, Wire.wire_nat_exact(s1, 1n, s2, ed)), Wr.get_nat(s2), {==})
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# The request
# -----------

def wx.tag(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> wx.RP(s, FWa.get_req.start(d)):
  match d:
    case Wr.Got{+t, +s1}:
      match t:
        case 0n:
          wx.poll(s, s1, Wire.wire_nat_exact(s, 0n, s1, ed), Wr.get_bool(s1), {==})
        case 1n:
          wx.step(s, s1, Wire.wire_nat_exact(s, 1n, s1, ed), Wr.get_bool(s1), {==})
        case 2n:
          wx.timeout(s, s1, Wire.wire_nat_exact(s, 2n, s1, ed), Wr.get_nat(s1), {==})
        case 3n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a value answered: a request read whole, nothing left
def wx.top(-s: String, d: Wr.Dec<FWa.Req>, rp: wx.RP(s, d), ok: {LawsBase.wire_opens_err(FWa.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, FWa.Req, q => {s == SpW.w_req(q, "") : String} & {SpW.fit(q) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{x, y}:
          LStg.stg.absurd(Sigma<&1, &1, FWa.Req, q2 => {s == SpW.w_req(q2, "") : String} & {SpW.fit(q2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LStg.stg.absurd(Sigma<&1, &1, FWa.Req, q2 => {s == SpW.w_req(q2, "") : String} & {SpW.fit(q2) == True{} : Bool}>, ok)

def WaitAny.wait_any_entry_exact(s, ok):
  wx.top(s, FWa.get_req(s), wx.tag(s, Wr.get_nat(s), {==}), ok)
