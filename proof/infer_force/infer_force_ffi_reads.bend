# eukhe: the proof of LAW infer_force_ffi_reads
#
# PROOF: each decoder stage answers Got only for the spelling of its
# value, within the wire (Wire.wire_nat_exact, wire_nat_decoded_fits,
# wire_bool_exact): a request decoded is spelled (rd.req); the entry
# answers a value only for a request read whole, nothing left (rd.top).

import Base
import ../../bend/ffi_infer_force.bend as FF
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/infer_force.bend as InferForce

def rd.BD(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# a False that is True proves anything
def rd.absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : rd.BD(_, G)
  Unit{}

# both are True: so is their and
def rd.both(+a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      rd.absurd({Bool.and(False{}, b) == True{} : Bool}, ea)

# the request q, then rest
def rd.spell(q: FF.Req, rest: String) -> String:
  match q:
    case FF.QFlag{i, sup, free}:
      Wr.put_nat(0n, Wr.put_nat(i, Wr.put_bool(sup, Wr.put_bool(free, rest))))
    case FF.QAfter{i, r, c}:
      Wr.put_nat(1n, Wr.put_nat(i, Wr.put_nat(r, Wr.put_bool(c, rest))))

# a decoded request is spelled, and fits
def rd.RP(s: String, x: Wr.Dec<FF.Req>) -> Type:
  match x:
    case Wr.Got{q, rr}:
      {s == rd.spell(q, rr) : String} & {InferForce.ask_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rd.free(-s: String, +i: Nat, +sup: Bool, +s3: String, pre: {s == Wr.put_nat(0n, Wr.put_nat(i, Wr.put_bool(sup, s3))) : String}, fi: {LawsBase.wire_fits(i) == True{} : Bool}, x: Wr.Dec<Bool>, ed: {Wr.get_bool(s3) == x : Wr.Dec<Bool>}) -> rd.RP(s, FF.get_flag.free(i, sup, x)):
  match x:
    case Wr.Got{+free, +s4}:
      +e = ed
      +eb = Wire.wire_bool_exact(s3, free, s4, e)
      (Equal.trans(String, s, Wr.put_nat(0n, Wr.put_nat(i, Wr.put_bool(sup, s3))), Wr.put_nat(0n, Wr.put_nat(i, Wr.put_bool(sup, Wr.put_bool(free, s4)))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_nat(i, Wr.put_bool(sup, z))), s3, Wr.put_bool(free, s4), eb)), fi)
    case Wr.Bad{}:
      Unit{}

def rd.sup(-s: String, +i: Nat, +s2: String, pre: {s == Wr.put_nat(0n, Wr.put_nat(i, s2)) : String}, fi: {LawsBase.wire_fits(i) == True{} : Bool}, x: Wr.Dec<Bool>, ed: {Wr.get_bool(s2) == x : Wr.Dec<Bool>}) -> rd.RP(s, FF.get_flag.sup(i, x)):
  match x:
    case Wr.Got{+sup, +s3}:
      +e = ed
      +eb = Wire.wire_bool_exact(s2, sup, s3, e)
      +pre2 = Equal.trans(String, s, Wr.put_nat(0n, Wr.put_nat(i, s2)), Wr.put_nat(0n, Wr.put_nat(i, Wr.put_bool(sup, s3))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_nat(i, z)), s2, Wr.put_bool(sup, s3), eb))
      rd.free(s, i, sup, s3, pre2, fi, Wr.get_bool(s3), {==})
    case Wr.Bad{}:
      Unit{}

def rd.flag(-s: String, +s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, x: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == x : Wr.Dec<Nat>}) -> rd.RP(s, FF.get_flag(x)):
  match x:
    case Wr.Got{+i, +s2}:
      +e = ed
      +ei = Wire.wire_nat_exact(s1, i, s2, e)
      +fi = Wire.wire_nat_decoded_fits(s1, i, s2, e)
      +pre2 = Equal.trans(String, s, Wr.put_nat(0n, s1), Wr.put_nat(0n, Wr.put_nat(i, s2)), pre, Equal.cong(String, String, z => Wr.put_nat(0n, z), s1, Wr.put_nat(i, s2), ei))
      rd.sup(s, i, s2, pre2, fi, Wr.get_bool(s2), {==})
    case Wr.Bad{}:
      Unit{}

def rd.called(-s: String, +i: Nat, +r: Nat, +s3: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(i, Wr.put_nat(r, s3))) : String}, fi: {LawsBase.wire_fits(i) == True{} : Bool}, fr: {LawsBase.wire_fits(r) == True{} : Bool}, x: Wr.Dec<Bool>, ed: {Wr.get_bool(s3) == x : Wr.Dec<Bool>}) -> rd.RP(s, FF.get_after.called(i, r, x)):
  match x:
    case Wr.Got{+c, +s4}:
      +e = ed
      +eb = Wire.wire_bool_exact(s3, c, s4, e)
      +pre2 = Equal.trans(String, s, Wr.put_nat(1n, Wr.put_nat(i, Wr.put_nat(r, s3))), Wr.put_nat(1n, Wr.put_nat(i, Wr.put_nat(r, Wr.put_bool(c, s4)))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_nat(i, Wr.put_nat(r, z))), s3, Wr.put_bool(c, s4), eb))
      (pre2, rd.both(LawsBase.wire_fits(i), LawsBase.wire_fits(r), fi, fr))
    case Wr.Bad{}:
      Unit{}

def rd.retries(-s: String, +i: Nat, +s2: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(i, s2)) : String}, fi: {LawsBase.wire_fits(i) == True{} : Bool}, x: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == x : Wr.Dec<Nat>}) -> rd.RP(s, FF.get_after.retries(i, x)):
  match x:
    case Wr.Got{+r, +s3}:
      +e = ed
      +er = Wire.wire_nat_exact(s2, r, s3, e)
      +fr = Wire.wire_nat_decoded_fits(s2, r, s3, e)
      +pre2 = Equal.trans(String, s, Wr.put_nat(1n, Wr.put_nat(i, s2)), Wr.put_nat(1n, Wr.put_nat(i, Wr.put_nat(r, s3))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_nat(i, z)), s2, Wr.put_nat(r, s3), er))
      rd.called(s, i, r, s3, pre2, fi, fr, Wr.get_bool(s3), {==})
    case Wr.Bad{}:
      Unit{}

def rd.after(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, x: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == x : Wr.Dec<Nat>}) -> rd.RP(s, FF.get_after(x)):
  match x:
    case Wr.Got{+i, +s2}:
      +e = ed
      +ei = Wire.wire_nat_exact(s1, i, s2, e)
      +fi = Wire.wire_nat_decoded_fits(s1, i, s2, e)
      +pre2 = Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_nat(i, s2)), pre, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_nat(i, s2), ei))
      rd.retries(s, i, s2, pre2, fi, Wr.get_nat(s2), {==})
    case Wr.Bad{}:
      Unit{}

def rd.tag(-s: String, t: Nat, +s1: String, pre: {s == Wr.put_nat(t, s1) : String}) -> rd.RP(s, FF.get_req.tag(t, s1)):
  match t:
    case 0n:
      rd.flag(s, s1, pre, Wr.get_nat(s1), {==})
    case 1n:
      rd.after(s, s1, pre, Wr.get_nat(s1), {==})
    case 2n+p:
      Unit{}

def rd.go(+s: String, x: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == x : Wr.Dec<Nat>}) -> rd.RP(s, FF.get_req.go(x)):
  match x:
    case Wr.Got{+t, +s1}:
      +e = ed
      rd.tag(s, t, s1, Wire.wire_nat_exact(s, t, s1, e))
    case Wr.Bad{}:
      Unit{}

# a request decoded is spelled, and fits
def rd.req(+s: String) -> rd.RP(s, FF.get_req(s)):
  rd.go(s, Wr.get_nat(s), {==})

def rd.T(s: String) -> Type:
  Sigma<&1, &1, FF.Req, q => {s == InferForce.spell_ask(q) : String} & {InferForce.ask_fits(q) == True{} : Bool}>

# the request read whole: its spelling with nothing after is spell_ask
def rd.whole(-s: String, q: FF.Req, rp: {s == rd.spell(q, "") : String} & {InferForce.ask_fits(q) == True{} : Bool}) -> rd.T(s):
  match q:
    case FF.QFlag{i, sup, free}:
      (FF.QFlag{i, sup, free}, rp)
    case FF.QAfter{i, r, c}:
      (FF.QAfter{i, r, c}, rp)

# a value answered: a request read whole, nothing left
def rd.top(-s: String, x: Wr.Dec<FF.Req>, rp: rd.RP(s, x), ok: {LawsBase.wire_opens_err(FF.run(x)) == False{} : Bool}) -> rd.T(s):
  match x:
    case Wr.Got{q, rest}:
      match rest:
        case SNil{}:
          rd.whole(s, q, rp)
        case SCon{y, z}:
          rd.absurd(rd.T(s), Equal.sym(Bool, True{}, False{}, ok))
    case Wr.Bad{}:
      rd.absurd(rd.T(s), Equal.sym(Bool, True{}, False{}, ok))

def InferForce.infer_force_ffi_reads(s, ok):
  rd.top(s, FF.get_req(s), rd.req(s), ok)
