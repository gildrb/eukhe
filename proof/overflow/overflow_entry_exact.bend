# eukhe: the proof of LAW overflow_entry_exact
#
# PROOF: each decoder stage of bend/ffi_overflow.bend answers Got{x, rest}
# only for an input that is the spec's spelling of what it read so far
# before rest, every number and length within the wire (ovx.*: the stage
# carries `pre`, the input spelled up to its field, and extends it with
# its field's exactness law: wire_nat_exact and wire_nat_decoded_fits,
# wire_str_exact and the length fits of LE.dcw.str). The entry answers a
# value only for a request read whole with nothing left: that input is the
# spelled request (ovx.top).

import Base
import ../../bend/text_pat.bend as Tp
import ../../bend/overflow.bend as O
import ../../bend/ffi_overflow.bend as FO
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/text_pat.bend as TextPat
import ../../laws/overflow.bend as Overflow
import ../base/staging.bend as LStg
import ../base/bool.bend as LBool
import ../base/wire_dec.bend as LE

def ovx.RP(s: String, d: Wr.Dec<FO.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == Overflow.sp_w_req(q, r) : String} & {Overflow.sp_fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ovx.STP(s: String, d: Wr.Dec<O.Stop>) -> Type:
  match d:
    case Wr.Got{st, r}:
      {s == Overflow.sp_w_stop(st, r) : String}
    case Wr.Bad{}:
      Unit

def ovx.stop.at(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> ovx.STP(s, FO.get_stop.tag(d)):
  match d:
    case Wr.Got{+t, +r}:
      match t:
        case 0n:
          Wire.wire_nat_exact(s, 0n, r, ed)
        case 1n:
          Wire.wire_nat_exact(s, 1n, r, ed)
        case 2n:
          Wire.wire_nat_exact(s, 2n, r, ed)
        case 3n:
          Wire.wire_nat_exact(s, 3n, r, ed)
        case 4n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a stop decoded is spelled
def ovx.stop(+s: String) -> ovx.STP(s, FO.get_stop(s)):
  ovx.stop.at(s, Wr.get_nat(s), {==})

def ovx.ov.o(-s: String, +st: O.Stop, +m: String, +p: String, +w: Nat, +i: Nat, +c: Nat, +s6: String, pre: {s == Wr.put_nat(0n, Overflow.sp_w_stop(st, Wr.put_str(m, Wr.put_str(p, Wr.put_nat(w, Wr.put_nat(i, Wr.put_nat(c, s6))))))) : String}, fm: {LawsBase.wire_fits(String.length(m)) == True{} : Bool}, fp: {LawsBase.wire_fits(String.length(p)) == True{} : Bool}, fw: {LawsBase.wire_fits(w) == True{} : Bool}, fi: {LawsBase.wire_fits(i) == True{} : Bool}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s6) == d : Wr.Dec<Nat>}) -> ovx.RP(s, FO.get_ov.output(st, m, p, w, i, c, d)):
  match d:
    case Wr.Got{+o, +r}:
      +ee = ed
      +e = Wire.wire_nat_exact(s6, o, r, ee)
      +fo = Wire.wire_nat_decoded_fits(s6, o, r, ee)
      (Equal.trans(String, s, Wr.put_nat(0n, Overflow.sp_w_stop(st, Wr.put_str(m, Wr.put_str(p, Wr.put_nat(w, Wr.put_nat(i, Wr.put_nat(c, s6))))))), Wr.put_nat(0n, Overflow.sp_w_stop(st, Wr.put_str(m, Wr.put_str(p, Wr.put_nat(w, Wr.put_nat(i, Wr.put_nat(c, Wr.put_nat(o, r)))))))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Overflow.sp_w_stop(st, Wr.put_str(m, Wr.put_str(p, Wr.put_nat(w, Wr.put_nat(i, Wr.put_nat(c, z))))))), s6, Wr.put_nat(o, r), e)), LBool.cb_and_intro(LawsBase.wire_fits(String.length(m)), Bool.and(LawsBase.wire_fits(String.length(p)), Bool.and(LawsBase.wire_fits(w), Bool.and(LawsBase.wire_fits(i), Bool.and(LawsBase.wire_fits(c), LawsBase.wire_fits(o))))), fm, LBool.cb_and_intro(LawsBase.wire_fits(String.length(p)), Bool.and(LawsBase.wire_fits(w), Bool.and(LawsBase.wire_fits(i), Bool.and(LawsBase.wire_fits(c), LawsBase.wire_fits(o)))), fp, LBool.cb_and_intro(LawsBase.wire_fits(w), Bool.and(LawsBase.wire_fits(i), Bool.and(LawsBase.wire_fits(c), LawsBase.wire_fits(o))), fw, LBool.cb_and_intro(LawsBase.wire_fits(i), Bool.and(LawsBase.wire_fits(c), LawsBase.wire_fits(o)), fi, LBool.cb_and_intro(LawsBase.wire_fits(c), LawsBase.wire_fits(o), fc, fo))))))
    case Wr.Bad{}:
      Unit{}

def ovx.ov.c(-s: String, +st: O.Stop, +m: String, +p: String, +w: Nat, +i: Nat, +s5: String, pre: {s == Wr.put_nat(0n, Overflow.sp_w_stop(st, Wr.put_str(m, Wr.put_str(p, Wr.put_nat(w, Wr.put_nat(i, s5)))))) : String}, fm: {LawsBase.wire_fits(String.length(m)) == True{} : Bool}, fp: {LawsBase.wire_fits(String.length(p)) == True{} : Bool}, fw: {LawsBase.wire_fits(w) == True{} : Bool}, fi: {LawsBase.wire_fits(i) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s5) == d : Wr.Dec<Nat>}) -> ovx.RP(s, FO.get_ov.cache(st, m, p, w, i, d)):
  match d:
    case Wr.Got{+c, +r}:
      +ee = ed
      +e = Wire.wire_nat_exact(s5, c, r, ee)
      +fc = Wire.wire_nat_decoded_fits(s5, c, r, ee)
      ovx.ov.o(s, st, m, p, w, i, c, r, Equal.trans(String, s, Wr.put_nat(0n, Overflow.sp_w_stop(st, Wr.put_str(m, Wr.put_str(p, Wr.put_nat(w, Wr.put_nat(i, s5)))))), Wr.put_nat(0n, Overflow.sp_w_stop(st, Wr.put_str(m, Wr.put_str(p, Wr.put_nat(w, Wr.put_nat(i, Wr.put_nat(c, r))))))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Overflow.sp_w_stop(st, Wr.put_str(m, Wr.put_str(p, Wr.put_nat(w, Wr.put_nat(i, z)))))), s5, Wr.put_nat(c, r), e)), fm, fp, fw, fi, fc, Wr.get_nat(r), {==})
    case Wr.Bad{}:
      Unit{}

def ovx.ov.i(-s: String, +st: O.Stop, +m: String, +p: String, +w: Nat, +s4: String, pre: {s == Wr.put_nat(0n, Overflow.sp_w_stop(st, Wr.put_str(m, Wr.put_str(p, Wr.put_nat(w, s4))))) : String}, fm: {LawsBase.wire_fits(String.length(m)) == True{} : Bool}, fp: {LawsBase.wire_fits(String.length(p)) == True{} : Bool}, fw: {LawsBase.wire_fits(w) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s4) == d : Wr.Dec<Nat>}) -> ovx.RP(s, FO.get_ov.input(st, m, p, w, d)):
  match d:
    case Wr.Got{+i, +r}:
      +ee = ed
      +e = Wire.wire_nat_exact(s4, i, r, ee)
      +fi = Wire.wire_nat_decoded_fits(s4, i, r, ee)
      ovx.ov.c(s, st, m, p, w, i, r, Equal.trans(String, s, Wr.put_nat(0n, Overflow.sp_w_stop(st, Wr.put_str(m, Wr.put_str(p, Wr.put_nat(w, s4))))), Wr.put_nat(0n, Overflow.sp_w_stop(st, Wr.put_str(m, Wr.put_str(p, Wr.put_nat(w, Wr.put_nat(i, r)))))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Overflow.sp_w_stop(st, Wr.put_str(m, Wr.put_str(p, Wr.put_nat(w, z))))), s4, Wr.put_nat(i, r), e)), fm, fp, fw, fi, Wr.get_nat(r), {==})
    case Wr.Bad{}:
      Unit{}

def ovx.ov.w(-s: String, +st: O.Stop, +m: String, +p: String, +s3: String, pre: {s == Wr.put_nat(0n, Overflow.sp_w_stop(st, Wr.put_str(m, Wr.put_str(p, s3)))) : String}, fm: {LawsBase.wire_fits(String.length(m)) == True{} : Bool}, fp: {LawsBase.wire_fits(String.length(p)) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s3) == d : Wr.Dec<Nat>}) -> ovx.RP(s, FO.get_ov.window(st, m, p, d)):
  match d:
    case Wr.Got{+w, +r}:
      +ee = ed
      +e = Wire.wire_nat_exact(s3, w, r, ee)
      +fw = Wire.wire_nat_decoded_fits(s3, w, r, ee)
      ovx.ov.i(s, st, m, p, w, r, Equal.trans(String, s, Wr.put_nat(0n, Overflow.sp_w_stop(st, Wr.put_str(m, Wr.put_str(p, s3)))), Wr.put_nat(0n, Overflow.sp_w_stop(st, Wr.put_str(m, Wr.put_str(p, Wr.put_nat(w, r))))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Overflow.sp_w_stop(st, Wr.put_str(m, Wr.put_str(p, z)))), s3, Wr.put_nat(w, r), e)), fm, fp, fw, Wr.get_nat(r), {==})
    case Wr.Bad{}:
      Unit{}

def ovx.ov.p(-s: String, +st: O.Stop, +m: String, +s2: String, pre: {s == Wr.put_nat(0n, Overflow.sp_w_stop(st, Wr.put_str(m, s2))) : String}, fm: {LawsBase.wire_fits(String.length(m)) == True{} : Bool}, d: Wr.Dec<String>, sp: LE.dcw.SP(s2, d)) -> ovx.RP(s, FO.get_ov.provider(st, m, d)):
  match d:
    case Wr.Got{+p, +r}:
      (e, fp) = sp
      ovx.ov.w(s, st, m, p, r, Equal.trans(String, s, Wr.put_nat(0n, Overflow.sp_w_stop(st, Wr.put_str(m, s2))), Wr.put_nat(0n, Overflow.sp_w_stop(st, Wr.put_str(m, Wr.put_str(p, r)))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Overflow.sp_w_stop(st, Wr.put_str(m, z))), s2, Wr.put_str(p, r), e)), fm, fp, Wr.get_nat(r), {==})
    case Wr.Bad{}:
      Unit{}

def ovx.ov.m(-s: String, +st: O.Stop, +s1: String, pre: {s == Wr.put_nat(0n, Overflow.sp_w_stop(st, s1)) : String}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> ovx.RP(s, FO.get_ov.msg(st, d)):
  match d:
    case Wr.Got{+m, +r}:
      (e, fm) = sp
      ovx.ov.p(s, st, m, r, Equal.trans(String, s, Wr.put_nat(0n, Overflow.sp_w_stop(st, s1)), Wr.put_nat(0n, Overflow.sp_w_stop(st, Wr.put_str(m, r))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Overflow.sp_w_stop(st, z)), s1, Wr.put_str(m, r), e)), fm, Wr.get_str(r), LE.dcw.str(r))
    case Wr.Bad{}:
      Unit{}

def ovx.ov(-s: String, +s0: String, pre: {s == Wr.put_nat(0n, s0) : String}, d: Wr.Dec<O.Stop>, stp: ovx.STP(s0, d)) -> ovx.RP(s, FO.get_ov(d)):
  match d:
    case Wr.Got{+st, +r}:
      ovx.ov.m(s, st, r, Equal.trans(String, s, Wr.put_nat(0n, s0), Wr.put_nat(0n, Overflow.sp_w_stop(st, r)), pre, Equal.cong(String, String, z => Wr.put_nat(0n, z), s0, Overflow.sp_w_stop(st, r), stp)), Wr.get_str(r), LE.dcw.str(r))
    case Wr.Bad{}:
      Unit{}


def ovx.rc.o(-s: String, +st: O.Stop, +ds: Nat, +s2: String, pre: {s == Wr.put_nat(1n, Overflow.sp_w_stop(st, Wr.put_nat(ds, s2))) : String}, fds: {LawsBase.wire_fits(ds) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}) -> ovx.RP(s, FO.get_rc.output(st, ds, d)):
  match d:
    case Wr.Got{+o, +r}:
      +ee = ed
      +e = Wire.wire_nat_exact(s2, o, r, ee)
      +fo = Wire.wire_nat_decoded_fits(s2, o, r, ee)
      (Equal.trans(String, s, Wr.put_nat(1n, Overflow.sp_w_stop(st, Wr.put_nat(ds, s2))), Wr.put_nat(1n, Overflow.sp_w_stop(st, Wr.put_nat(ds, Wr.put_nat(o, r)))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, Overflow.sp_w_stop(st, Wr.put_nat(ds, z))), s2, Wr.put_nat(o, r), e)), LBool.cb_and_intro(LawsBase.wire_fits(ds), LawsBase.wire_fits(o), fds, fo))
    case Wr.Bad{}:
      Unit{}

def ovx.rc.ds(-s: String, +st: O.Stop, +s1: String, pre: {s == Wr.put_nat(1n, Overflow.sp_w_stop(st, s1)) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> ovx.RP(s, FO.get_rc.desired(st, d)):
  match d:
    case Wr.Got{+ds, +r}:
      +ee = ed
      +e = Wire.wire_nat_exact(s1, ds, r, ee)
      +fds = Wire.wire_nat_decoded_fits(s1, ds, r, ee)
      ovx.rc.o(s, st, ds, r, Equal.trans(String, s, Wr.put_nat(1n, Overflow.sp_w_stop(st, s1)), Wr.put_nat(1n, Overflow.sp_w_stop(st, Wr.put_nat(ds, r))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, Overflow.sp_w_stop(st, z)), s1, Wr.put_nat(ds, r), e)), fds, Wr.get_nat(r), {==})
    case Wr.Bad{}:
      Unit{}

def ovx.rc(-s: String, +s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<O.Stop>, stp: ovx.STP(s0, d)) -> ovx.RP(s, FO.get_rc(d)):
  match d:
    case Wr.Got{+st, +r}:
      ovx.rc.ds(s, st, r, Equal.trans(String, s, Wr.put_nat(1n, s0), Wr.put_nat(1n, Overflow.sp_w_stop(st, r)), pre, Equal.cong(String, String, z => Wr.put_nat(1n, z), s0, Overflow.sp_w_stop(st, r), stp)), Wr.get_nat(r), {==})
    case Wr.Bad{}:
      Unit{}


def ovx.tag(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> ovx.RP(s, FO.get_req.tag(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          ovx.ov(s, s0, Wire.wire_nat_exact(s, 0n, s0, ed), FO.get_stop(s0), ovx.stop(s0))
        case 1n:
          ovx.rc(s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), FO.get_stop(s0), ovx.stop(s0))
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a value answered: a request read whole, nothing left
def ovx.top(-s: String, d: Wr.Dec<FO.Req>, rp: ovx.RP(s, d), ok: {LawsBase.wire_opens_err(FO.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, FO.Req, r => {s == Overflow.sp_w_req(r, "") : String} & {Overflow.sp_fit_req(r) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{x, y}:
          LStg.stg.absurd(Sigma<&1, &1, FO.Req, r2 => {s == Overflow.sp_w_req(r2, "") : String} & {Overflow.sp_fit_req(r2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LStg.stg.absurd(Sigma<&1, &1, FO.Req, r2 => {s == Overflow.sp_w_req(r2, "") : String} & {Overflow.sp_fit_req(r2) == True{} : Bool}>, ok)

def Overflow.overflow_entry_exact(s, ok):
  ovx.top(s, FO.get_req(s), ovx.tag(s, Wr.get_nat(s), {==}), ok)
