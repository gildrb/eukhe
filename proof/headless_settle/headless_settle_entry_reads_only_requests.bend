# eukhe: the proof of LAW headless_settle_entry_reads_only_requests
#
# PROOF: each decoder stage of bend/ffi_headless_settle.bend answers
# Got{x, rest} only for an input that spells x before rest, every count
# within the wire (hso.*: a predicate per stage, carried with
# wire_bool_exact, wire_nat_exact and wire_nat_decoded_fits); a value is
# answered only for a request read whole, with nothing left (hso.top).

import Base
import ../../bend/headless_settle.bend as Hs
import ../../bend/ffi_headless_settle.bend as FHs
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/headless_settle.bend as HeadlessSettle
import ../../spec/durable/headless_wire.bend as SpW
import ../base/bool.bend as LBool
import ../base/staging.bend as LStg
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_bool_exact.bend as PWireBoolExact

def hso.RP(s: String, x: Wr.Dec<Hs.Facts>) -> Type:
  match x:
    case Wr.Got{f, rr}:
      {s == SpW.w_settle_req(f, rr) : String} & {SpW.fit_settle(f) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def hso.limit(-s: String, +b: Bool, +j: Nat, +k: Nat, +c: Nat, +w: Nat, +x: Nat, +u: Bool, +s7: String, pre: {s == Wr.put_bool(b, Wr.put_nat(j, Wr.put_nat(k, Wr.put_nat(c, Wr.put_nat(w, Wr.put_nat(x, Wr.put_bool(u, s7))))))) : String}, fj: {LawsBase.wire_fits(j) == True{} : Bool}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, fw: {LawsBase.wire_fits(w) == True{} : Bool}, fx: {LawsBase.wire_fits(x) == True{} : Bool}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s7) == d : Wr.Dec<Bool>}) -> hso.RP(s, FHs.get_facts.limit(b, j, k, c, w, x, u, d)):
  match d:
    case Wr.Got{+l, +s8}:
      +e = ed
      (Equal.trans(String, s, Wr.put_bool(b, Wr.put_nat(j, Wr.put_nat(k, Wr.put_nat(c, Wr.put_nat(w, Wr.put_nat(x, Wr.put_bool(u, s7))))))), Wr.put_bool(b, Wr.put_nat(j, Wr.put_nat(k, Wr.put_nat(c, Wr.put_nat(w, Wr.put_nat(x, Wr.put_bool(u, Wr.put_bool(l, s8)))))))), pre, Equal.cong(String, String, z => Wr.put_bool(b, Wr.put_nat(j, Wr.put_nat(k, Wr.put_nat(c, Wr.put_nat(w, Wr.put_nat(x, Wr.put_bool(u, z))))))), s7, Wr.put_bool(l, s8), Wire.wire_bool_exact(s7, l, s8, e))), LBool.cb_and_intro(LawsBase.wire_fits(j), Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(w), LawsBase.wire_fits(x)))), fj, LBool.cb_and_intro(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(w), LawsBase.wire_fits(x))), fk, LBool.cb_and_intro(LawsBase.wire_fits(c), Bool.and(LawsBase.wire_fits(w), LawsBase.wire_fits(x)), fc, LBool.cb_and_intro(LawsBase.wire_fits(w), LawsBase.wire_fits(x), fw, fx)))))
    case Wr.Bad{}:
      Unit{}

def hso.unknown(-s: String, +b: Bool, +j: Nat, +k: Nat, +c: Nat, +w: Nat, +x: Nat, +s6: String, pre: {s == Wr.put_bool(b, Wr.put_nat(j, Wr.put_nat(k, Wr.put_nat(c, Wr.put_nat(w, Wr.put_nat(x, s6)))))) : String}, fj: {LawsBase.wire_fits(j) == True{} : Bool}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, fw: {LawsBase.wire_fits(w) == True{} : Bool}, fx: {LawsBase.wire_fits(x) == True{} : Bool}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s6) == d : Wr.Dec<Bool>}) -> hso.RP(s, FHs.get_facts.unknown(b, j, k, c, w, x, d)):
  match d:
    case Wr.Got{+u, +s7}:
      +e = ed
      +pre2 = Equal.trans(String, s, Wr.put_bool(b, Wr.put_nat(j, Wr.put_nat(k, Wr.put_nat(c, Wr.put_nat(w, Wr.put_nat(x, s6)))))), Wr.put_bool(b, Wr.put_nat(j, Wr.put_nat(k, Wr.put_nat(c, Wr.put_nat(w, Wr.put_nat(x, Wr.put_bool(u, s7))))))), pre, Equal.cong(String, String, z => Wr.put_bool(b, Wr.put_nat(j, Wr.put_nat(k, Wr.put_nat(c, Wr.put_nat(w, Wr.put_nat(x, z)))))), s6, Wr.put_bool(u, s7), Wire.wire_bool_exact(s6, u, s7, e)))
      hso.limit(s, b, j, k, c, w, x, u, s7, pre2, fj, fk, fc, fw, fx, Wr.get_bool(s7), {==})
    case Wr.Bad{}:
      Unit{}

def hso.wakes(-s: String, +b: Bool, +j: Nat, +k: Nat, +c: Nat, +w: Nat, +s5: String, pre: {s == Wr.put_bool(b, Wr.put_nat(j, Wr.put_nat(k, Wr.put_nat(c, Wr.put_nat(w, s5))))) : String}, fj: {LawsBase.wire_fits(j) == True{} : Bool}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, fw: {LawsBase.wire_fits(w) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s5) == d : Wr.Dec<Nat>}) -> hso.RP(s, FHs.get_facts.wakes(b, j, k, c, w, d)):
  match d:
    case Wr.Got{+x, +s6}:
      +e = ed
      +fx = Wire.wire_nat_decoded_fits(s5, x, s6, e)
      +pre2 = Equal.trans(String, s, Wr.put_bool(b, Wr.put_nat(j, Wr.put_nat(k, Wr.put_nat(c, Wr.put_nat(w, s5))))), Wr.put_bool(b, Wr.put_nat(j, Wr.put_nat(k, Wr.put_nat(c, Wr.put_nat(w, Wr.put_nat(x, s6)))))), pre, Equal.cong(String, String, z => Wr.put_bool(b, Wr.put_nat(j, Wr.put_nat(k, Wr.put_nat(c, Wr.put_nat(w, z))))), s5, Wr.put_nat(x, s6), Wire.wire_nat_exact(s5, x, s6, e)))
      hso.unknown(s, b, j, k, c, w, x, s6, pre2, fj, fk, fc, fw, fx, Wr.get_bool(s6), {==})
    case Wr.Bad{}:
      Unit{}

def hso.runs(-s: String, +b: Bool, +j: Nat, +k: Nat, +c: Nat, +s4: String, pre: {s == Wr.put_bool(b, Wr.put_nat(j, Wr.put_nat(k, Wr.put_nat(c, s4)))) : String}, fj: {LawsBase.wire_fits(j) == True{} : Bool}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s4) == d : Wr.Dec<Nat>}) -> hso.RP(s, FHs.get_facts.runs(b, j, k, c, d)):
  match d:
    case Wr.Got{+w, +s5}:
      +e = ed
      +fw = Wire.wire_nat_decoded_fits(s4, w, s5, e)
      +pre2 = Equal.trans(String, s, Wr.put_bool(b, Wr.put_nat(j, Wr.put_nat(k, Wr.put_nat(c, s4)))), Wr.put_bool(b, Wr.put_nat(j, Wr.put_nat(k, Wr.put_nat(c, Wr.put_nat(w, s5))))), pre, Equal.cong(String, String, z => Wr.put_bool(b, Wr.put_nat(j, Wr.put_nat(k, Wr.put_nat(c, z)))), s4, Wr.put_nat(w, s5), Wire.wire_nat_exact(s4, w, s5, e)))
      hso.wakes(s, b, j, k, c, w, s5, pre2, fj, fk, fc, fw, Wr.get_nat(s5), {==})
    case Wr.Bad{}:
      Unit{}

def hso.children(-s: String, +b: Bool, +j: Nat, +k: Nat, +s3: String, pre: {s == Wr.put_bool(b, Wr.put_nat(j, Wr.put_nat(k, s3))) : String}, fj: {LawsBase.wire_fits(j) == True{} : Bool}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s3) == d : Wr.Dec<Nat>}) -> hso.RP(s, FHs.get_facts.children(b, j, k, d)):
  match d:
    case Wr.Got{+c, +s4}:
      +e = ed
      +fc = Wire.wire_nat_decoded_fits(s3, c, s4, e)
      +pre2 = Equal.trans(String, s, Wr.put_bool(b, Wr.put_nat(j, Wr.put_nat(k, s3))), Wr.put_bool(b, Wr.put_nat(j, Wr.put_nat(k, Wr.put_nat(c, s4)))), pre, Equal.cong(String, String, z => Wr.put_bool(b, Wr.put_nat(j, Wr.put_nat(k, z))), s3, Wr.put_nat(c, s4), Wire.wire_nat_exact(s3, c, s4, e)))
      hso.runs(s, b, j, k, c, s4, pre2, fj, fk, fc, Wr.get_nat(s4), {==})
    case Wr.Bad{}:
      Unit{}

def hso.kernel(-s: String, +b: Bool, +j: Nat, +s2: String, pre: {s == Wr.put_bool(b, Wr.put_nat(j, s2)) : String}, fj: {LawsBase.wire_fits(j) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}) -> hso.RP(s, FHs.get_facts.kernel(b, j, d)):
  match d:
    case Wr.Got{+k, +s3}:
      +e = ed
      +fk = Wire.wire_nat_decoded_fits(s2, k, s3, e)
      +pre2 = Equal.trans(String, s, Wr.put_bool(b, Wr.put_nat(j, s2)), Wr.put_bool(b, Wr.put_nat(j, Wr.put_nat(k, s3))), pre, Equal.cong(String, String, z => Wr.put_bool(b, Wr.put_nat(j, z)), s2, Wr.put_nat(k, s3), Wire.wire_nat_exact(s2, k, s3, e)))
      hso.children(s, b, j, k, s3, pre2, fj, fk, Wr.get_nat(s3), {==})
    case Wr.Bad{}:
      Unit{}

def hso.jobs(-s: String, +b: Bool, +s1: String, pre: {s == Wr.put_bool(b, s1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> hso.RP(s, FHs.get_facts.jobs(b, d)):
  match d:
    case Wr.Got{+j, +s2}:
      +e = ed
      +fj = Wire.wire_nat_decoded_fits(s1, j, s2, e)
      +pre2 = Equal.trans(String, s, Wr.put_bool(b, s1), Wr.put_bool(b, Wr.put_nat(j, s2)), pre, Equal.cong(String, String, z => Wr.put_bool(b, z), s1, Wr.put_nat(j, s2), Wire.wire_nat_exact(s1, j, s2, e)))
      hso.kernel(s, b, j, s2, pre2, fj, Wr.get_nat(s2), {==})
    case Wr.Bad{}:
      Unit{}

def hso.busy(+s: String, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s) == d : Wr.Dec<Bool>}) -> hso.RP(s, FHs.get_facts.busy(d)):
  match d:
    case Wr.Got{+b, +s1}:
      +e = ed
      hso.jobs(s, b, s1, Wire.wire_bool_exact(s, b, s1, e), Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

# a request decoded is spelled, and fits
def hso.req(+s: String) -> hso.RP(s, FHs.get_facts(s)):
  hso.busy(s, Wr.get_bool(s), {==})

def hso.T(s: String) -> Type:
  Sigma<&1, &1, Hs.Facts, f => {s == SpW.w_settle_req(f, "") : String} & {SpW.fit_settle(f) == True{} : Bool}>

# a value answered: a request read whole, nothing left
def hso.top(-s: String, x: Wr.Dec<Hs.Facts>, rp: hso.RP(s, x), ok: {LawsBase.wire_opens_err(FHs.ffi.got(x)) == False{} : Bool}) -> hso.T(s):
  match x:
    case Wr.Got{+f, rest}:
      match rest:
        case SNil{}:
          (f, rp)
        case SCon{y, z}:
          LStg.stg.absurd(hso.T(s), ok)
    case Wr.Bad{}:
      LStg.stg.absurd(hso.T(s), ok)

def HeadlessSettle.headless_settle_entry_reads_only_requests(s, ok):
  hso.top(s, FHs.get_facts(s), hso.req(s), ok)
