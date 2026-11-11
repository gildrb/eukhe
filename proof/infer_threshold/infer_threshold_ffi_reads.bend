# eukhe: the proof of LAW infer_threshold_ffi_reads
#
# PROOF: each field the entry's decoder reads is the spelling of its value,
# within the wire (Wire.wire_bool_exact, wire_nat_exact,
# wire_nat_decoded_fits, wire_list_exact, WireFfi.wrb.nats_fit; a sign is
# its tag 0 or 1, then a Nat: itr.z), so the input up to a field is the
# prefix F spelled so far, applied to the rest (itr.go .. itr.cuts); the
# entry answers a value only for a request read whole, nothing left
# (itr.top).

import Base
import ../../bend/infer_threshold.bend as M
import ../../bend/ffi_infer_threshold.bend as FT
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/infer_threshold.bend as InferThreshold
import ../wire/base/spell.bend as LAWireSpell
import ../wire_ffi/base.bend as WRB

# the request q, then rest
def itr.spell(q: FT.Req, rest: String) -> String:
  match q:
    case FT.Req{on, t, last, w, r, m, keep, full, xs, cuts}:
      Wr.put_bool(on, Wr.put_nat(t, Wr.put_nat(last, Wr.put_nat(w, InferThreshold.spell_z(r, InferThreshold.spell_z(m, Wr.put_nat(keep, Wr.put_nat(full, InferThreshold.spell_nats(xs, InferThreshold.spell_nats(cuts, rest))))))))))

# a decoded request is spelled, then its rest, and fits
def itr.P(s: String, x: Wr.Dec<FT.Req>) -> Type:
  match x:
    case Wr.Got{q, rr}:
      {s == itr.spell(q, rr) : String} & {InferThreshold.ask_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# every number of a request fits: the nine halves
def itr.fits(-t: Nat, -last: Nat, -w: Nat, -r: M.Z, -m: M.Z, -keep: Nat, -full: Nat, -xs: List<&2, Nat>, -cuts: List<&2, Nat>,
  ft: {LawsBase.wire_fits(t) == True{} : Bool}, fl: {LawsBase.wire_fits(last) == True{} : Bool}, fw: {LawsBase.wire_fits(w) == True{} : Bool},
  fr: {InferThreshold.z_fits(r) == True{} : Bool}, fm: {InferThreshold.z_fits(m) == True{} : Bool}, fk: {LawsBase.wire_fits(keep) == True{} : Bool},
  ff: {LawsBase.wire_fits(full) == True{} : Bool}, fx: {InferThreshold.nats_fit(xs) == True{} : Bool}, fc: {InferThreshold.nats_fit(cuts) == True{} : Bool})
  -> {InferThreshold.req_fits(t, last, w, r, m, keep, full, xs, cuts) == True{} : Bool}:
  +h7 = LAWireSpell.ws_and_tt(InferThreshold.nats_fit(xs), InferThreshold.nats_fit(cuts), fx, fc)
  +h6 = LAWireSpell.ws_and_tt(LawsBase.wire_fits(full), Bool.and(InferThreshold.nats_fit(xs), InferThreshold.nats_fit(cuts)), ff, h7)
  +h5 = LAWireSpell.ws_and_tt(LawsBase.wire_fits(keep), Bool.and(LawsBase.wire_fits(full), Bool.and(InferThreshold.nats_fit(xs), InferThreshold.nats_fit(cuts))), fk, h6)
  +h4 = LAWireSpell.ws_and_tt(InferThreshold.z_fits(m), Bool.and(LawsBase.wire_fits(keep), Bool.and(LawsBase.wire_fits(full), Bool.and(InferThreshold.nats_fit(xs), InferThreshold.nats_fit(cuts)))), fm, h5)
  +h3 = LAWireSpell.ws_and_tt(InferThreshold.z_fits(r), Bool.and(InferThreshold.z_fits(m), Bool.and(LawsBase.wire_fits(keep), Bool.and(LawsBase.wire_fits(full), Bool.and(InferThreshold.nats_fit(xs), InferThreshold.nats_fit(cuts))))), fr, h4)
  +h2 = LAWireSpell.ws_and_tt(LawsBase.wire_fits(w), Bool.and(InferThreshold.z_fits(r), Bool.and(InferThreshold.z_fits(m), Bool.and(LawsBase.wire_fits(keep), Bool.and(LawsBase.wire_fits(full), Bool.and(InferThreshold.nats_fit(xs), InferThreshold.nats_fit(cuts)))))), fw, h3)
  +h1 = LAWireSpell.ws_and_tt(LawsBase.wire_fits(last), Bool.and(LawsBase.wire_fits(w), Bool.and(InferThreshold.z_fits(r), Bool.and(InferThreshold.z_fits(m), Bool.and(LawsBase.wire_fits(keep), Bool.and(LawsBase.wire_fits(full), Bool.and(InferThreshold.nats_fit(xs), InferThreshold.nats_fit(cuts))))))), fl, h2)
  LAWireSpell.ws_and_tt(LawsBase.wire_fits(t), Bool.and(LawsBase.wire_fits(last), Bool.and(LawsBase.wire_fits(w), Bool.and(InferThreshold.z_fits(r), Bool.and(InferThreshold.z_fits(m), Bool.and(LawsBase.wire_fits(keep), Bool.and(LawsBase.wire_fits(full), Bool.and(InferThreshold.nats_fit(xs), InferThreshold.nats_fit(cuts)))))))), ft, h1)

# A sign
# ------

# a decoded sign is spelled, then its rest, and fits
def itr.ZP(s: String, d: Wr.Dec<M.Z>) -> Type:
  match d:
    case Wr.Got{z, rr}:
      {s == InferThreshold.spell_z(z, rr) : String} & {InferThreshold.z_fits(z) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def itr.z_up(-s: String, +s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> itr.ZP(s, FT.get_z.up(d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      (WRB.wrb.step(z => Wr.put_nat(0n, z), s, s1, Wr.put_nat(n, s2), pre, Wire.wire_nat_exact(s1, n, s2, e)), Wire.wire_nat_decoded_fits(s1, n, s2, e))
    case Wr.Bad{}:
      Unit{}

def itr.z_down(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> itr.ZP(s, FT.get_z.down(d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      (WRB.wrb.step(z => Wr.put_nat(1n, z), s, s1, Wr.put_nat(n, s2), pre, Wire.wire_nat_exact(s1, n, s2, e)), Wire.wire_nat_decoded_fits(s1, n, s2, e))
    case Wr.Bad{}:
      Unit{}

def itr.z_tag(-s: String, t: Nat, +s1: String, pre: {s == Wr.put_nat(t, s1) : String}) -> itr.ZP(s, FT.get_z.tag(t, s1)):
  match t:
    case 0n:
      itr.z_up(s, s1, pre, Wr.get_nat(s1), {==})
    case 1n:
      itr.z_down(s, s1, pre, Wr.get_nat(s1), {==})
    case 2n+p:
      Unit{}

def itr.z(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> itr.ZP(s, FT.get_z(d)):
  match d:
    case Wr.Got{+t, +s1}:
      +e = ed
      itr.z_tag(s, t, s1, Wire.wire_nat_exact(s, t, s1, e))
    case Wr.Bad{}:
      Unit{}

# The request, field by field
# ---------------------------
# s is itr.p<k>(the k fields read so far, rest): those fields spelled,
# then the rest.

def itr.p1(on: Bool, z: String) -> String:
  Wr.put_bool(on, z)

def itr.p2(on: Bool, t: Nat, z: String) -> String:
  itr.p1(on, Wr.put_nat(t, z))

def itr.p3(on: Bool, t: Nat, last: Nat, z: String) -> String:
  itr.p2(on, t, Wr.put_nat(last, z))

def itr.p4(on: Bool, t: Nat, last: Nat, w: Nat, z: String) -> String:
  itr.p3(on, t, last, Wr.put_nat(w, z))

def itr.p5(on: Bool, t: Nat, last: Nat, w: Nat, r: M.Z, z: String) -> String:
  itr.p4(on, t, last, w, InferThreshold.spell_z(r, z))

def itr.p6(on: Bool, t: Nat, last: Nat, w: Nat, r: M.Z, m: M.Z, z: String) -> String:
  itr.p5(on, t, last, w, r, InferThreshold.spell_z(m, z))

def itr.p7(on: Bool, t: Nat, last: Nat, w: Nat, r: M.Z, m: M.Z, keep: Nat, z: String) -> String:
  itr.p6(on, t, last, w, r, m, Wr.put_nat(keep, z))

def itr.p8(on: Bool, t: Nat, last: Nat, w: Nat, r: M.Z, m: M.Z, keep: Nat, full: Nat, z: String) -> String:
  itr.p7(on, t, last, w, r, m, keep, Wr.put_nat(full, z))

def itr.p9(on: Bool, t: Nat, last: Nat, w: Nat, r: M.Z, m: M.Z, keep: Nat, full: Nat, xs: List<&2, Nat>, z: String) -> String:
  itr.p8(on, t, last, w, r, m, keep, full, InferThreshold.spell_nats(xs, z))

def itr.cuts(-s: String, +on: Bool, +t: Nat, +last: Nat, +w: Nat, +r: M.Z, +m: M.Z, +keep: Nat, +full: Nat, +xs: List<&2, Nat>, +s9: String, pre: {s == itr.p9(on, t, last, w, r, m, keep, full, xs, s9) : String},
  ft: {LawsBase.wire_fits(t) == True{} : Bool}, fl: {LawsBase.wire_fits(last) == True{} : Bool}, fw: {LawsBase.wire_fits(w) == True{} : Bool}, fr: {InferThreshold.z_fits(r) == True{} : Bool}, fm: {InferThreshold.z_fits(m) == True{} : Bool}, fk: {LawsBase.wire_fits(keep) == True{} : Bool}, ff: {LawsBase.wire_fits(full) == True{} : Bool}, fx: {InferThreshold.nats_fit(xs) == True{} : Bool},
  d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s9) == d : Wr.Dec<List<&2, Nat>>}) -> itr.P(s, FT.get_req.cuts(on, t, last, w, r, m, keep, full, xs, d)):
  match d:
    case Wr.Got{+cuts, +s10}:
      +e = ed
      (WRB.wrb.step(z => itr.p9(on, t, last, w, r, m, keep, full, xs, z), s, s9, Wr.put_list(~Nat, ~Wr.put_nat, cuts, s10), pre, Wire.wire_list_exact(s9, cuts, s10, e)), itr.fits(t, last, w, r, m, keep, full, xs, cuts, ft, fl, fw, fr, fm, fk, ff, fx, WRB.wrb.nats_fit(s9, cuts, s10, e)))
    case Wr.Bad{}:
      Unit{}

def itr.sizes(-s: String, +on: Bool, +t: Nat, +last: Nat, +w: Nat, +r: M.Z, +m: M.Z, +keep: Nat, +full: Nat, +s8: String, pre: {s == itr.p8(on, t, last, w, r, m, keep, full, s8) : String},
  ft: {LawsBase.wire_fits(t) == True{} : Bool}, fl: {LawsBase.wire_fits(last) == True{} : Bool}, fw: {LawsBase.wire_fits(w) == True{} : Bool}, fr: {InferThreshold.z_fits(r) == True{} : Bool}, fm: {InferThreshold.z_fits(m) == True{} : Bool}, fk: {LawsBase.wire_fits(keep) == True{} : Bool}, ff: {LawsBase.wire_fits(full) == True{} : Bool},
  d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s8) == d : Wr.Dec<List<&2, Nat>>}) -> itr.P(s, FT.get_req.sizes(on, t, last, w, r, m, keep, full, d)):
  match d:
    case Wr.Got{+xs, +s9}:
      +e = ed
      itr.cuts(s, on, t, last, w, r, m, keep, full, xs, s9, WRB.wrb.step(z => itr.p8(on, t, last, w, r, m, keep, full, z), s, s8, Wr.put_list(~Nat, ~Wr.put_nat, xs, s9), pre, Wire.wire_list_exact(s8, xs, s9, e)), ft, fl, fw, fr, fm, fk, ff, WRB.wrb.nats_fit(s8, xs, s9, e), Wr.get_list(~Nat, ~Wr.get_nat, s9), {==})
    case Wr.Bad{}:
      Unit{}

def itr.full(-s: String, +on: Bool, +t: Nat, +last: Nat, +w: Nat, +r: M.Z, +m: M.Z, +keep: Nat, +s7: String, pre: {s == itr.p7(on, t, last, w, r, m, keep, s7) : String},
  ft: {LawsBase.wire_fits(t) == True{} : Bool}, fl: {LawsBase.wire_fits(last) == True{} : Bool}, fw: {LawsBase.wire_fits(w) == True{} : Bool}, fr: {InferThreshold.z_fits(r) == True{} : Bool}, fm: {InferThreshold.z_fits(m) == True{} : Bool}, fk: {LawsBase.wire_fits(keep) == True{} : Bool},
  d: Wr.Dec<Nat>, ed: {Wr.get_nat(s7) == d : Wr.Dec<Nat>}) -> itr.P(s, FT.get_req.full(on, t, last, w, r, m, keep, d)):
  match d:
    case Wr.Got{+full, +s8}:
      +e = ed
      itr.sizes(s, on, t, last, w, r, m, keep, full, s8, WRB.wrb.step(z => itr.p7(on, t, last, w, r, m, keep, z), s, s7, Wr.put_nat(full, s8), pre, Wire.wire_nat_exact(s7, full, s8, e)), ft, fl, fw, fr, fm, fk, Wire.wire_nat_decoded_fits(s7, full, s8, e), Wr.get_list(~Nat, ~Wr.get_nat, s8), {==})
    case Wr.Bad{}:
      Unit{}

def itr.keep(-s: String, +on: Bool, +t: Nat, +last: Nat, +w: Nat, +r: M.Z, +m: M.Z, +s6: String, pre: {s == itr.p6(on, t, last, w, r, m, s6) : String},
  ft: {LawsBase.wire_fits(t) == True{} : Bool}, fl: {LawsBase.wire_fits(last) == True{} : Bool}, fw: {LawsBase.wire_fits(w) == True{} : Bool}, fr: {InferThreshold.z_fits(r) == True{} : Bool}, fm: {InferThreshold.z_fits(m) == True{} : Bool},
  d: Wr.Dec<Nat>, ed: {Wr.get_nat(s6) == d : Wr.Dec<Nat>}) -> itr.P(s, FT.get_req.keep(on, t, last, w, r, m, d)):
  match d:
    case Wr.Got{+keep, +s7}:
      +e = ed
      itr.full(s, on, t, last, w, r, m, keep, s7, WRB.wrb.step(z => itr.p6(on, t, last, w, r, m, z), s, s6, Wr.put_nat(keep, s7), pre, Wire.wire_nat_exact(s6, keep, s7, e)), ft, fl, fw, fr, fm, Wire.wire_nat_decoded_fits(s6, keep, s7, e), Wr.get_nat(s7), {==})
    case Wr.Bad{}:
      Unit{}

def itr.margin(-s: String, +on: Bool, +t: Nat, +last: Nat, +w: Nat, +r: M.Z, -s5: String, pre: {s == itr.p5(on, t, last, w, r, s5) : String},
  ft: {LawsBase.wire_fits(t) == True{} : Bool}, fl: {LawsBase.wire_fits(last) == True{} : Bool}, fw: {LawsBase.wire_fits(w) == True{} : Bool}, fr: {InferThreshold.z_fits(r) == True{} : Bool},
  d: Wr.Dec<M.Z>, zp: itr.ZP(s5, d)) -> itr.P(s, FT.get_req.margin(on, t, last, w, r, d)):
  match d:
    case Wr.Got{+m, +s6}:
      (em, fm) = zp
      itr.keep(s, on, t, last, w, r, m, s6, WRB.wrb.step(z => itr.p5(on, t, last, w, r, z), s, s5, InferThreshold.spell_z(m, s6), pre, em), ft, fl, fw, fr, fm, Wr.get_nat(s6), {==})
    case Wr.Bad{}:
      Unit{}

def itr.reserve(-s: String, +on: Bool, +t: Nat, +last: Nat, +w: Nat, -s4: String, pre: {s == itr.p4(on, t, last, w, s4) : String},
  ft: {LawsBase.wire_fits(t) == True{} : Bool}, fl: {LawsBase.wire_fits(last) == True{} : Bool}, fw: {LawsBase.wire_fits(w) == True{} : Bool},
  d: Wr.Dec<M.Z>, zp: itr.ZP(s4, d)) -> itr.P(s, FT.get_req.reserve(on, t, last, w, d)):
  match d:
    case Wr.Got{+r, +s5}:
      (er, fr) = zp
      itr.margin(s, on, t, last, w, r, s5, WRB.wrb.step(z => itr.p4(on, t, last, w, z), s, s4, InferThreshold.spell_z(r, s5), pre, er), ft, fl, fw, fr, FT.get_z(Wr.get_nat(s5)), itr.z(s5, Wr.get_nat(s5), {==}))
    case Wr.Bad{}:
      Unit{}

def itr.window(-s: String, +on: Bool, +t: Nat, +last: Nat, +s3: String, pre: {s == itr.p3(on, t, last, s3) : String},
  ft: {LawsBase.wire_fits(t) == True{} : Bool}, fl: {LawsBase.wire_fits(last) == True{} : Bool},
  d: Wr.Dec<Nat>, ed: {Wr.get_nat(s3) == d : Wr.Dec<Nat>}) -> itr.P(s, FT.get_req.window(on, t, last, d)):
  match d:
    case Wr.Got{+w, +s4}:
      +e = ed
      itr.reserve(s, on, t, last, w, s4, WRB.wrb.step(z => itr.p3(on, t, last, z), s, s3, Wr.put_nat(w, s4), pre, Wire.wire_nat_exact(s3, w, s4, e)), ft, fl, Wire.wire_nat_decoded_fits(s3, w, s4, e), FT.get_z(Wr.get_nat(s4)), itr.z(s4, Wr.get_nat(s4), {==}))
    case Wr.Bad{}:
      Unit{}

def itr.last(-s: String, +on: Bool, +t: Nat, +s2: String, pre: {s == itr.p2(on, t, s2) : String},
  ft: {LawsBase.wire_fits(t) == True{} : Bool},
  d: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}) -> itr.P(s, FT.get_req.last(on, t, d)):
  match d:
    case Wr.Got{+last, +s3}:
      +e = ed
      itr.window(s, on, t, last, s3, WRB.wrb.step(z => itr.p2(on, t, z), s, s2, Wr.put_nat(last, s3), pre, Wire.wire_nat_exact(s2, last, s3, e)), ft, Wire.wire_nat_decoded_fits(s2, last, s3, e), Wr.get_nat(s3), {==})
    case Wr.Bad{}:
      Unit{}

def itr.tokens(-s: String, +on: Bool, +s1: String, pre: {s == itr.p1(on, s1) : String},
  d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> itr.P(s, FT.get_req.tokens(on, d)):
  match d:
    case Wr.Got{+t, +s2}:
      +e = ed
      itr.last(s, on, t, s2, WRB.wrb.step(z => itr.p1(on, z), s, s1, Wr.put_nat(t, s2), pre, Wire.wire_nat_exact(s1, t, s2, e)), Wire.wire_nat_decoded_fits(s1, t, s2, e), Wr.get_nat(s2), {==})
    case Wr.Bad{}:
      Unit{}

def itr.go(+s: String, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s) == d : Wr.Dec<Bool>}) -> itr.P(s, FT.get_req.go(d)):
  match d:
    case Wr.Got{+on, +s1}:
      +e = ed
      itr.tokens(s, on, s1, Wire.wire_bool_exact(s, on, s1, e), Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

# The answer
# ----------

def itr.G(s: String) -> Type:
  Sigma<&1, &1, FT.Req, q => {s == InferThreshold.spell_ask(q) : String} & {InferThreshold.ask_fits(q) == True{} : Bool}>

# a request read whole: its spelling with nothing after is spell_ask
def itr.whole(-s: String, q: FT.Req, rp: {s == itr.spell(q, "") : String} & {InferThreshold.ask_fits(q) == True{} : Bool}) -> itr.G(s):
  match q:
    case FT.Req{on, t, last, w, r, m, keep, full, xs, cuts}:
      (FT.Req{on, t, last, w, r, m, keep, full, xs, cuts}, rp)

# a value answered: a request read whole, nothing left
def itr.top(-s: String, x: Wr.Dec<FT.Req>, rp: itr.P(s, x), ok: {LawsBase.wire_opens_err(FT.run(x)) == False{} : Bool}) -> itr.G(s):
  match x:
    case Wr.Got{q, rest}:
      match rest:
        case SNil{}:
          itr.whole(s, q, rp)
        case SCon{y, z}:
          LAWireSpell.ws_absurd(itr.G(s), ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(itr.G(s), ok)

def InferThreshold.infer_threshold_ffi_reads(s, ok):
  itr.top(s, FT.get_req(s), itr.go(s, Wr.get_bool(s), {==}), ok)
