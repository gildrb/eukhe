# eukhe: the proof of LAW restart_ffi_malformed_unless_request
#
# PROOF: each field the entry's decoder reads is exactly its spelling, then
# its rest (wire_nat_exact, wire_list_exact with wire_nats_spells), and every
# number and count it reads fits (wire_nat_decoded_fits, LWF.wrb.nats_fit);
# the stages carry the input spelled up to their field (`pre`). So a request
# the decoder reads is the input's spelled prefix, and when it reads none
# the entry answers the malformed error, which the premise excludes.

import Base
import ../../bend/ffi_supervise.bend as FS
import ../../bend/supervise.bend as Su
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/supervise.bend as Supervise
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_list_exact.bend as PWireListExact
import ../wire/wire_nats_spells.bend as PWireNatsSpells
import ../wire/base/spell.bend as LAWireSpell
import ../wire_ffi/base.bend as LWF

# s spelled up to a field a is s spelled up to its spelling b
def smu.step(-F: String -> String, -s: String, -a: String, -b: String, pre: {s == F(a) : String}, e: {a == b : String}) -> {s == F(b) : String}:
  Equal.trans(String, s, F(a), F(b), pre, Equal.cong(String, String, F, a, b, e))

# a request the decoder reads: the input is its spelling, then the rest,
# and its numbers fit
def smu.Req(s: String, d: Wr.Dec<FS.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == Supervise.rs_spell_req(q, r) : String} & {Supervise.rs_req_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def smu.gap(+s: String, +c: Su.Cfg, +a: List<&2, Nat>, +s5: String, pre: {s == Supervise.rs_spell_cfg(c, LawsBase.wire_spell_nats(a, s5)) : String}, fc: {Supervise.rs_cfg_fits(c) == True{} : Bool}, fa: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, a)), LawsBase.wire_nats_fit(a)) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s5) == d : Wr.Dec<Nat>}) -> smu.Req(s, FS.get_req.gap(c, a, d)):
  match d:
    case Wr.Got{+g, +r}:
      +ee = ed
      +fl = Bool.and(LawsBase.wire_fits(List.length(&2, Nat, a)), LawsBase.wire_nats_fit(a))
      (smu.step(z => Supervise.rs_spell_cfg(c, LawsBase.wire_spell_nats(a, z)), s, s5, Wr.put_nat(g, r), pre, Wire.wire_nat_exact(s5, g, r, ee)),
        LAWireSpell.ws_and_tt(Supervise.rs_cfg_fits(c), Bool.and(fl, LawsBase.wire_fits(g)), fc, LAWireSpell.ws_and_tt(fl, LawsBase.wire_fits(g), fa, Wire.wire_nat_decoded_fits(s5, g, r, ee))))
    case Wr.Bad{}:
      Unit{}

def smu.ages(+s: String, +c: Su.Cfg, +s4: String, pre: {s == Supervise.rs_spell_cfg(c, s4) : String}, fc: {Supervise.rs_cfg_fits(c) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s4) == d : Wr.Dec<List<&2, Nat>>}) -> smu.Req(s, FS.get_req.ages(c, d)):
  match d:
    case Wr.Got{+a, +s5}:
      +ee = ed
      +e4 = Equal.trans(String, s4, Wr.put_list(~Nat, ~Wr.put_nat, a, s5), LawsBase.wire_spell_nats(a, s5), Wire.wire_list_exact(s4, a, s5, ee), Wire.wire_nats_spells(a, s5))
      smu.gap(s, c, a, s5, smu.step(z => Supervise.rs_spell_cfg(c, z), s, s4, LawsBase.wire_spell_nats(a, s5), pre, e4), fc, LWF.wrb.nats_fit(s4, a, s5, ee), Wr.get_nat(s5), {==})
    case Wr.Bad{}:
      Unit{}

def smu.m(+s: String, +k: Nat, +w: Nat, +b: Nat, +s3: String, pre: {s == Wr.put_nat(k, Wr.put_nat(w, Wr.put_nat(b, s3))) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, fw: {LawsBase.wire_fits(w) == True{} : Bool}, fb: {LawsBase.wire_fits(b) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s3) == d : Wr.Dec<Nat>}) -> smu.Req(s, FS.get_req.cfg(FS.get_cfg.m(k, w, b, d))):
  match d:
    case Wr.Got{+m, +s4}:
      +ee = ed
      +fm = Wire.wire_nat_decoded_fits(s3, m, s4, ee)
      +fc = LAWireSpell.ws_and_tt(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(w), Bool.and(LawsBase.wire_fits(b), LawsBase.wire_fits(m))), fk, LAWireSpell.ws_and_tt(LawsBase.wire_fits(w), Bool.and(LawsBase.wire_fits(b), LawsBase.wire_fits(m)), fw, LAWireSpell.ws_and_tt(LawsBase.wire_fits(b), LawsBase.wire_fits(m), fb, fm)))
      smu.ages(s, Su.Cfg{k, w, b, m}, s4, smu.step(z => Wr.put_nat(k, Wr.put_nat(w, Wr.put_nat(b, z))), s, s3, Wr.put_nat(m, s4), pre, Wire.wire_nat_exact(s3, m, s4, ee)), fc, Wr.get_list(~Nat, ~Wr.get_nat, s4), {==})
    case Wr.Bad{}:
      Unit{}

def smu.b(+s: String, +k: Nat, +w: Nat, +s2: String, pre: {s == Wr.put_nat(k, Wr.put_nat(w, s2)) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, fw: {LawsBase.wire_fits(w) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}) -> smu.Req(s, FS.get_req.cfg(FS.get_cfg.b(k, w, d))):
  match d:
    case Wr.Got{+b, +s3}:
      +ee = ed
      smu.m(s, k, w, b, s3, smu.step(z => Wr.put_nat(k, Wr.put_nat(w, z)), s, s2, Wr.put_nat(b, s3), pre, Wire.wire_nat_exact(s2, b, s3, ee)), fk, fw, Wire.wire_nat_decoded_fits(s2, b, s3, ee), Wr.get_nat(s3), {==})
    case Wr.Bad{}:
      Unit{}

def smu.w(+s: String, +k: Nat, +s1: String, pre: {s == Wr.put_nat(k, s1) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> smu.Req(s, FS.get_req.cfg(FS.get_cfg.w(k, d))):
  match d:
    case Wr.Got{+w, +s2}:
      +ee = ed
      smu.b(s, k, w, s2, smu.step(z => Wr.put_nat(k, z), s, s1, Wr.put_nat(w, s2), pre, Wire.wire_nat_exact(s1, w, s2, ee)), fk, Wire.wire_nat_decoded_fits(s1, w, s2, ee), Wr.get_nat(s2), {==})
    case Wr.Bad{}:
      Unit{}

# the request the decoder reads is the input's spelled prefix, and fits
def smu.k(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> smu.Req(s, FS.get_req.cfg(FS.get_cfg.k(d))):
  match d:
    case Wr.Got{+k, +s1}:
      +ee = ed
      smu.w(s, k, s1, Wire.wire_nat_exact(s, k, s1, ee), Wire.wire_nat_decoded_fits(s, k, s1, ee), Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

def smu.goal(+s: String) -> Type:
  &q: FS.Req -> &rest: String -> {(s, Supervise.rs_req_fits(q)) == (Supervise.rs_spell_req(q, rest), True{}) : String & Bool}

def smu.eq(+s: String, +q: FS.Req, +rest: String, e1: {s == Supervise.rs_spell_req(q, rest) : String}, e2: {Supervise.rs_req_fits(q) == True{} : Bool}) -> {(s, Supervise.rs_req_fits(q)) == (Supervise.rs_spell_req(q, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, Supervise.rs_spell_req(q, rest), e1) : {(_, Supervise.rs_req_fits(q)) == (Supervise.rs_spell_req(q, rest), True{}) : String & Bool}
  %Equal.sym(Bool, Supervise.rs_req_fits(q), True{}, e2) : {(Supervise.rs_spell_req(q, rest), _) == (Supervise.rs_spell_req(q, rest), True{}) : String & Bool}
  {==}

def smu.main(+s: String, d: Wr.Dec<FS.Req>, inv: smu.Req(s, d), other: {String.eq(FS.ffi.go(d), Supervise.rs_malformed()) == False{} : Bool}) -> smu.goal(s):
  match d:
    case Wr.Got{+q, +rest}:
      (e1, e2) = inv
      (q, (rest, smu.eq(s, q, rest, e1, e2)))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(smu.goal(s), other)

def Supervise.restart_ffi_malformed_unless_request(s, other):
  smu.main(s, FS.get_req(s), smu.k(s, Wr.get_nat(s), {==}), other)
