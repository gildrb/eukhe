# eukhe: the proof of LAW adw_open_malformed_unless_request
#
# PROOF: the decoder reads only spelled opens that fit, the rest after
# them untouched (asx.open); when it reads none the entry answers the
# malformed error, which the premise excludes.

import Base
import ../../bend/admission.bend as Ad
import ../../bend/ffi_admission.bend as FAd
import ../../bend/wire.bend as Wr
import ../../laws/admission.bend as Admission
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell
import ./base/spell.bend as LASpell
import ../../laws/admission/wire.bend as AdmissionWire

def aom.goal(+s: String) -> Type:
  &l: Ad.Lim -> &q: Nat -> &rest: String -> {(s, Bool.and(AdmissionWire.adw_lim_fits(l), LawsBase.wire_fits(q))) == (AdmissionWire.adw_spell_open(l, q, rest), True{}) : String & Bool}

def aom.eq(+s: String, +l: Ad.Lim, +q: Nat, +rest: String, e1: {s == AdmissionWire.adw_spell_open(l, q, rest) : String}, e2: {Bool.and(AdmissionWire.adw_lim_fits(l), LawsBase.wire_fits(q)) == True{} : Bool}) -> {(s, Bool.and(AdmissionWire.adw_lim_fits(l), LawsBase.wire_fits(q))) == (AdmissionWire.adw_spell_open(l, q, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, AdmissionWire.adw_spell_open(l, q, rest), e1) : {(_, Bool.and(AdmissionWire.adw_lim_fits(l), LawsBase.wire_fits(q))) == (AdmissionWire.adw_spell_open(l, q, rest), True{}) : String & Bool}
  %Equal.sym(Bool, Bool.and(AdmissionWire.adw_lim_fits(l), LawsBase.wire_fits(q)), True{}, e2) : {(AdmissionWire.adw_spell_open(l, q, rest), _) == (AdmissionWire.adw_spell_open(l, q, rest), True{}) : String & Bool}
  {==}

def aom.at(+s: String, lq: +Sigma<Ad.Lim, x => Nat>, +r: String, inv: LASpell.asx.Open.at(s, lq, r)) -> aom.goal(s):
  match lq:
    case (+l, +q):
      (e1, e2) = inv
      (l, (q, (r, aom.eq(s, l, q, r, e1, e2))))

def aom.main(+s: String, d: Wr.Dec<+Sigma<Ad.Lim, x => Nat>>, inv: LASpell.asx.Open(s, d), other: {String.eq(AdmissionWire.adw_reply(FAd.open.go(d)), Wr.err("admission: malformed open")) == False{} : Bool}) -> aom.goal(s):
  match d:
    case Wr.Got{lq, +r}:
      aom.at(s, lq, r, inv)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(aom.goal(s), other)

def AdmissionWire.adw_open_malformed_unless_request(s, other):
  aom.main(s, FAd.get_open(s), LASpell.asx.open(s), other)
