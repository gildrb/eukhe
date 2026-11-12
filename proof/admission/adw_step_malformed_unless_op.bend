# eukhe: the proof of LAW adw_step_malformed_unless_op
#
# PROOF: the decoder reads only spelled ops that fit, the rest after them
# untouched (asx.op); when it reads none the entry answers the malformed
# error, which the premise excludes.

import Base
import ../../bend/admission.bend as Ad
import ../../bend/ffi_admission.bend as FAd
import ../../bend/wire.bend as Wr
import ../../laws/admission.bend as Admission
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell
import ./base/spell.bend as LASpell
import ../../laws/admission/wire.bend as AdmissionWire

def amo.goal(+s: String) -> Type:
  &o: Ad.Op -> &rest: String -> {(s, AdmissionWire.adw_op_fits(o)) == (AdmissionWire.adw_spell_op(o, rest), True{}) : String & Bool}

def amo.eq(+s: String, +o: Ad.Op, +rest: String, e1: {s == AdmissionWire.adw_spell_op(o, rest) : String}, e2: {AdmissionWire.adw_op_fits(o) == True{} : Bool}) -> {(s, AdmissionWire.adw_op_fits(o)) == (AdmissionWire.adw_spell_op(o, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, AdmissionWire.adw_spell_op(o, rest), e1) : {(_, AdmissionWire.adw_op_fits(o)) == (AdmissionWire.adw_spell_op(o, rest), True{}) : String & Bool}
  %Equal.sym(Bool, AdmissionWire.adw_op_fits(o), True{}, e2) : {(AdmissionWire.adw_spell_op(o, rest), _) == (AdmissionWire.adw_spell_op(o, rest), True{}) : String & Bool}
  {==}

def amo.main(-x: Ad.Live, +s: String, d: Wr.Dec<Ad.Op>, inv: LASpell.asx.Op(s, d), other: {String.eq(AdmissionWire.adw_reply(FAd.step.op(x, d)), Wr.err("admission: malformed op")) == False{} : Bool}) -> amo.goal(s):
  match d:
    case Wr.Got{+o, +rest}:
      (e1, e2) = inv
      (o, (rest, amo.eq(s, o, rest, e1, e2)))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(amo.goal(s), other)

def AdmissionWire.adw_step_malformed_unless_op(x, s, other):
  amo.main(x, s, FAd.get_op(s), LASpell.asx.op(s), other)
