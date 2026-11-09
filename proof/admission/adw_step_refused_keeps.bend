# eukhe: the proof of LAW adw_step_refused_keeps
#
# PROOF: every step on a running controller but a whole op read with
# nothing left answers the controller kept; a whole op answers a
# controller, which never opens with 'E' (asp.live_not_err), against the
# premise.

import Base
import ../../bend/admission.bend as Ad
import ../../bend/ffi_admission.bend as FAd
import ../../bend/wire.bend as Wr
import ../../laws/admission.bend as Admission
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell
import ./base/spell.bend as LASpell
import ../../laws/admission/wire.bend as AdmissionWire

def ark.end(r: String, +x: Ad.Live, +o: Ad.Op, err: {LawsBase.wire_opens_err(AdmissionWire.adw_reply(FAd.step.end(Wr.end(r), x, o))) == True{} : Bool}) -> {AdmissionWire.adw_state(FAd.step.end(Wr.end(r), x, o)) == FAd.Running{x} : FAd.St}:
  match r:
    case SNil{}:
      LASpell.asp.absurd({FAd.Running{Ad.Live.step(x, o)} == FAd.Running{x} : FAd.St}, Equal.trans(Bool, False{}, LawsBase.wire_opens_err(FAd.put_live(Ad.Live.step(x, o), "")), True{}, Equal.sym(Bool, LawsBase.wire_opens_err(FAd.put_live(Ad.Live.step(x, o), "")), False{}, LASpell.asp.live_not_err(Ad.Live.step(x, o), "")), err))
    case SCon{c, t}:
      {==}

def ark.main(d: Wr.Dec<Ad.Op>, +x: Ad.Live, err: {LawsBase.wire_opens_err(AdmissionWire.adw_reply(FAd.step.op(x, d))) == True{} : Bool}) -> {AdmissionWire.adw_state(FAd.step.op(x, d)) == FAd.Running{x} : FAd.St}:
  match d:
    case Wr.Got{+o, r}:
      ark.end(r, x, o, err)
    case Wr.Bad{}:
      {==}

def AdmissionWire.adw_step_refused_keeps(x, s, err):
  ark.main(FAd.get_op(s), x, err)
