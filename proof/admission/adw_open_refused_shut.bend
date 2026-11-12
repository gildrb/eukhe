# eukhe: the proof of LAW adw_open_refused_shut
#
# PROOF: every open but a whole request read with nothing left answers
# the refused state; a whole request answers a controller, which never
# opens with 'E' (asp.live_not_err), against the premise.

import Base
import ../../bend/admission.bend as Ad
import ../../bend/ffi_admission.bend as FAd
import ../../bend/wire.bend as Wr
import ../../laws/admission.bend as Admission
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell
import ./base/spell.bend as LASpell
import ../../laws/admission/wire.bend as AdmissionWire

def aor.end(r: String, +l: Ad.Lim, +q: Nat, err: {LawsBase.wire_opens_err(AdmissionWire.adw_reply(FAd.open.end(Wr.end(r), l, q))) == True{} : Bool}) -> {AdmissionWire.adw_state(FAd.open.end(Wr.end(r), l, q)) == FAd.Shut{} : FAd.St}:
  match r:
    case SNil{}:
      LASpell.asp.absurd({FAd.Running{Ad.Live.new(l, q)} == FAd.Shut{} : FAd.St}, Equal.trans(Bool, False{}, LawsBase.wire_opens_err(FAd.put_live(Ad.Live.new(l, q), "")), True{}, Equal.sym(Bool, LawsBase.wire_opens_err(FAd.put_live(Ad.Live.new(l, q), "")), False{}, LASpell.asp.live_not_err(Ad.Live.new(l, q), "")), err))
    case SCon{c, t}:
      {==}

def aor.at(lq: +Sigma<Ad.Lim, x => Nat>, r: String, err: {LawsBase.wire_opens_err(AdmissionWire.adw_reply(FAd.open.req(lq, Wr.end(r)))) == True{} : Bool}) -> {AdmissionWire.adw_state(FAd.open.req(lq, Wr.end(r))) == FAd.Shut{} : FAd.St}:
  match lq:
    case (+l, +q):
      aor.end(r, l, q, err)

def aor.main(d: Wr.Dec<+Sigma<Ad.Lim, x => Nat>>, err: {LawsBase.wire_opens_err(AdmissionWire.adw_reply(FAd.open.go(d))) == True{} : Bool}) -> {AdmissionWire.adw_state(FAd.open.go(d)) == FAd.Shut{} : FAd.St}:
  match d:
    case Wr.Got{lq, r}:
      aor.at(lq, r, err)
    case Wr.Bad{}:
      {==}

def AdmissionWire.adw_open_refused_shut(s, err):
  aor.main(FAd.get_open(s), err)
