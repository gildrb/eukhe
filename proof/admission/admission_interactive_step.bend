# eukhe: the proof of LAW admission_interactive_step

import Base
import ../../bend/admission.bend as Ad
import ../../laws/admission.bend as Admission
import ./base/admission/waits.bend as LAAdmissionWaits
import ./base/admission/terms.bend as AT
import ./base/admission/bridge.bend as LBr
import ./base/admission/count.bend as PC

# Laws (e)
# --------

def interactive_step(s: Ad.St, o: Ad.Op, +w: Nat, ws: {Admission.adm_waits_ia(Admission.adm_status(s, w)) == True{} : Bool}, wf: {Admission.adm_waits_ia(Admission.adm_status(Ad.step(s, o), w)) == True{} : Bool}) -> {Ad.le(Nat.add(Admission.adm_frees(s, o), AT.ahead(Ad.step(s, o), w)), AT.ahead(s, w)) == True{} : Bool}:
  LAAdmissionWaits.aw.step(s, o, w, ws, wf)

def Admission.admission_interactive_step(s, o, w, ws, wf):
  %LBr.br.ahead(Ad.step(s, o), w) : {Nat.is_le(Nat.add(Admission.adm_frees(s, o), _), Admission.adm_ahead(s, w)) == True{} : Bool}
  %LBr.br.ahead(s, w) : {Nat.is_le(Nat.add(Admission.adm_frees(s, o), AT.ahead(Ad.step(s, o), w)), _) == True{} : Bool}
  %PC.pac.le(Nat.add(Admission.adm_frees(s, o), AT.ahead(Ad.step(s, o), w)), AT.ahead(s, w)) : {_ == True{} : Bool}
  interactive_step(s, o, w, ws, wf)
