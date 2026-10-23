# eukhe: the proof of LAW admission_interactive_step

import Base
import ../../bend/admission.bend as Ad
import ../../laws/admission.bend as Admission
import ./base.bend as LA

# Laws (e)
# --------

def interactive_step(s: Ad.St, o: Ad.Op, +w: Nat, ws: {Ad.waits.ia(Ad.status(s, w)) == True{} : Bool}, wf: {Ad.waits.ia(Ad.status(Ad.step(s, o), w)) == True{} : Bool}) -> {Ad.le(Nat.add(Ad.frees(s, o), Ad.ahead(Ad.step(s, o), w)), Ad.ahead(s, w)) == True{} : Bool}:
  LA.aw.step(s, o, w, ws, wf)

def Admission.admission_interactive_step(s, o, w, ws, wf):
  interactive_step(s, o, w, ws, wf)
