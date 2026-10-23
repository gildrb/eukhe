# eukhe: the proof of LAW effort_clamp_idem

import Base
import ../../bend/effort.bend as Ef
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pe.effort_clamp_idem(+m: Ef.Mdl, +l: Ef.Lv) -> {Ef.clamp(m, Ef.clamp(m, l)) == Ef.clamp(m, l) : Ef.Lv}:
  LA.pe.clamp_idem(Ef.offered(m), l)

def Laws.effort_clamp_idem(m, l):
  pe.effort_clamp_idem(m, l)
