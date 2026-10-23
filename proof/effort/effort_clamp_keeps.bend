# eukhe: the proof of LAW effort_clamp_keeps

import Base
import ../../bend/effort.bend as Ef
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pe.effort_clamp_keeps(+m: Ef.Mdl, +l: Ef.Lv, in: {Ef.has(Ef.offered(m), l) == True{} : Bool}) -> {Ef.clamp(m, l) == l : Ef.Lv}:
  LA.pe.clamp_keep(Ef.offered(m), l, in)

def Laws.effort_clamp_keeps(m, l, in):
  pe.effort_clamp_keeps(m, l, in)
