# eukhe: the proof of LAW effort_clamp_offered

import Base
import ../../bend/effort.bend as Ef
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pe.effort_clamp_offered(+m: Ef.Mdl, +l: Ef.Lv, ne: {Ef.empty(Ef.offered(m)) == False{} : Bool}) -> {Ef.has(Ef.offered(m), Ef.clamp(m, l)) == True{} : Bool}:
  LA.pe.clamp_in(Ef.offered(m), l, ne)

def Laws.effort_clamp_offered(m, l, ne):
  pe.effort_clamp_offered(m, l, ne)
