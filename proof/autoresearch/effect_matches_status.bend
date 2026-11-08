# eukhe: the proof of LAW effect_matches_status

import Base
import ../../bend/autoresearch/state.bend as ArS
import ../../laws/autoresearch/model.bend as Autoresearch
import ./base/step.bend as AS

def ems.of(+s: ArS.St, +e: ArS.Ev, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, g: AS.as.Gen(ArS.Took{s2, eff, stop}, s, e, 0n)) -> {eff == Autoresearch.ar_effect(e) : ArS.Eff}:
  (a, r1) = g
  (b, r2) = r1
  b

def Autoresearch.effect_matches_status(s, e, s2, eff, stop, ok):
  ems.of(s, e, s2, eff, stop, AS.as.gen_took(s, e, 0n, s2, eff, stop, ok))
