# eukhe: the proof of LAW flag_monotone

import Base
import ../../bend/autoresearch/state.bend as ArS
import ../../laws/autoresearch/model.bend as Autoresearch
import ./base/step.bend as AS

def fm.of(+s: ArS.St, +e: ArS.Ev, +id: Nat, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, g: AS.as.Gen(ArS.Took{s2, eff, stop}, s, e, id), was: {Autoresearch.ar_flagged(Autoresearch.ar_runs(s), id) == True{} : Bool})
  -> {Autoresearch.ar_flagged(Autoresearch.ar_runs(s2), id) == True{} : Bool}:
  (a, r1) = g
  (b, r2) = r1
  (c, f) = r2
  f(was)

def Autoresearch.flag_monotone(s, e, s2, eff, stop, id, ok, was):
  fm.of(s, e, id, s2, eff, stop, AS.as.gen_took(s, e, id, s2, eff, stop, ok), was)
