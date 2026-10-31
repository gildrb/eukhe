# eukhe: the proof of LAW segment_monotone

import Base
import ../../bend/autoresearch/state.bend as ArS
import ../../laws/autoresearch/model.bend as Autoresearch
import ./base/step.bend as AS

def sm.of(+s: ArS.St, +e: ArS.Ev, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, g: AS.as.Gen(ArS.Took{s2, eff, stop}, s, e, 0n)) -> {Autoresearch.ar_seg(s2) == Nat.add(Autoresearch.ar_seg(s), Autoresearch.ar_bump(s, e)) : Nat}:
  (a, rest) = g
  a

def Autoresearch.segment_monotone(s, e, s2, eff, stop, ok):
  sm.of(s, e, s2, eff, stop, AS.as.gen_took(s, e, 0n, s2, eff, stop, ok))
