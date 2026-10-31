# eukhe: the proof of LAW cap_stops

import Base
import ../../bend/autoresearch/state.bend as ArS
import ../../laws/autoresearch/model.bend as Autoresearch
import ./base/step.bend as AS

def cs.of(+s: ArS.St, +e: ArS.Ev, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, g: AS.as.Gen(ArS.Took{s2, eff, stop}, s, e, 0n))
  -> {stop == Bool.and(Autoresearch.ar_is_log(e), Autoresearch.ar_capped(Autoresearch.ar_cfg(s2), ArS.St.logged(s2))) : Bool} & {Autoresearch.ar_mode(s2) == Autoresearch.ar_mode_after(e, stop, Autoresearch.ar_mode(s)) : ArS.Mode}:
  (a, r1) = g
  (b, r2) = r1
  (c, r3) = r2
  c

def Autoresearch.cap_stops(s, e, s2, eff, stop, ok):
  cs.of(s, e, s2, eff, stop, AS.as.gen_took(s, e, 0n, s2, eff, stop, ok))
