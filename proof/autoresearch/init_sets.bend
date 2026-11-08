# eukhe: the proof of LAW init_sets

import Base
import ../../bend/autoresearch/state.bend as ArS
import ../../spec/autoresearch/metric_line.bend as SL
import ../../laws/autoresearch/model.bend as Autoresearch
import ./base/step.bend as AS

def is.of(+s: ArS.St, +c: ArS.Cfg, +fresh: Bool, +harness: Bool, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, h: AS.as.Init(ArS.Took{s2, eff, stop}, s, c, fresh, harness))
  -> {Bool.and(Bool.and(SL.nonempty(ArS.Cfg.metric(c)), SL.all_name(ArS.Cfg.metric(c))), Autoresearch.ar_cap_ok(ArS.Cfg.max(c))) == True{} : Bool} & {s2 == ArS.St{Some{c}, Nat.add(Autoresearch.ar_seg(s), Autoresearch.ar_bump(s, ArS.Init{c, fresh, harness})), ArS.On{}, ArS.snoc(Autoresearch.ar_runs(s), Autoresearch.ar_gone(s)), None{}} : ArS.St}:
  (p1, rest) = h
  (p2, rest2) = rest
  (p3, rest3) = rest2
  (p1, p3)

def Autoresearch.init_sets(s, c, fresh, harness, s2, eff, stop, ok):
  is.of(s, c, fresh, harness, s2, eff, stop, AS.as.init_took(s, c, fresh, harness, s2, eff, stop, ok))
