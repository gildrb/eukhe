# eukhe: the proof of LAW init_keeps_metric

import Base
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../laws/autoresearch/model.bend as Autoresearch
import ./base/step.bend as AS

def ikm.goal(m: Maybe<&2, ArS.Cfg>, c: ArS.Cfg) -> Type:
  match m:
    case None{}:
      Unit
    case Some{o}:
      {Bool.and(String.eq(ArS.Cfg.metric(o), ArS.Cfg.metric(c)), Autoresearch.ar_dir_eq(ArS.Cfg.dir(o), ArS.Cfg.dir(c))) == True{} : Bool}

def ikm.dir(a: ArS.Dir, b: ArS.Dir) -> {ArP.dir_eq(a, b) == Autoresearch.ar_dir_eq(a, b) : Bool}:
  match a b:
    case ArS.Lower{} ArS.Lower{}:
      {==}
    case ArS.Lower{} ArS.Higher{}:
      {==}
    case ArS.Higher{} ArS.Lower{}:
      {==}
    case ArS.Higher{} ArS.Higher{}:
      {==}

def ikm.of(m: Maybe<&2, ArS.Cfg>, +c: ArS.Cfg, k: AS.as.keepT(m, False{}, c)) -> ikm.goal(m, c):
  match m:
    case None{}:
      Unit{}
    case Some{+o}:
      %ikm.dir(ArS.Cfg.dir(o), ArS.Cfg.dir(c)) : {Bool.and(String.eq(ArS.Cfg.metric(o), ArS.Cfg.metric(c)), _) == True{} : Bool}
      k

def ikm.h(+s: ArS.St, +c: ArS.Cfg, -harness: Bool, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, h: AS.as.Init(ArS.Took{s2, eff, stop}, s, c, False{}, harness)) -> ikm.goal(Autoresearch.ar_cfg(s), c):
  (p1, r1) = h
  (p2, r2) = r1
  (p3, r3) = r2
  (p4, r4) = r3
  (p5, p6) = r4
  ikm.of(Autoresearch.ar_cfg(s), c, p6)

def Autoresearch.init_keeps_metric(s, o, c, harness, s2, eff, stop, old, ok):
  %old : ikm.goal(_, c)
  ikm.h(s, c, harness, s2, eff, stop, AS.as.init_took(s, c, False{}, harness, s2, eff, stop, ok))
