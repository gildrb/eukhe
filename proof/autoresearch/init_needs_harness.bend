# eukhe: the proof of LAW init_needs_harness

import Base
import ../../bend/autoresearch/state.bend as ArS
import ../../laws/autoresearch/model.bend as Autoresearch
import ./base/step.bend as AS

def inh.of(old: Maybe<&2, ArS.Cfg>, fresh: Bool, -harness: Bool, -seg: Nat, -mode: ArS.Mode, -runs: List<&2, ArS.Row>, -pend: Maybe<&2, ArS.Pend>, p2: AS.as.harnT(old, fresh, harness), new: {Bool.or(Autoresearch.ar_no_cfg(ArS.St{old, seg, mode, runs, pend}), fresh) == True{} : Bool}) -> {harness == True{} : Bool}:
  match old:
    case None{}:
      p2
    case Some{o}:
      match fresh:
        case True{}:
          p2
        case False{}:
          AS.as.absurd({harness == True{} : Bool}, new)

def inh.h(old: Maybe<&2, ArS.Cfg>, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>, -c: ArS.Cfg, fresh: Bool, -harness: Bool, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, h: AS.as.Init(ArS.Took{s2, eff, stop}, ArS.St{old, seg, mode, runs, pend}, c, fresh, harness), new: {Bool.or(Autoresearch.ar_no_cfg(ArS.St{old, seg, mode, runs, pend}), fresh) == True{} : Bool}) -> {harness == True{} : Bool}:
  (p1, rest) = h
  (p2, rest2) = rest
  inh.of(old, fresh, harness, seg, mode, runs, pend, p2, new)

def Autoresearch.init_needs_harness(s, c, fresh, harness, s2, eff, stop, ok, new):
  match s:
    case ArS.St{+old, +seg, +mode, +runs, +pend}:
      inh.h(old, seg, mode, runs, pend, c, fresh, harness, s2, eff, stop, AS.as.init_took(ArS.St{old, seg, mode, runs, pend}, c, fresh, harness, s2, eff, stop, ok), new)
