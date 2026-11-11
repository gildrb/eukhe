# eukhe: the proof of LAW dir_tick_fails

import Base
import ../../bend/director.bend as Dr
import ../../laws/director.bend as Director
import ./base.bend as LA

def pd.settle_failed(d: Dr.Dec, +n: Nat, +s: List<&2, Dr.Layer>, +vs: List<&2, Dr.Verdict>, +cap: Nat, eo: {Dr.Dec.out(d) == Dr.Failed{} : Dr.Out}) -> {Dr.settle(d, n, s, vs, cap) == Dr.Loop{n, Dr.kept(s, vs, cap), Some{Dr.Failed{}}} : Dr.Loop}:
  match d:
    case Dr.Dec{o, t}:
      match o:
        case Dr.Cont{}:
          LA.pd.out_absurd({Dr.settle(Dr.Dec{Dr.Cont{}, t}, n, s, vs, cap) == Dr.Loop{n, Dr.kept(s, vs, cap), Some{Dr.Failed{}}} : Dr.Loop}, Dr.Cont{}, Dr.Failed{}, eo, {==})
        case Dr.Hand{}:
          LA.pd.out_absurd({Dr.settle(Dr.Dec{Dr.Hand{}, t}, n, s, vs, cap) == Dr.Loop{n, Dr.kept(s, vs, cap), Some{Dr.Failed{}}} : Dr.Loop}, Dr.Hand{}, Dr.Failed{}, eo, {==})
        case Dr.Failed{}:
          {==}

def Director.dir_tick_fails(cap, n, s, vs, f):
  pd.settle_failed(Dr.decide(s, vs, cap), n, s, vs, cap, f)
