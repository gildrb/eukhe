# eukhe: the proof of LAW dir_tick_hands_back

import Base
import ../../bend/director.bend as Dr
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pd.settle_hand(d: Dr.Dec, +n: Nat, +s: List<&2, Dr.Layer>, +vs: List<&2, Dr.Verdict>, +cap: Nat, eo: {Dr.Dec.out(d) == Dr.Hand{} : Dr.Out}) -> {Dr.settle(d, n, s, vs, cap) == Dr.Loop{n, Dr.kept(s, vs, cap), Some{Dr.Hand{}}} : Dr.Loop}:
  match d:
    case Dr.Dec{o, t}:
      match o:
        case Dr.Cont{}:
          LA.pd.out_absurd({Dr.settle(Dr.Dec{Dr.Cont{}, t}, n, s, vs, cap) == Dr.Loop{n, Dr.kept(s, vs, cap), Some{Dr.Hand{}}} : Dr.Loop}, Dr.Cont{}, Dr.Hand{}, eo, {==})
        case Dr.Hand{}:
          {==}
        case Dr.Failed{}:
          LA.pd.out_absurd({Dr.settle(Dr.Dec{Dr.Failed{}, t}, n, s, vs, cap) == Dr.Loop{n, Dr.kept(s, vs, cap), Some{Dr.Hand{}}} : Dr.Loop}, Dr.Failed{}, Dr.Hand{}, eo, {==})

def Laws.dir_tick_hands_back(cap, n, s, vs, h):
  pd.settle_hand(Dr.decide(s, vs, cap), n, s, vs, cap, h)
