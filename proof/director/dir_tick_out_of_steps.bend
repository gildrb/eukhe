# eukhe: the proof of LAW dir_tick_out_of_steps

import Base
import ../../bend/director.bend as Dr
import ../../laws/director.bend as Director
import ./base.bend as LA

# a settle of an outcome: Cont with no step left, Hand, Failed
def pd.settle_cont0(d: Dr.Dec, +s: List<&2, Dr.Layer>, +vs: List<&2, Dr.Verdict>, +cap: Nat, eo: {Dr.Dec.out(d) == Dr.Cont{} : Dr.Out}) -> {Dr.settle(d, 0n, s, vs, cap) == Dr.Loop{0n, Dr.kept(s, vs, cap), Some{Dr.Hand{}}} : Dr.Loop}:
  match d:
    case Dr.Dec{o, t}:
      match o:
        case Dr.Cont{}:
          {==}
        case Dr.Hand{}:
          LA.pd.out_absurd({Dr.settle(Dr.Dec{Dr.Hand{}, t}, 0n, s, vs, cap) == Dr.Loop{0n, Dr.kept(s, vs, cap), Some{Dr.Hand{}}} : Dr.Loop}, Dr.Hand{}, Dr.Cont{}, eo, {==})
        case Dr.Failed{}:
          LA.pd.out_absurd({Dr.settle(Dr.Dec{Dr.Failed{}, t}, 0n, s, vs, cap) == Dr.Loop{0n, Dr.kept(s, vs, cap), Some{Dr.Hand{}}} : Dr.Loop}, Dr.Failed{}, Dr.Cont{}, eo, {==})

def Director.dir_tick_out_of_steps(cap, s, vs, go):
  pd.settle_cont0(Dr.decide(s, vs, cap), s, vs, cap, go)
