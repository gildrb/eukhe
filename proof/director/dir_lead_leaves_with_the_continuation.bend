# eukhe: the proof of LAW dir_lead_leaves_with_the_continuation

import Base
import ../../bend/director.bend as Dr
import ../../laws/director.bend as Director
import ../base.bend as L
import ./base.bend as LA

# a settle that goes on does not read the verdicts again
def pd.goon_on(n: Nat, +t: List<&2, Dr.Layer>, +s: List<&2, Dr.Layer>, +vs1: List<&2, Dr.Verdict>, +vs2: List<&2, Dr.Verdict>, +cap: Nat, on: {Dr.ended(Dr.go.on(n, t, s, vs2, cap)) == False{} : Bool}) -> {Dr.go.on(n, t, s, vs1, cap) == Dr.go.on(n, t, s, vs2, cap) : Dr.Loop}:
  match n:
    case 0n:
      L.cvar.pv.absurd({Dr.go.on(0n, t, s, vs1, cap) == Dr.go.on(0n, t, s, vs2, cap) : Dr.Loop}, on)
    case 1n+m:
      {==}

def pd.settle_on(d: Dr.Dec, +n: Nat, +s: List<&2, Dr.Layer>, +vs1: List<&2, Dr.Verdict>, +vs2: List<&2, Dr.Verdict>, +cap: Nat, on: {Dr.ended(Dr.settle(d, n, s, vs2, cap)) == False{} : Bool}) -> {Dr.settle(d, n, s, vs1, cap) == Dr.settle(d, n, s, vs2, cap) : Dr.Loop}:
  match d:
    case Dr.Dec{o, +t}:
      match o:
        case Dr.Cont{}:
          pd.goon_on(n, t, s, vs1, vs2, cap, on)
        case Dr.Hand{}:
          L.cvar.pv.absurd({Dr.settle(Dr.Dec{Dr.Hand{}, t}, n, s, vs1, cap) == Dr.settle(Dr.Dec{Dr.Hand{}, t}, n, s, vs2, cap) : Dr.Loop}, on)
        case Dr.Failed{}:
          L.cvar.pv.absurd({Dr.settle(Dr.Dec{Dr.Failed{}, t}, n, s, vs1, cap) == Dr.settle(Dr.Dec{Dr.Failed{}, t}, n, s, vs2, cap) : Dr.Loop}, on)

def Director.dir_lead_leaves_with_the_continuation(cap, l, vs, on):
  match l:
    case Dr.Loop{+n, +s, e}:
      match e:
        case None{}:
          +L = Director.dir_leads(vs, Dr.Leave{})
          +r = Nat.is_lt(List.length(&2, Dr.Layer, s), cap)
          %Equal.sym(Dr.Dec, Dr.decide.go(s, vs, r, False{}), Dr.decide.go(s, L, r, False{}), LA.pd.leave_as(s, vs, r, False{})) : {Dr.settle(_, n, s, vs, cap) == Dr.settle(Dr.decide(s, L, cap), n, s, L, cap) : Dr.Loop}
          pd.settle_on(Dr.decide(s, L, cap), n, s, vs, L, cap, on)
        case Some{x}:
          {==}
