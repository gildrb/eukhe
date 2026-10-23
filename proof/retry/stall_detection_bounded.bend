# eukhe: the proof of LAW stall_detection_bounded

import Base
import ../../bend/retry.bend as R
import ../../LAWS.bend as Laws
import ./base.bend as LA

# the bound after one more event, given the bound of the events after it
def rp.idle_next(over: Bool, +g: Nat, rest: List<&2, Nat>, +d: Nat, +last: Nat, ih: {Nat.is_le(R.Idle.at(R.idle.go(rest, d, Nat.add(last, g))), Nat.add(R.idle.life.go(rest, d, Nat.add(last, g)), d)) == True{} : Bool}) -> {Nat.is_le(R.Idle.at(R.idle.sel(over, R.IdleStall{Nat.add(last, d)}, R.idle.go(rest, d, Nat.add(last, g)))), Nat.add(R.idle.life.sel(over, last, R.idle.life.go(rest, d, Nat.add(last, g))), d)) == True{} : Bool}:
  match over:
    case True{}:
      LA.rp.le_refl(Nat.add(last, d))
    case False{}:
      ih

def rp.idle_go(gs: List<&2, Nat>, +d: Nat, +last: Nat) -> {Nat.is_le(R.Idle.at(R.idle.go(gs, d, last)), Nat.add(R.idle.life.go(gs, d, last), d)) == True{} : Bool}:
  match gs:
    case Nil{}:
      LA.rp.le_add(last, d)
    case +g <> +rest:
      rp.idle_next(Nat.is_gt(g, d), g, rest, d, last, rp.idle_go(rest, d, Nat.add(last, g)))

def detection_bounded(gs: List<&2, Nat>, +d: Nat) -> {Nat.is_le(R.Idle.at(R.idle(gs, d)), Nat.add(R.idle.life(gs, d), d)) == True{} : Bool}:
  match gs:
    case Nil{}:
      LA.rp.le_refl(d)
    case +g <> +rest:
      rp.idle_next(Nat.is_gt(g, d), g, rest, d, 0n, rp.idle_go(rest, d, g))

def Laws.stall_detection_bounded(gs, d):
  detection_bounded(gs, d)
