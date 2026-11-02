# eukhe: the proof of LAW stall_life_exact

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry

def rp.life_sel(over: Bool, +last: Nat, +x: Nat) -> {R.idle.life.sel(over, last, x) == Retry.rs.life.at(over, last, x) : Nat}:
  match over:
    case True{}:
      {==}
    case False{}:
      {==}

def rp.life_go(gs: List<&2, Nat>, +d: Nat, +last: Nat) -> {R.idle.life.go(gs, d, last) == Retry.rs.life.go(gs, d, last) : Nat}:
  match gs:
    case Nil{}:
      {==}
    case +g <> +rest:
      %rp.life_go(rest, d, Nat.add(last, g)) : {R.idle.life.sel(Nat.is_gt(g, d), last, R.idle.life.go(rest, d, Nat.add(last, g))) == Retry.rs.life.at(Nat.is_gt(g, d), last, _) : Nat}
      rp.life_sel(Nat.is_gt(g, d), last, R.idle.life.go(rest, d, Nat.add(last, g)))

def life_exact(gs: List<&2, Nat>, +d: Nat) -> {R.idle.life(gs, d) == Retry.rs.life(gs, d) : Nat}:
  match gs:
    case Nil{}:
      {==}
    case +g <> +rest:
      %rp.life_go(rest, d, g) : {R.idle.life.sel(Nat.is_gt(g, d), 0n, R.idle.life.go(rest, d, g)) == Retry.rs.life.at(Nat.is_gt(g, d), 0n, _) : Nat}
      rp.life_sel(Nat.is_gt(g, d), 0n, R.idle.life.go(rest, d, g))

def Retry.stall_life_exact(gs, d):
  life_exact(gs, d)
