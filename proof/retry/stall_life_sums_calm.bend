# eukhe: the proof of LAW stall_life_sums_calm
# By induction on the gaps, the life walk from `last` adds the sum of the
# gaps before the first one past the deadline to last (rl.go).

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ../base/nat.bend as LNat

def rl.go_sel(over: Bool, +g: Nat, rest: List<&2, Nat>, +d: Nat, +last: Nat, ih: {R.idle.life.go(rest, d, Nat.add(last, g)) == Nat.add(Nat.add(last, g), Retry.rs.sum(Retry.rs.calm(rest, d))) : Nat}) -> {R.idle.life.sel(over, last, R.idle.life.go(rest, d, Nat.add(last, g))) == Nat.add(last, Retry.rs.sum(Retry.rs.calm.keep(over, g, Retry.rs.calm(rest, d)))) : Nat}:
  match over:
    case True{}:
      Equal.sym(Nat, Nat.add(last, 0n), last, LNat.add_zero(last))
    case False{}:
      +S = Retry.rs.sum(Retry.rs.calm(rest, d))
      Equal.trans(Nat, R.idle.life.go(rest, d, Nat.add(last, g)), Nat.add(Nat.add(last, g), S), Nat.add(last, Nat.add(g, S)), ih, LNat.add_assoc(last, g, S))

def rl.go(gs: List<&2, Nat>, +d: Nat, +last: Nat) -> {R.idle.life.go(gs, d, last) == Nat.add(last, Retry.rs.sum(Retry.rs.calm(gs, d))) : Nat}:
  match gs:
    case Nil{}:
      Equal.sym(Nat, Nat.add(last, 0n), last, LNat.add_zero(last))
    case +g <> +rest:
      rl.go_sel(Nat.is_gt(g, d), g, rest, d, last, rl.go(rest, d, Nat.add(last, g)))

def rl.top(over: Bool, +g: Nat, rest: List<&2, Nat>, +d: Nat) -> {R.idle.life.sel(over, 0n, R.idle.life.go(rest, d, g)) == Retry.rs.sum(Retry.rs.calm.keep(over, g, Retry.rs.calm(rest, d))) : Nat}:
  match over:
    case True{}:
      {==}
    case False{}:
      rl.go(rest, d, g)

def life(gs: List<&2, Nat>, +d: Nat) -> {R.idle.life(gs, d) == Retry.rs.sum(Retry.rs.calm(gs, d)) : Nat}:
  match gs:
    case Nil{}:
      {==}
    case +g <> +rest:
      rl.top(Nat.is_gt(g, d), g, rest, d)

def Retry.stall_life_sums_calm(gs, d):
  life(gs, d)
