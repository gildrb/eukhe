# eukhe: the proof of LAW idle_exact
# By induction on the gaps: each step picks the same end on the same test.

import Base
import ../../bend/retry.bend as R
import ../../laws/retry_idle.bend as RetryIdle

def ie.sel(late: Bool, +d: Nat, +last: Nat, then: R.Idle) -> {R.idle.sel(late, R.IdleStall{Nat.add(last, d)}, then) == RetryIdle.idle_spec.at(late, d, last, then) : R.Idle}:
  match late:
    case True{}:
      {==}
    case False{}:
      {==}

def ie.go(gs: List<&2, Nat>, +d: Nat, +last: Nat) -> {RetryIdle.idle_spec.go(gs, d, last) == R.idle.go(gs, d, last) : R.Idle}:
  match gs:
    case Nil{}:
      {==}
    case +g <> +rest:
      %ie.go(rest, d, Nat.add(last, g)) : {RetryIdle.idle_spec.at(Nat.is_gt(g, d), d, last, RetryIdle.idle_spec.go(rest, d, Nat.add(last, g))) == R.idle.sel(Nat.is_gt(g, d), R.IdleStall{Nat.add(last, d)}, _) : R.Idle}
      Equal.sym(R.Idle, R.idle.sel(Nat.is_gt(g, d), R.IdleStall{Nat.add(last, d)}, RetryIdle.idle_spec.go(rest, d, Nat.add(last, g))), RetryIdle.idle_spec.at(Nat.is_gt(g, d), d, last, RetryIdle.idle_spec.go(rest, d, Nat.add(last, g))), ie.sel(Nat.is_gt(g, d), d, last, RetryIdle.idle_spec.go(rest, d, Nat.add(last, g))))

def RetryIdle.idle_exact(gs, d):
  match gs:
    case Nil{}:
      {==}
    case +g <> +rest:
      %ie.go(rest, d, g) : {R.idle.sel(Nat.is_gt(g, d), R.IdleStall{d}, _) == RetryIdle.idle_spec.at(Nat.is_gt(g, d), d, 0n, RetryIdle.idle_spec.go(rest, d, g)) : R.Idle}
      ie.sel(Nat.is_gt(g, d), d, 0n, RetryIdle.idle_spec.go(rest, d, g))
