# eukhe: the proof of LAW stall_ends_exact
# By induction on the gaps (re.go): the walk from `last` ends as the end
# of its gaps read whole (re.acc of whether a gap is past the deadline, the
# sum of the gaps before the first such one, and the sum of all), shifted
# by last (re.shift). The stream's walk is the walk from 0 (re.top).

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ../base/nat.bend as LNat

# how the walk from last ends: stalled d after last plus the calm gaps c,
# or closed at last plus all the gaps t
def re.acc(late: Bool, +c: Nat, +t: Nat, +d: Nat, +last: Nat) -> R.Idle:
  match late:
    case True{}:
      R.IdleStall{Nat.add(Nat.add(last, c), d)}
    case False{}:
      R.IdleClose{Nat.add(last, t)}

# a walk from last + g is the walk from last with g more of every sum
def re.shift(late: Bool, +c: Nat, +t: Nat, +d: Nat, +last: Nat, +g: Nat) -> {re.acc(late, c, t, d, Nat.add(last, g)) == re.acc(late, Nat.add(g, c), Nat.add(g, t), d, last) : R.Idle}:
  match late:
    case True{}:
      Equal.cong(Nat, R.Idle, x => R.IdleStall{Nat.add(x, d)}, Nat.add(Nat.add(last, g), c), Nat.add(last, Nat.add(g, c)), LNat.add_assoc(last, g, c))
    case False{}:
      Equal.cong(Nat, R.Idle, x => R.IdleClose{x}, Nat.add(Nat.add(last, g), t), Nat.add(last, Nat.add(g, t)), LNat.add_assoc(last, g, t))

def re.step(over: Bool, +g: Nat, +rest: List<&2, Nat>, +d: Nat, +last: Nat, ih: {R.idle.go(rest, d, Nat.add(last, g)) == re.acc(Retry.rs.past(rest, d), Retry.rs.sum(Retry.rs.calm(rest, d)), Retry.rs.sum(rest), d, Nat.add(last, g)) : R.Idle}) -> {R.idle.sel(over, R.IdleStall{Nat.add(last, d)}, R.idle.go(rest, d, Nat.add(last, g))) == re.acc(Bool.or(over, Retry.rs.past(rest, d)), Retry.rs.sum(Retry.rs.calm.keep(over, g, Retry.rs.calm(rest, d))), Nat.add(g, Retry.rs.sum(rest)), d, last) : R.Idle}:
  match over:
    case True{}:
      Equal.cong(Nat, R.Idle, x => R.IdleStall{Nat.add(x, d)}, last, Nat.add(last, 0n), Equal.sym(Nat, Nat.add(last, 0n), last, LNat.add_zero(last)))
    case False{}:
      +L = Retry.rs.past(rest, d)
      +C = Retry.rs.sum(Retry.rs.calm(rest, d))
      +T = Retry.rs.sum(rest)
      Equal.trans(R.Idle, R.idle.go(rest, d, Nat.add(last, g)), re.acc(L, C, T, d, Nat.add(last, g)), re.acc(L, Nat.add(g, C), Nat.add(g, T), d, last), ih, re.shift(L, C, T, d, last, g))

def re.go(gs: List<&2, Nat>, +d: Nat, +last: Nat) -> {R.idle.go(gs, d, last) == re.acc(Retry.rs.past(gs, d), Retry.rs.sum(Retry.rs.calm(gs, d)), Retry.rs.sum(gs), d, last) : R.Idle}:
  match gs:
    case Nil{}:
      Equal.cong(Nat, R.Idle, x => R.IdleClose{x}, last, Nat.add(last, 0n), Equal.sym(Nat, Nat.add(last, 0n), last, LNat.add_zero(last)))
    case +g <> +rest:
      re.step(Nat.is_gt(g, d), g, rest, d, last, re.go(rest, d, Nat.add(last, g)))

# the walk from 0 ends as the spec's end
def re.top(late: Bool, +gs: List<&2, Nat>, +d: Nat) -> {re.acc(late, Retry.rs.sum(Retry.rs.calm(gs, d)), Retry.rs.sum(gs), d, 0n) == Retry.rs.end.of(late, gs, d) : R.Idle}:
  match late:
    case True{}:
      {==}
    case False{}:
      {==}

def ends(gs: List<&2, Nat>, +d: Nat) -> {R.idle(gs, d) == Retry.rs.end(gs, d) : R.Idle}:
  match gs:
    case Nil{}:
      {==}
    case +g <> +rest:
      +L = Retry.rs.past(g <> rest, d)
      Equal.trans(R.Idle, R.idle(g <> rest, d), re.acc(L, Retry.rs.sum(Retry.rs.calm(g <> rest, d)), Retry.rs.sum(g <> rest), d, 0n), Retry.rs.end(g <> rest, d), re.step(Nat.is_gt(g, d), g, rest, d, 0n, re.go(rest, d, g)), re.top(L, g <> rest, d))

def Retry.stall_ends_exact(gs, d):
  ends(gs, d)
