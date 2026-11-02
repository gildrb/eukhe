# eukhe: lemmas the proofs of area supervise share

import Base
import ../../bend/supervise.bend as Su
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/supervise.bend as Supervise
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire
import ../base/nat.bend as LNat

# (D1) the restart decision and the orphan exit window

# the budget's window is the spec's: keep after older, in one pass
def ps.rs_window_put(b: Bool, +x: Nat, r: List<&2, Nat>) -> {Su.keep.put(b, x, r) == Supervise.restart_window_put(b, x, r) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ps.rs_window(+w: Nat, +g: Nat, a: List<&2, Nat>) -> {Su.keep(w, Su.older(g, a)) == Supervise.restart_window(w, g, a) : List<&2, Nat>}:
  match a:
    case Nil{}:
      {==}
    case +x <> +t:
      %ps.rs_window(w, g, t) : {Su.keep.put(Nat.is_lt(Nat.add(g, x), w), Nat.add(g, x), Su.keep(w, Su.older(g, t))) == Supervise.restart_window_put(Nat.is_lt(Nat.add(g, x), w), Nat.add(g, x), _) : List<&2, Nat>}
      ps.rs_window_put(Nat.is_lt(Nat.add(g, x), w), Nat.add(g, x), Su.keep(w, Su.older(g, t)))

def ps.ffi_list(+xs: List<&2, Nat>, +r: String, h: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool}) -> {Wr.Got{xs, r} == Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, xs, r)) : Wr.Dec<List<&2, Nat>>}:
  Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, xs, r)), Wr.Got{xs, r}, Wire.wire_list_round_trip(xs, r, h))

# the budget's step is the spec's
def ps.rs_step(+c: Su.Cfg, +s: Su.St, +g: Nat) -> {Su.step(c, s, g) == Supervise.restart_step(c, s, g) : Su.St}:
  match c:
    case Su.Cfg{k, +w, b, m}:
      match s:
        case Su.St{a, n}:
          %ps.rs_window(w, g, a) : {Su.St{0n <> Su.keep(w, Su.older(g, a)), 1n+List.length(&2, Nat, Su.keep(w, Su.older(g, a)))} == Su.St{0n <> _, 1n+List.length(&2, Nat, _)} : Su.St}
          {==}

# the budget's run is the spec's fold of the step
def ps.rs_go(+c: Su.Cfg, gs: List<&2, Nat>, +s: Su.St) -> {Su.go(c, gs, s) == Supervise.restart_go(c, gs, s) : Su.St}:
  match gs:
    case Nil{}:
      {==}
    case +g <> rest:
      %ps.rs_step(c, s, g) : {Su.go(c, rest, Su.step(c, s, g)) == Supervise.restart_go(c, rest, _) : Su.St}
      ps.rs_go(c, rest, Su.step(c, s, g))

# the budget's count is the spec's
def ps.rs_count(s: Su.St) -> {Su.St.n(s) == Supervise.restart_count(s) : Nat}:
  match s:
    case Su.St{a, n}:
      {==}

# the span from c is the sum of the gaps, then c
def ps.rs_span(gs: List<&2, Nat>, +c: Nat) -> {Su.span.go(gs, c) == Nat.add(Supervise.restart_sum(gs), c) : Nat}:
  match gs:
    case Nil{}:
      {==}
    case +g <> +rest:
      +s = Supervise.restart_sum(rest)
      Equal.trans(Nat, Su.span.go(rest, Nat.add(g, c)), Nat.add(s, Nat.add(g, c)), Nat.add(Nat.add(g, s), c), ps.rs_span(rest, Nat.add(g, c)),
        Equal.trans(Nat, Nat.add(s, Nat.add(g, c)), Nat.add(g, Nat.add(s, c)), Nat.add(Nat.add(g, s), c), LNat.add_lcomm(s, g, c), LNat.add_assoc_r(g, s, c)))
