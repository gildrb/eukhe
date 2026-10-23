# eukhe: lemmas the proofs of area supervise share

import Base
import ../../bend/supervise.bend as Su
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/supervise.bend as Supervise
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire

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
