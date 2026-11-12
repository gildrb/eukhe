# eukhe: lemmas the proofs of area supervise share

import Base
import ../../bend/supervise.bend as Su
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/supervise.bend as Supervise
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire
import ../base/nat.bend as LNat

# (D1) the restart budget's entry and span

def ps.ffi_list(+xs: List<&2, Nat>, +r: String, h: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool}) -> {Wr.Got{xs, r} == Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, xs, r)) : Wr.Dec<List<&2, Nat>>}:
  Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, xs, r)), Wr.Got{xs, r}, Wire.wire_list_round_trip(xs, r, h))

# the span from c is the sum of the gaps, then c
def ps.rs_span(gs: List<&2, Nat>, +c: Nat) -> {Su.span.go(gs, c) == Nat.add(Supervise.restart_sum(gs), c) : Nat}:
  match gs:
    case Nil{}:
      {==}
    case +g <> +rest:
      +s = Supervise.restart_sum(rest)
      Equal.trans(Nat, Su.span.go(rest, Nat.add(g, c)), Nat.add(s, Nat.add(g, c)), Nat.add(Nat.add(g, s), c), ps.rs_span(rest, Nat.add(g, c)),
        Equal.trans(Nat, Nat.add(s, Nat.add(g, c)), Nat.add(g, Nat.add(s, c)), Nat.add(Nat.add(g, s), c), LNat.add_lcomm(s, g, c), LNat.add_assoc_r(g, s, c)))
