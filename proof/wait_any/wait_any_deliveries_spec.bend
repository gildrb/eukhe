# eukhe: the proof of LAW wait_any_deliveries_spec
#
# PROOF: induction on the events: each step is the spec's (wait_any_step_spec), its deliveries and next state read alike (wa.dl_out).

import Base
import ../../bend/wait_any.bend as Wa
import ../../spec/durable/wait_any.bend as WaSpec
import ../../laws/wait_any.bend as WaitAny
import ./base.bend as LW
import ./wait_any_step_spec.bend as PWaitAnyStepSpec

def wa.dl_out(o: Wa.Out, rest: List<&2, Wa.Ev>, +wake: Bool, ih: @dd: Wa.D -> {Wa.deliveries(rest, wake, dd) == WaSpec.deliveries(rest, wake, dd) : Nat})
  -> {Nat.add(Wa.Out.k(o), Wa.deliveries(rest, wake, Wa.Out.d(o))) == Nat.add(WaSpec.out_k(o), WaSpec.deliveries(rest, wake, WaSpec.out_d(o))) : Nat}:
  match o:
    case Wa.Out{+dd, +k}:
      %ih(dd) : {Nat.add(k, Wa.deliveries(rest, wake, dd)) == Nat.add(k, _) : Nat}
      {==}

def wa.dels(es: List<&2, Wa.Ev>, +wake: Bool, +d: Wa.D) -> {Wa.deliveries(es, wake, d) == WaSpec.deliveries(es, wake, d) : Nat}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      %WaitAny.wait_any_step_spec(wake, d, e) : {Nat.add(Wa.Out.k(Wa.step(wake, d, e)), Wa.deliveries(rest, wake, Wa.Out.d(Wa.step(wake, d, e)))) == Nat.add(WaSpec.out_k(_), WaSpec.deliveries(rest, wake, WaSpec.out_d(_))) : Nat}
      wa.dl_out(Wa.step(wake, d, e), rest, wake, dd => wa.dels(rest, wake, dd))

def WaitAny.wait_any_deliveries_spec(es, wake, d):
  wa.dels(es, wake, d)
