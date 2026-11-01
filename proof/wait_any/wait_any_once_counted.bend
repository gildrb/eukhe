# eukhe: the proof of LAW wait_any_once_counted
#
# PROOF: the laws' count of the code's steps is the code's own count (wa.cnt), and no events deliver more than the one a fresh job has left (wa.once_go).

import Base
import ../../bend/wait_any.bend as Wa
import ../../spec/durable/wait_any.bend as WaSpec
import ../../laws/wait_any.bend as WaitAny
import ./base.bend as LW


def wa.cnt_out(o: Wa.Out, rest: List<&2, Wa.Ev>, +wake: Bool, ih: @dd: Wa.D -> {WaitAny.wa_count(rest, wake, dd) == Wa.deliveries(rest, wake, dd) : Nat})
  -> {Nat.add(WaSpec.out_k(o), WaitAny.wa_count(rest, wake, WaSpec.out_d(o))) == Nat.add(Wa.Out.k(o), Wa.deliveries(rest, wake, Wa.Out.d(o))) : Nat}:
  match o:
    case Wa.Out{+dd, +k}:
      %ih(dd) : {Nat.add(k, WaitAny.wa_count(rest, wake, dd)) == Nat.add(k, _) : Nat}
      {==}

def wa.cnt(es: List<&2, Wa.Ev>, +wake: Bool, +d: Wa.D) -> {WaitAny.wa_count(es, wake, d) == Wa.deliveries(es, wake, d) : Nat}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      wa.cnt_out(Wa.step(wake, d, e), rest, wake, dd => wa.cnt(rest, wake, dd))

def WaitAny.wait_any_once_counted(wake, es):
  %Equal.sym(Nat, WaitAny.wa_count(es, wake, WaSpec.fresh()), Wa.deliveries(es, wake, Wa.fresh()), wa.cnt(es, wake, WaSpec.fresh())) : {Nat.is_le(_, 1n) == True{} : Bool}
  LW.wa.once_go(es, wake, Wa.fresh())
