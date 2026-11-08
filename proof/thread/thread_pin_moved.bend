# eukhe: the proof of LAW thread_pin_moved
#
# PROOF: the pin's head differs from the call's (the premise), so the call
# pins the fresh render under its head.

import Base
import ../../bend/thread.bend as Th
import ../../laws/thread.bend as Thread

def Thread.thread_pin_moved(p, h, fresh, moved):
  match p:
    case Th.Pin{+h0, +v}:
      %Equal.sym(Bool, Nat.is_eq(h0, h), False{}, moved) : {Th.pin.keep(_, Th.Pin{h0, v}, h, fresh) == Th.Pin{h, fresh} : Th.Pin}
      {==}
