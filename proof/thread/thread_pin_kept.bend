# eukhe: the proof of LAW thread_pin_kept
#
# PROOF: the pin's head equals the call's (thb.eq_refl), so the pin keeps
# its own view.

import Base
import ../../bend/thread.bend as Th
import ../../laws/thread.bend as Thread
import ./base.bend as LA

def Thread.thread_pin_kept(h, view, fresh):
  %Equal.sym(Bool, Nat.is_eq(h, h), True{}, LA.thb.eq_refl(h)) : {Th.pin.keep(_, Th.Pin{h, view}, h, fresh) == Th.Pin{h, view} : Th.Pin}
  {==}
