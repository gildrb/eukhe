# eukhe: the proof of LAW auth_read_check_is_model
# The entry answers the laws' reply (LAR.ar.answers); on either
# freshness that reply directs the model's check.

import Base
import ../../bend/auth_flight.bend as F
import ../../laws/auth_read.bend as AuthRead
import ./base.bend as LAR

def auth_read_check_is_model.b(b: Bool, +f: Nat, +c: Nat, w: F.W) -> {AuthRead.ar_check_leg(AuthRead.ar_code(AuthRead.ar_pick(b, 0n, 1n)), f, c) == F.Adv.l(F.adv.check(f, F.Sto{c, b}, w)) : F.Leg}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def AuthRead.auth_read_check_is_model(now, r, f, c, w, fnow, fr):
  %LAR.ar.answers(F.AskCheck{}, now, r, fnow, fr) : {AuthRead.ar_check_leg(AuthRead.ar_code(_), f, c) == F.Adv.l(F.adv.check(f, F.Sto{c, AuthRead.ar_fresh(now, r)}, w)) : F.Leg}
  auth_read_check_is_model.b(AuthRead.ar_fresh(now, r), f, c, w)
