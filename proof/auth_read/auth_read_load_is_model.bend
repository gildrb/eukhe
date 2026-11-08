# eukhe: the proof of LAW auth_read_load_is_model
# The entry answers the laws' reply (LAR.ar.answers); on either
# freshness that reply directs the model's load.

import Base
import ../../bend/auth_flight.bend as F
import ../../laws/auth_read.bend as AuthRead
import ./base.bend as LAR

def auth_read_load_is_model.b(b: Bool, +c: Nat, w: F.W) -> {AuthRead.ar_load_leg(AuthRead.ar_code(AuthRead.ar_pick(b, 0n, 1n)), c) == F.Adv.l(F.adv.load(F.Sto{c, b}, w)) : F.Leg}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def AuthRead.auth_read_load_is_model(now, e, c, w, fnow, fe):
  %LAR.ar.answers(F.AskLoad{}, now, F.Oauth{e}, fnow, fe) : {AuthRead.ar_load_leg(AuthRead.ar_code(_), c) == F.Adv.l(F.adv.load(F.Sto{c, AuthRead.ar_fresh(now, F.Oauth{e})}, w)) : F.Leg}
  auth_read_load_is_model.b(Nat.is_lt(now, e), c, w)
