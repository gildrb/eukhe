# eukhe: the proof of LAW auth_read_store_is_model
# The entry answers the laws' reply (LAR.ar.answers); on either
# freshness of the peer's credential that reply directs the model's store.

import Base
import ../../bend/auth_flight.bend as F
import ../../laws/auth_read.bend as AuthRead
import ./base.bend as LAR

def auth_read_store_is_model.b(b: Bool, +f: Nat, +p: Nat, +c: Nat, +fl: Bool, +ld: List<&2, F.Out>, +n: Nat) -> {AuthRead.ar_store_adv(AuthRead.ar_code(AuthRead.ar_pick(b, 3n, 4n)), f, p, c, b, fl, ld, n) == F.adv.store(f, c, F.W{F.Sto{p, b}, fl, ld, n}) : F.Adv}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def AuthRead.auth_read_store_is_model(now, r, f, p, c, fl, ld, n, fnow, fr):
  %LAR.ar.answers(F.AskStore{}, now, r, fnow, fr) : {AuthRead.ar_store_adv(AuthRead.ar_code(_), f, p, c, AuthRead.ar_fresh(now, r), fl, ld, n) == F.adv.store(f, c, F.W{F.Sto{p, AuthRead.ar_fresh(now, r)}, fl, ld, n}) : F.Adv}
  auth_read_store_is_model.b(AuthRead.ar_fresh(now, r), f, p, c, fl, ld, n)
