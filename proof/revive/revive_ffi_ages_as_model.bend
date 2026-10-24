# eukhe: the proof of LAW revive_ffi_ages_as_model
# The entry answers the spec's reply (Revive.revive_ffi_answers); with no
# other veto that is the spec's freshness of the stamp, and a stamp at
# `at` read at at + a is not in the future (at <= at + a) and a ms old
# ((at + a) - at = a, PRvAges.rva.sub): Rv.fresh(m, a).

import Base
import ../../bend/ffi_revive.bend as FR
import ../../bend/revive.bend as Rv
import ../../laws/revive.bend as Revive
import ./revive_ffi_answers.bend as PRvAnswers
import ./revive_veto_ages_as_model.bend as PRvAges

# at is at most at + a
def rfm.le(at: Nat, +a: Nat) -> {True{} == Nat.is_le(at, Nat.add(at, a)) : Bool}:
  match at:
    case 0n:
      PRvAges.rva.le0(a)
    case 1n+p:
      rfm.le(p, a)

def Revive.revive_ffi_ages_as_model(at, a, m, k, fits):
  +f = {Rv.Facts{False{}, False{}, None{}, Rv.Stamp{at}, Nat.add(at, a), m, k} : Rv.Facts}
  %Equal.sym(String, FR.ffi(Revive.rv_spell(f)), Revive.rv_reply(f), Revive.revive_ffi_answers(f, fits)) : {_ == Revive.rv_reply.fresh(Rv.fresh(m, a)) : String}
  %rfm.le(at, a) : {Revive.rv_reply.fresh(Revive.rv_fresh.of(_, at, Nat.add(at, a), m, k)) == Revive.rv_reply.fresh(Rv.fresh(m, a)) : String}
  %PRvAges.rva.sub(at, a) : {Revive.rv_reply.fresh(Nat.is_le(_, m)) == Revive.rv_reply.fresh(Rv.fresh(m, a)) : String}
  {==}
