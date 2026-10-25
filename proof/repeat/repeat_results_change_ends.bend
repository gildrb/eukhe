# eukhe: the proof of LAW repeat_results_change_ends

import Base
import ../../bend/repeat.bend as Rp
import ../../bend/ffi_repeat.bend as FRp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/wire.bend as LWire
import ../../laws/repeat.bend as Repeat
import ./base.bend as LARepeat

# PROOF of LAW repeat_results_change_ends: the round's calls equal the first round's (rp.eq_refl), its results do not (ne, rp.same), so the walk stops with the count (rp.stop_eq).

def Repeat.repeat_results_change_ends(want, k, s, rs0, pend, ne):
  %Equal.sym(Bool, Nat.is_eq(s, s), True{}, LARepeat.rp.eq_refl(s)) : {Rp.called.pick(Bool.and(_, Rp.same(pend, rs0)), want, k, Some{Rp.Round{s, rs0}}, s, pend) == Rp.Stops{Repeat.clip(1n+k)} : Rp.Next}
  %Equal.sym(Bool, Rp.same(pend, rs0), Repeat.ids_eq(pend, rs0), LARepeat.rp.same(pend, rs0)) : {Rp.called.pick(_, want, k, Some{Rp.Round{s, rs0}}, s, pend) == Rp.Stops{Repeat.clip(1n+k)} : Rp.Next}
  %Equal.sym(Bool, Repeat.ids_eq(pend, rs0), False{}, ne) : {Rp.called.pick(_, want, k, Some{Rp.Round{s, rs0}}, s, pend) == Rp.Stops{Repeat.clip(1n+k)} : Rp.Next}
  LARepeat.rp.stop_eq(k)
