# eukhe: the proof of LAW doc_plan_loaded_publishes_its_write

import Base
import ../../bend/doc_plan.bend as Dp
import ../../bend/ffi_doc_plan.bend as FDp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip
import ../wire/wire_bool_not_err.bend as PWireBoolNotErr
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../base/wire.bend as LWire
import ../../laws/doc_plan.bend as DocPlan
import ./base.bend as LADocPlan

# PROOF of LAW doc_plan_loaded_publishes_its_write: by the two comparisons of the versions (dp.not_lt_up, dp.lt_up) the content is nothing, so not published, or a base, so published.

def dpl.quiet(+version: Nat, +d: Nat) -> {Dp.publishes(False{}, Dp.OfLoaded{}, DocPlan.writes(Dp.content(Nat.add(version, d), version, False{}))) == False{} : Bool}:
  %LADocPlan.dp.not_lt_up(version, d) : {Dp.publishes(False{}, Dp.OfLoaded{}, DocPlan.writes(Dp.content.pick(_, False{}))) == False{} : Bool}
  {==}

def dpl.base(+stored: Nat, +e: Nat) -> {Dp.publishes(False{}, Dp.OfLoaded{}, DocPlan.writes(Dp.content(stored, Nat.add(stored, 1n+e), False{}))) == True{} : Bool}:
  %LADocPlan.dp.lt_up(stored, e) : {Dp.publishes(False{}, Dp.OfLoaded{}, DocPlan.writes(Dp.content.pick(_, False{}))) == True{} : Bool}
  {==}

def DocPlan.doc_plan_loaded_publishes_its_write(version, d, stored, e):
  (dpl.quiet(version, d), dpl.base(stored, e))
