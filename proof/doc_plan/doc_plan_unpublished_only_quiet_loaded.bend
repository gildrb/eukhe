# eukhe: the proof of LAW doc_plan_unpublished_only_quiet_loaded

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

# PROOF of LAW doc_plan_unpublished_only_quiet_loaded: every other retire, change and write publishes, so the premise is absurd there.

def DocPlan.doc_plan_unpublished_only_quiet_loaded(retire, c, w, no):
  match retire:
    case True{}:
      LADocPlan.dp.absurd_t({True{} == False{} : Bool} & {c == Dp.OfLoaded{} : Dp.Change} & {w == False{} : Bool}, no)
    case False{}:
      match c:
        case Dp.NoChange{}:
          LADocPlan.dp.absurd_t({False{} == False{} : Bool} & {Dp.NoChange{} == Dp.OfLoaded{} : Dp.Change} & {w == False{} : Bool}, no)
        case Dp.Fresh{}:
          LADocPlan.dp.absurd_t({False{} == False{} : Bool} & {Dp.Fresh{} == Dp.OfLoaded{} : Dp.Change} & {w == False{} : Bool}, no)
        case Dp.OfLoaded{}:
          match w:
            case True{}:
              LADocPlan.dp.absurd_t({False{} == False{} : Bool} & {Dp.OfLoaded{} == Dp.OfLoaded{} : Dp.Change} & {True{} == False{} : Bool}, no)
            case False{}:
              ({==}, ({==}, {==}))
