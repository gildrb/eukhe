# eukhe: the proof of LAW doc_plan_ffi_example

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

# PROOF of LAW doc_plan_ffi_example: each anchor computes.

def DocPlan.doc_plan_ffi_example():
  ({==}, ({==}, ({==}, ({==}, {==}))))
