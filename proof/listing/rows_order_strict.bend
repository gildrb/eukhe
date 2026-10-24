# eukhe: the proof of LAW rows_order_strict

import Base
import ../../bend/staging.bend as Sg
import ../../bend/listing.bend as Ls
import ../../laws/listing.bend as Listing
import ./base/order.bend as LO
import ./base/rows.bend as LR

# PROOF of LAW rows_order_strict: the spec's order is lo.Fr
# (lo.before_spec), which never holds both ways (lo.Fr_asym).

def Listing.rows_order_strict(a, b):
  %Equal.sym(Bool, Listing.sp_before(a, b), LO.lo.Fr(a, b), LO.lo.before_spec(a, b)) : {Bool.and(_, Listing.sp_before(b, a)) == False{} : Bool}
  %Equal.sym(Bool, Listing.sp_before(b, a), LO.lo.Fr(b, a), LO.lo.before_spec(b, a)) : {Bool.and(LO.lo.Fr(a, b), _) == False{} : Bool}
  LO.lo.Fr_asym(a, b)
