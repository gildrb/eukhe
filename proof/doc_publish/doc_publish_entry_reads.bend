# eukhe: the proof of LAW doc_publish_entry_reads
#
# PROOF: the count reads back by wire_nat_round_trip (it fits by the
# premise); the one-digit tag of each re-read reads back, and the rest is
# never looked at.

import Base
import ../../bend/doc_publish.bend as Dp
import ../../bend/ffi_doc_publish.bend as FDp
import ../../bend/wire.bend as Wr
import ../../laws/wire.bend as Wire
import ../../laws/doc_publish.bend as DocPublish
import ../base/wire.bend as LBaseWire

def DocPublish.doc_publish_entry_reads(n, s, rest, h):
  match s:
    case Dp.Same{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, Wr.put_nat(0n, rest))), Wr.Got{n, Wr.put_nat(0n, rest)}, Wire.wire_nat_round_trip(n, Wr.put_nat(0n, rest), h)) : {FDp.get_req.rebases(_) == Wr.Got{FDp.Req{n, Dp.Same{}}, rest} : Wr.Dec<FDp.Req>}
      {==}
    case Dp.Gone{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, Wr.put_nat(1n, rest))), Wr.Got{n, Wr.put_nat(1n, rest)}, Wire.wire_nat_round_trip(n, Wr.put_nat(1n, rest), h)) : {FDp.get_req.rebases(_) == Wr.Got{FDp.Req{n, Dp.Gone{}}, rest} : Wr.Dec<FDp.Req>}
      {==}
    case Dp.Moved{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, Wr.put_nat(2n, rest))), Wr.Got{n, Wr.put_nat(2n, rest)}, Wire.wire_nat_round_trip(n, Wr.put_nat(2n, rest), h)) : {FDp.get_req.rebases(_) == Wr.Got{FDp.Req{n, Dp.Moved{}}, rest} : Wr.Dec<FDp.Req>}
      {==}
