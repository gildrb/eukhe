# eukhe: the proof of LAW tags_entry_reads
#
# PROOF: the count reads back (wire_nat_round_trip, it fits), then each
# scan in turn (ptg.go_rt); rest is never read.

import Base
import ../../bend/doc_tags.bend as Dt
import ../../bend/ffi_doc_tags.bend as FDt
import ../../bend/wire.bend as Wr
import ../../laws/doc_tags.bend as DocTags
import ../../laws/base.bend as LawsBase
import ./base.bend as LADocTags
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire

def DocTags.tags_entry_reads(ss, rest, h):
  match ss:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, h)) : {Wr.get_list.start(~Dt.Scan, ~FDt.get_scan, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, Dt.Scan>>}
      {==}
    case Con{+x, +t}:
      +r = rest
      +items = LADocTags.ptg.items(x <> t, r)
      %Equal.sym(String, DocTags.sp_w_req(x <> t, r), Wr.put_nat(List.length(&2, Dt.Scan, x <> t), items), LADocTags.ptg.put(x <> t, r)) : {FDt.get_req(_) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Dt.Scan>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Dt.Scan, x <> t), items)), Wr.Got{List.length(&2, Dt.Scan, x <> t), items}, Wire.wire_nat_round_trip(List.length(&2, Dt.Scan, x <> t), items, h)) : {Wr.get_list.start(~Dt.Scan, ~FDt.get_scan, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Dt.Scan>>}
      LADocTags.ptg.go_rt(t, x, r)
