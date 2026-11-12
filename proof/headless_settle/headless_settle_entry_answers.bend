# eukhe: the proof of LAW headless_settle_entry_answers
#
# PROOF: the entry's decoder is the laws' reader (hs.req), which reads
# the spelled request back whole with nothing left (hs.req_rt), so the
# entry answers the core's decision, spelled as the spec spells it
# (hs.put).

import Base
import ../../bend/headless_settle.bend as Hs
import ../../bend/ffi_headless_settle.bend as FHs
import ../../bend/wire.bend as Wr
import ../../spec/durable/headless_wire.bend as SpW
import ../../laws/headless_settle.bend as HeadlessSettle
import ./base.bend as LAHeadlessSettle

# the entry spells a decision as the spec does
def hs.put(x: Hs.Settle, -rest: String) -> {FHs.put_settle(x, rest) == SpW.w_settle(x, rest) : String}:
  match x:
    case Hs.Finished{}:
      {==}
    case Hs.Waiting{}:
      {==}
    case Hs.GiveUp{}:
      {==}

def HeadlessSettle.headless_settle_entry_answers(f, fit):
  +s = SpW.w_settle_req(f, "")
  %Equal.sym(Wr.Dec<Hs.Facts>, FHs.get_facts(s), SpW.r_settle(s), LAHeadlessSettle.hs.req(s)) : {FHs.ffi.got(_) == SpW.w_settle(Hs.settle(f), "") : String}
  %Equal.sym(Wr.Dec<Hs.Facts>, SpW.r_settle(s), Wr.Got{f, ""}, LAHeadlessSettle.hs.req_rt(f, "", fit)) : {FHs.ffi.got(_) == SpW.w_settle(Hs.settle(f), "") : String}
  hs.put(Hs.settle(f), "")
