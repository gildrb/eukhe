# eukhe: the proof of LAW headless_settle_entry_reads
#
# PROOF: the reader reads the spelled request back with nothing left
# (hs.req_rt), and the end check passes on the empty rest.

import Base
import ../../bend/headless_settle.bend as Hs
import ../../bend/wire.bend as Wr
import ../../spec/durable/headless_wire.bend as SpW
import ../../laws/headless_settle.bend as HeadlessSettle
import ./base.bend as LAHeadlessSettle

def HeadlessSettle.headless_settle_entry_reads(f, fit):
  %Equal.sym(Wr.Dec<Hs.Facts>, SpW.r_settle(SpW.w_settle_req(f, "")), Wr.Got{f, ""}, LAHeadlessSettle.hs.req_rt(f, "", fit)) : {SpW.r_settle_whole(_) == Some{f} : Maybe<&2, Hs.Facts>}
  {==}
