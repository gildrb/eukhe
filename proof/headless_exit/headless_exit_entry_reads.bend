# eukhe: the proof of LAW headless_exit_entry_reads
#
# PROOF: the reader reads the spelled request back with nothing left
# (hx.req_rt), and the end check passes on the empty rest.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../bend/wire.bend as Wr
import ../../spec/durable/headless_wire.bend as SpW
import ../../laws/headless_exit.bend as HeadlessExit
import ./base.bend as LAHeadlessExit

def HeadlessExit.headless_exit_entry_reads(f):
  %Equal.sym(Wr.Dec<Hx.Facts>, SpW.r_exit(SpW.w_exit_req(f, "")), Wr.Got{f, ""}, LAHeadlessExit.hx.req_rt(f, "")) : {SpW.r_exit_whole(_) == Some{f} : Maybe<&2, Hx.Facts>}
  {==}
