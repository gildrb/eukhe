# eukhe: the proof of LAW headless_exit_entry_left_over
#
# PROOF: the entry's decoder is the laws' reader (hx.req), which reads the
# spelled request back with the rest untouched (hx.req_rt); the rest is
# not empty, so the entry answers the error form.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../bend/ffi_headless_exit.bend as FHx
import ../../bend/wire.bend as Wr
import ../../spec/durable/headless_wire.bend as SpW
import ../../laws/headless_exit.bend as HeadlessExit
import ./base.bend as LAHeadlessExit

def HeadlessExit.headless_exit_entry_left_over(f, ch, t):
  +s = SpW.w_exit_req(f, SCon{ch, t})
  %Equal.sym(Wr.Dec<Hx.Facts>, FHx.get_facts(s), SpW.r_exit(s), LAHeadlessExit.hx.req(s)) : {FHx.ffi.got(_) == Wr.err("headless_exit: malformed request") : String}
  %Equal.sym(Wr.Dec<Hx.Facts>, SpW.r_exit(s), Wr.Got{f, SCon{ch, t}}, LAHeadlessExit.hx.req_rt(f, SCon{ch, t})) : {FHx.ffi.got(_) == Wr.err("headless_exit: malformed request") : String}
  {==}
