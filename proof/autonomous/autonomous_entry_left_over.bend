# eukhe: the proof of LAW autonomous_entry_left_over
#
# PROOF: the entry's decoder is the laws' reader (au.req), which reads the
# spelled request back with the rest untouched (au.req_rt); the rest is
# not empty, so the entry answers the error form.

import Base
import ../../bend/verify.bend as V
import ../../bend/autonomous.bend as Au
import ../../bend/ffi_autonomous.bend as FAu
import ../../bend/wire.bend as Wr
import ../../spec/autonomous/autonomous.bend as SpA
import ../../laws/autonomous.bend as Autonomous
import ./base.bend as LAAutonomous

def Autonomous.autonomous_entry_left_over(f, ch, t):
  +s = SpA.w_req(f, SCon{ch, t})
  %Equal.sym(Wr.Dec<Au.Facts>, FAu.get_facts(s), SpA.r_req(s), LAAutonomous.au.req(s)) : {FAu.ffi.got(_) == Wr.err("autonomous: malformed request") : String}
  %Equal.sym(Wr.Dec<Au.Facts>, SpA.r_req(s), Wr.Got{f, SCon{ch, t}}, LAAutonomous.au.req_rt(f, SCon{ch, t})) : {FAu.ffi.got(_) == Wr.err("autonomous: malformed request") : String}
  {==}
