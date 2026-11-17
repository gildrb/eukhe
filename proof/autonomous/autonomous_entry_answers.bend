# eukhe: the proof of LAW autonomous_entry_answers
#
# PROOF: the entry's decoder is the laws' reader (au.req), which reads
# the spelled request back whole with nothing left (au.req_rt), so the
# entry answers the core's step, spelled as the spec spells it (au.put).

import Base
import ../../bend/verify.bend as V
import ../../bend/autonomous.bend as Au
import ../../bend/ffi_autonomous.bend as FAu
import ../../bend/wire.bend as Wr
import ../../spec/autonomous/autonomous.bend as SpA
import ../../laws/autonomous.bend as Autonomous
import ./base.bend as LAAutonomous

def Autonomous.autonomous_entry_answers(f):
  +s = SpA.w_req(f, "")
  %Equal.sym(Wr.Dec<Au.Facts>, FAu.get_facts(s), SpA.r_req(s), LAAutonomous.au.req(s)) : {FAu.ffi.got(_) == SpA.w_step(Au.decide(f), "") : String}
  %Equal.sym(Wr.Dec<Au.Facts>, SpA.r_req(s), Wr.Got{f, ""}, LAAutonomous.au.req_rt(f, "")) : {FAu.ffi.got(_) == SpA.w_step(Au.decide(f), "") : String}
  LAAutonomous.au.put(Au.decide(f), "")
