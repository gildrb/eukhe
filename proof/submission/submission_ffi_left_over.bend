# eukhe: the proof of LAW submission_ffi_left_over

import Base
import ../../bend/submission.bend as Sb
import ../../bend/ffi_submission.bend as FSb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../base/wire.bend as LWire
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ../../laws/submission.bend as Submission
import ./base.bend as LASubmission

# PROOF of LAW submission_ffi_left_over: the request reads back with the rest untouched (sb_reads); the rest is not empty, so the entry answers the left-over error form.

def Submission.submission_ffi_left_over(s, c, h, t, sf, cf):
  %Equal.sym(String, FSb.ffi(Submission.spell_req(s, c, SCon{h, t})), FSb.ffi.done(s, c, Wr.end(SCon{h, t})), LASubmission.sb_reads(s, c, SCon{h, t}, sf, cf)) : {_ == Wr.err("submission: input left after the request") : String}
  {==}
