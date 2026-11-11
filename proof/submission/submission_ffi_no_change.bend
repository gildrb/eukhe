# eukhe: the proof of LAW submission_ffi_no_change

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

# PROOF of LAW submission_ffi_no_change: the submission reads back with nothing after it (sb_dec_sub), and the empty input holds no change tag.

def Submission.submission_ffi_no_change(s, sf):
  %Equal.sym(Wr.Dec<Sb.Sub>, FSb.get_sub(Wr.get_nat(Submission.spell_sub(s, ""))), Wr.Got{s, ""}, LASubmission.sb_dec_sub(s, "", sf)) : {FSb.ffi.got(_) == Wr.err("submission: malformed request") : String}
  {==}
