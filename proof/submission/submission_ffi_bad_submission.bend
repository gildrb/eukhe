# eukhe: the proof of LAW submission_ffi_bad_submission

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

# PROOF of LAW submission_ffi_bad_submission: the tag reads back (wire_nat_round_trip through sb_nat) and no submission has it.

def Submission.submission_ffi_bad_submission(k, x, fit):
  %LASubmission.sb_nat(8n+k, x, fit) : {FSb.ffi.got(FSb.get_sub(_)) == Wr.err("submission: malformed request") : String}
  {==}
