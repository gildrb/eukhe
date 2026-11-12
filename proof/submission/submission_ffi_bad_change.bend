# eukhe: the proof of LAW submission_ffi_bad_change

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

# PROOF of LAW submission_ffi_bad_change: the submission reads back with the rest untouched (sb_dec_sub), the change tag reads back (sb_nat) and no change has it.

def Submission.submission_ffi_bad_change(s, k, x, sf, fit):
  %Equal.sym(Wr.Dec<Sb.Sub>, FSb.get_sub(Wr.get_nat(Submission.spell_sub(s, Wr.put_nat(3n+k, x)))), Wr.Got{s, Wr.put_nat(3n+k, x)}, LASubmission.sb_dec_sub(s, Wr.put_nat(3n+k, x), sf)) : {FSb.ffi.got(_) == Wr.err("submission: malformed request") : String}
  %LASubmission.sb_nat(3n+k, x, fit) : {FSb.ffi.change(s, FSb.get_change(_)) == Wr.err("submission: malformed request") : String}
  {==}
