# eukhe: the proof of LAW submission_ffi_answers

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
import ./submission_step_exact.bend as PSubmissionStepExact

# PROOF of LAW submission_ffi_answers: the submission and the change read back with nothing left (sb_reads: sb_dec_sub, sb_dec_change over wire_nat_round_trip), the model's outcome is the spec's (submission_step_exact) and the reply writer is the spec's speller (sb_put_out).

def Submission.submission_ffi_answers(s, c, sf, cf):
  %Equal.sym(String, FSb.ffi(Submission.spell_req(s, c, "")), FSb.ffi.done(s, c, Wr.end("")), LASubmission.sb_reads(s, c, "", sf, cf)) : {_ == Submission.spell_out(Submission.step_spec(s, c)) : String}
  %Submission.submission_step_exact(s, c) : {FSb.put_out(Sb.step(s, c)) == Submission.spell_out(_) : String}
  LASubmission.sb_put_out(Sb.step(s, c))
