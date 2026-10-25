# eukhe: the proof of LAW submission_ffi_exact

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

# PROOF of LAW submission_ffi_exact: a reply that is not the error form comes from a known submission tag and its ids, then a known change tag and its id, with nothing left; each decoded number is its encoding (wire_nat_exact), so the input is the spelled request (sb_ex, sb_ch, sb_join).

def Submission.submission_ffi_exact(x, ok):
  LASubmission.sb_ex(x, Wr.get_nat(x), {==}, ok)
