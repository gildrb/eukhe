# eukhe: the proof of LAW stream_failure_repeating
#
# PROOF: the detail by cases on the period, the message lemma, the recorded
# period by cases (LA.sfb.repeating).

import Base
import ../../bend/text_pat.bend as Tp
import ../../bend/stream_failure.bend as Sf
import ../../bend/ffi_stream_failure.bend as FSf
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/text_pat.bend as TextPat
import ../../laws/overflow.bend as OverflowLaws
import ../../laws/stream_failure.bend as StreamFailure
import ./base.bend as LA

def StreamFailure.stream_failure_repeating(limit, period, q):
  LA.sfb.repeating(limit, period, q)
