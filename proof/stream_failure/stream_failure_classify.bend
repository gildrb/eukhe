# eukhe: the proof of LAW stream_failure_classify
#
# PROOF: the code's list of tests is the spec's chain of choices, test by test
# (LA.sfb.classify: the searches by text_pat_hit, the lowering by
# text_pat_lower).

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

def StreamFailure.stream_failure_classify(t, st):
  LA.sfb.classify(t, st)
