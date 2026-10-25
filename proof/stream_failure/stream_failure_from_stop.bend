# eukhe: the proof of LAW stream_failure_from_stop
#
# PROOF: by cases on the reason: the classification and the message lemmas
# (LA.sfb.from_stop).

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

def StreamFailure.stream_failure_from_stop(raw, r):
  LA.sfb.from_stop(raw, r)
