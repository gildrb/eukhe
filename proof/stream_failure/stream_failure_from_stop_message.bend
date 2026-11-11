# eukhe: the proof of LAW stream_failure_from_stop_message
#
# PROOF: a reason is the type of its message, so the message is the cause's text and " (x)" (LA.sfm.quals1); no reason computes.

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
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

def StreamFailure.stream_failure_from_stop_message(x):
  (LA.sfm.quals1(Sf.classify(Some{x}, None{}), x), {==})
