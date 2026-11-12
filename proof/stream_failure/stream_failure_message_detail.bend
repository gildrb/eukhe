# eukhe: the proof of LAW stream_failure_message_detail
#
# PROOF: the message is its parts in order; the detail part is ": " and the detail, and the request id part is empty (LA.sfm.detail).

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

def StreamFailure.stream_failure_message_detail(k, t, st, d):
  LA.sfm.detail(k, t, st, d)
