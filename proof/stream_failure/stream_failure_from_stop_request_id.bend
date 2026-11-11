# eukhe: the proof of LAW stream_failure_from_stop_request_id
#
# PROOF: both messages are R2 messages with the request id last (LA.sfm.rid).

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

def StreamFailure.stream_failure_from_stop_request_id(raw, r):
  match raw:
    case None{}:
      LA.sfm.rid(Sf.KUnknown{}, None{}, None{}, Some{"stream ended with an error and no stop reason"}, r)
    case Some{+x}:
      LA.sfm.rid(Sf.classify(Some{x}, None{}), Some{x}, None{}, None{}, r)
