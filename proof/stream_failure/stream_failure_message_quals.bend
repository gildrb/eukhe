# eukhe: the proof of LAW stream_failure_message_quals
#
# PROOF: the qualifiers are the parenthesized type, status, or both joined by ", " (LA.sfm.quals1-3: the message's trailing empty parts dropped, String.append re-associated, the cause's text is the table's).

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

def StreamFailure.stream_failure_message_quals(k, x, s):
  (LA.sfm.quals1(k, x), (LA.sfm.quals2(k, s), LA.sfm.quals3(k, x, s)))
