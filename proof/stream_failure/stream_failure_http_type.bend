# eukhe: the proof of LAW stream_failure_http_type
#
# PROOF: the HTTP cause carries the body type, else the code, else the class name (LA.sfh.or2).

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

def StreamFailure.stream_failure_http_type(m, st, bt, d, code, sdk, r):
  LA.sfh.or2(bt, code, sdk)
