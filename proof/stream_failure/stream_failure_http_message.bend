# eukhe: the proof of LAW stream_failure_http_message
#
# PROOF: the code's message of a cause is none for unknown and the R2 message otherwise, cause by cause (LA.sfh.msg), at the HTTP cause's own kind and type.

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

def StreamFailure.stream_failure_http_message(m, st, bt, d, code, sdk, r):
  LA.sfh.msg(Sf.http.kind(Sf.classify(Sf.or_else(Sf.or_else(bt, Sf.or_else(code, sdk)), Some{m}), st), Bool.and(Sf.needs_type(Sf.classify(Sf.or_else(Sf.or_else(bt, Sf.or_else(code, sdk)), Some{m}), st)), Sf.is_none(Sf.or_else(bt, Sf.or_else(code, sdk)))), st), Sf.or_else(bt, Sf.or_else(code, sdk)), st, d, r)
