# eukhe: the proof of LAW stream_failure_http
#
# PROOF: the type's precedence, the classification (stream_failure_classify's
# lemma), the typeless rule by cases and the message by cases on the cause
# (LA.sfb.http).

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

def StreamFailure.stream_failure_http(m, st, bt, d, code, sdk, r):
  LA.sfb.http(m, st, bt, d, code, sdk, r)
