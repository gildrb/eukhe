# eukhe: the proof of LAW stream_failure_http_typeless_kept
#
# PROOF: with no type the message is classified; the code's test for a cause only a type may give is sf_auth_like (LA.sfh.needs), which the premise fixes, so the code keeps the message's cause.

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

def StreamFailure.stream_failure_http_typeless_kept(m, st, d, r, hk):
  %Equal.sym(Bool, Bool.and(Sf.needs_type(Sf.classify(Some{m}, st)), True{}), StreamFailure.sf_auth_like(Sf.classify(Some{m}, st)), LA.sfh.needs(Sf.classify(Some{m}, st))) : {StreamFailure.sf_kind(Sf.http.of(Sf.http.kind(Sf.classify(Some{m}, st), _, st), None{}, st, d, r)) == Sf.classify(Some{m}, st) : Sf.Cause}
  %Equal.sym(Bool, StreamFailure.sf_auth_like(Sf.classify(Some{m}, st)), False{}, hk) : {StreamFailure.sf_kind(Sf.http.of(Sf.http.kind(Sf.classify(Some{m}, st), _, st), None{}, st, d, r)) == Sf.classify(Some{m}, st) : Sf.Cause}
  {==}
