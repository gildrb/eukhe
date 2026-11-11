# eukhe: the proof of LAW stream_failure_http_typed
#
# PROOF: the provider error type is y (LA.sfh.or2 and the premise), so the code classifies y, and a present type never gives way to the status (LA.sfd.and_false).

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

def StreamFailure.stream_failure_http_typed(m, st, bt, d, code, sdk, r, y, hy):
  %Equal.sym(Maybe<&2, String>, Sf.or_else(bt, Sf.or_else(code, sdk)), Some{y}, Equal.trans(Maybe<&2, String>, Sf.or_else(bt, Sf.or_else(code, sdk)), StreamFailure.sp_or(bt, StreamFailure.sp_or(code, sdk)), Some{y}, LA.sfh.or2(bt, code, sdk), hy)) : {StreamFailure.sf_kind(Sf.http.of(Sf.http.kind(Sf.classify(Sf.or_else(_, Some{m}), st), Bool.and(Sf.needs_type(Sf.classify(Sf.or_else(_, Some{m}), st)), Sf.is_none(_)), st), _, st, d, r)) == Sf.classify(Some{y}, st) : Sf.Cause}
  %Equal.sym(Bool, Bool.and(Sf.needs_type(Sf.classify(Some{y}, st)), False{}), False{}, LA.sfd.and_false(Sf.needs_type(Sf.classify(Some{y}, st)))) : {StreamFailure.sf_kind(Sf.http.of(Sf.http.kind(Sf.classify(Some{y}, st), _, st), Some{y}, st, d, r)) == Sf.classify(Some{y}, st) : Sf.Cause}
  {==}
