# eukhe: the proof of LAW stream_failure_classify_first
#
# PROOF: the code's cause is the first rule of the table that holds (LA.sfd.classify: each code test is its rule, LA.sfd.r_*); the table split at x, with none holding before it, decides x's cause (LA.sfd.split).

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

def StreamFailure.stream_failure_classify_first(t, st, pre, x, post, hr, hx, hp):
  %Equal.sym(Sf.Cause, Sf.classify(t, st), LA.sfd.decide(StreamFailure.sf_rules(), StreamFailure.sf_lowered(t), st), LA.sfd.classify(t, st)) : {_ == StreamFailure.sf_cause(x) : Sf.Cause}
  %Equal.sym(List<&2, StreamFailure.SfRule>, StreamFailure.sf_rules(), List.append(&2, StreamFailure.SfRule, pre, x <> post), hr) : {LA.sfd.decide(_, StreamFailure.sf_lowered(t), st) == StreamFailure.sf_cause(x) : Sf.Cause}
  LA.sfd.split(pre, x, post, StreamFailure.sf_lowered(t), st, hp, hx)
