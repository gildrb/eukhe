# eukhe: the proof of LAW stream_failure_classify_none
#
# PROOF: the code's cause is the first rule of the table that holds (LA.sfd.classify); none holds, so it is unknown (LA.sfd.none).

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

def StreamFailure.stream_failure_classify_none(t, st, hp):
  %Equal.sym(Sf.Cause, Sf.classify(t, st), LA.sfd.decide(StreamFailure.sf_rules(), StreamFailure.sf_lowered(t), st), LA.sfd.classify(t, st)) : {_ == Sf.KUnknown{} : Sf.Cause}
  LA.sfd.none(StreamFailure.sf_rules(), StreamFailure.sf_lowered(t), st, hp)
