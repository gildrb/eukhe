# eukhe: the proof of LAW stream_failure_shown
#
# PROOF: by induction on the line and the allowance together: the code keeps a
# char per char allowed and marks the first char past it (LA.sfb.shown_go).

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

def StreamFailure.stream_failure_shown(s):
  LA.sfb.shown(s)
