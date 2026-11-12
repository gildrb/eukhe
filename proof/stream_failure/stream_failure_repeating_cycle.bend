# eukhe: the proof of LAW stream_failure_repeating_cycle
#
# PROOF: by cases on the period: 0 and 1 contradict the premise; 2 or more takes the cycle detail after ": " (LA.sfm.detail) and records the period.

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

def StreamFailure.stream_failure_repeating_cycle(limit, period, q, h):
  match period:
    case 0n:
      LLogicLogic.absurd({Sf.repeating(limit, 0n, q) == Sf.Repeat{String.concat(["Provider stream repeating: a cycle of ", Nat.show(0n), " lines repeated over the last ", Nat.show(limit), " lines, ending with ", q]), 0n} : Sf.Repeat}, h)
    case 1n:
      LLogicLogic.absurd({Sf.repeating(limit, 1n, q) == Sf.Repeat{String.concat(["Provider stream repeating: a cycle of ", Nat.show(1n), " lines repeated over the last ", Nat.show(limit), " lines, ending with ", q]), 1n} : Sf.Repeat}, h)
    case 2n+p:
      %Equal.sym(String, Sf.message(Sf.KRepeating{}, None{}, None{}, Some{String.concat(["a cycle of ", Nat.show(2n+p), " lines repeated over the last ", Nat.show(limit), " lines, ending with ", q])}, None{}), String.append(Sf.message(Sf.KRepeating{}, None{}, None{}, None{}, None{}), String.append(": ", String.concat(["a cycle of ", Nat.show(2n+p), " lines repeated over the last ", Nat.show(limit), " lines, ending with ", q]))), LA.sfm.detail(Sf.KRepeating{}, None{}, None{}, String.concat(["a cycle of ", Nat.show(2n+p), " lines repeated over the last ", Nat.show(limit), " lines, ending with ", q]))) : {Sf.Repeat{_, 2n+p} == Sf.Repeat{String.concat(["Provider stream repeating: a cycle of ", Nat.show(2n+p), " lines repeated over the last ", Nat.show(limit), " lines, ending with ", q]), 2n+p} : Sf.Repeat}
      {==}
