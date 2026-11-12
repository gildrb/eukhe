# eukhe: the proof of LAW stream_failure_repeating_line
#
# PROOF: by cases on the period: 0 and 1 take the one-line detail after ": " (LA.sfm.detail) and record 1; 2 or more contradicts the premise.

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

def StreamFailure.stream_failure_repeating_line(limit, period, q, h):
  match period:
    case 0n:
      %Equal.sym(String, Sf.message(Sf.KRepeating{}, None{}, None{}, Some{String.concat(["the same line ", Nat.show(limit), " times in a row: ", q])}, None{}), String.append(Sf.message(Sf.KRepeating{}, None{}, None{}, None{}, None{}), String.append(": ", String.concat(["the same line ", Nat.show(limit), " times in a row: ", q]))), LA.sfm.detail(Sf.KRepeating{}, None{}, None{}, String.concat(["the same line ", Nat.show(limit), " times in a row: ", q]))) : {Sf.Repeat{_, 1n} == Sf.Repeat{String.concat(["Provider stream repeating: the same line ", Nat.show(limit), " times in a row: ", q]), 1n} : Sf.Repeat}
      {==}
    case 1n:
      %Equal.sym(String, Sf.message(Sf.KRepeating{}, None{}, None{}, Some{String.concat(["the same line ", Nat.show(limit), " times in a row: ", q])}, None{}), String.append(Sf.message(Sf.KRepeating{}, None{}, None{}, None{}, None{}), String.append(": ", String.concat(["the same line ", Nat.show(limit), " times in a row: ", q]))), LA.sfm.detail(Sf.KRepeating{}, None{}, None{}, String.concat(["the same line ", Nat.show(limit), " times in a row: ", q]))) : {Sf.Repeat{_, 1n} == Sf.Repeat{String.concat(["Provider stream repeating: the same line ", Nat.show(limit), " times in a row: ", q]), 1n} : Sf.Repeat}
      {==}
    case 2n+p:
      LLogicLogic.absurd({Sf.repeating(limit, 2n+p, q) == Sf.Repeat{String.concat(["Provider stream repeating: the same line ", Nat.show(limit), " times in a row: ", q]), 1n} : Sf.Repeat}, h)
