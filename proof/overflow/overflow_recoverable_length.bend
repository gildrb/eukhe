# eukhe: the proof of LAW overflow_recoverable_length
#
# PROOF: by cases on the limit: a limit of 0 is never above an output, and a limit above 0 leaves the output test alone.

import Base
import ../../bend/text_pat.bend as Tp
import ../../bend/overflow.bend as O
import ../../bend/ffi_overflow.bend as FO
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/text_pat.bend as TextPat
import ../../laws/overflow.bend as Overflow
import ./base.bend as LA

def Overflow.overflow_recoverable_length(desired, output):
  match desired:
    case 0n:
      match output:
        case 0n:
          {==}
        case 1n+o:
          {==}
    case 1n+d:
      {==}
