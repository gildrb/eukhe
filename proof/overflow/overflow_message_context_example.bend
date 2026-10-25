# eukhe: the proof of LAW overflow_message_context_example
#
# PROOF: closed: both sides compute.

import Base
import ../../bend/text_pat.bend as Tp
import ../../bend/overflow.bend as O
import ../../bend/ffi_overflow.bend as FO
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/text_pat.bend as TextPat
import ../../laws/overflow.bend as Overflow

def Overflow.overflow_message_context_example():
  {==}
