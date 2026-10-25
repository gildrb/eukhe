# eukhe: the proof of LAW overflow_message_decides
#
# PROOF: the code's lazy message test is its strict form, whose searches,
# tables and fold are the spec's (LA.ovb.message).

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

def Overflow.overflow_message_decides(msg, provider):
  LA.ovb.message(msg, provider)
