# eukhe: the proof of LAW overflow_other_reply
#
# PROOF: a tool-use or abort reply is no error, no stop and no length stop: every test is false (LA.ovb.and_false).

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

def Overflow.overflow_other_reply(msg, provider, window, input, cache_read, output):
  LA.ovb.and_false(Nat.is_lt(0n, window))
