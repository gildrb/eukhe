# eukhe: the proof of LAW overflow_error_reply
#
# PROOF: an error reply is no stop and no length stop, so its usage test is false whatever the window (LA.ovb.and_false), and the reply is its message test (LA.ovb.or_false).

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

def Overflow.overflow_error_reply(msg, provider, window, input, cache_read, output):
  %Equal.sym(Bool, Bool.and(Nat.is_lt(0n, window), False{}), False{}, LA.ovb.and_false(Nat.is_lt(0n, window))) : {Bool.or(O.message_overflow(msg, provider), _) == O.message_overflow(msg, provider) : Bool}
  LA.ovb.or_false(O.message_overflow(msg, provider))
