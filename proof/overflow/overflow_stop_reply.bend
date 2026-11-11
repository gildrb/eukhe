# eukhe: the proof of LAW overflow_stop_reply
#
# PROOF: a stop reply is no error, so only its usage test counts, and that is a window and the reads past it (LA.ovb.or_false drops the length arm).

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

def Overflow.overflow_stop_reply(msg, provider, window, input, cache_read, output):
  +u = Nat.add(input, cache_read)
  %Equal.sym(Bool, Bool.or(Nat.is_lt(window, u), False{}), Nat.is_lt(window, u), LA.ovb.or_false(Nat.is_lt(window, u))) : {Bool.and(Nat.is_lt(0n, window), _) == Bool.and(Nat.is_lt(0n, window), Nat.is_lt(window, u)) : Bool}
  {==}
