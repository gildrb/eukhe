# eukhe: the proof of LAW overflow_decides
#
# PROOF: the usage test and the message test are the spec's (LA.ovb.usage,
# LA.ovb.message: the code's lazy search of each table is the spec's Bool
# search, its tables are the spec's, its fold is text_pat_fold's), and so
# is the error test (LA.ovb.err).

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

def Overflow.overflow_decides(st, msg, provider, window, input, cache_read, output):
  +u = Nat.add(input, cache_read)
  %Equal.sym(Bool, O.usage_overflow(st, window, u, output), Overflow.sp_usage(st, window, u, output), LA.ovb.usage(st, window, u, output)) : {Bool.or(Bool.and(O.is_error(st), O.message_overflow(msg, provider)), _) == Overflow.sp_overflow(st, msg, provider, window, input, cache_read, output) : Bool}
  %Equal.sym(Bool, O.message_overflow(msg, provider), Overflow.sp_message(msg, provider), LA.ovb.message(msg, provider)) : {Bool.or(Bool.and(O.is_error(st), _), Overflow.sp_usage(st, window, u, output)) == Overflow.sp_overflow(st, msg, provider, window, input, cache_read, output) : Bool}
  %Equal.sym(Bool, O.is_error(st), Overflow.sp_is_error(st), LA.ovb.err(st)) : {Bool.or(Bool.and(_, Overflow.sp_message(msg, provider)), Overflow.sp_usage(st, window, u, output)) == Overflow.sp_overflow(st, msg, provider, window, input, cache_read, output) : Bool}
  {==}
