# eukhe: the proof of LAW loop_ffi_spelled_left_over
#
# PROOF: the decoder reads the spelled request and leaves the rest
# (le.spelled); a rest that is not empty is refused.

import Base
import ../../bend/ffi_loop.bend as FLp
import ../../bend/wire.bend as Wr
import ../../laws/loop/entry.bend as LoopEntry
import ./base/entry.bend as LALoopEntry

def llo_whole(-r: FLp.Req, +rest: String, more: {String.is_empty(rest) == False{} : Bool}) -> {FLp.ffi.whole(r, Wr.end(rest)) == Wr.err("loop: input left over") : String}:
  %Equal.sym(Bool, String.is_empty(rest), False{}, more) : {FLp.ffi.whole(r, _) == Wr.err("loop: input left over") : String}
  {==}

def LoopEntry.loop_ffi_spelled_left_over(r, rest, h, more):
  Equal.trans(String, FLp.ffi(LoopEntry.lp_spell_req(r, rest)), FLp.ffi.whole(r, Wr.end(rest)), Wr.err("loop: input left over"),
    LALoopEntry.le.spelled(r, rest, h), llo_whole(r, rest, more))
