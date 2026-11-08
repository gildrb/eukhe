# eukhe: the proof of LAW dir_ffi_answers_spelled
#
# PROOF: the spelled request is the entry's own encoding of it, and so is
# the spelled reply (pds.req, pds.loop); on that encoding the entry answers
# the loop after the model's tick (dir_ffi_is_tick).

import Base
import ../../bend/director.bend as Dr
import ../../bend/ffi_director.bend as FDr
import ../../bend/wire.bend as Wr
import ../../laws/director.bend as Director
import ./dir_ffi_is_tick.bend as PDirFfiIsTick
import ./dir_ffi_answers_spelled/spell.bend as LS

def pda.go(q: FDr.Req, fits: {Director.dir_req_fits(q) == True{} : Bool}) -> {FDr.ffi(Director.dir_spell_req(q, "")) == Director.dir_spell_answer(q) : String}:
  match q:
    case FDr.Req{+c, +l, +vs}:
      %LS.pds.req(FDr.Req{c, l, vs}, "") : {FDr.ffi(_) == Director.dir_spell_loop(Dr.tick(c, l, vs), "") : String}
      %LS.pds.loop(Dr.tick(c, l, vs), "") : {FDr.ffi(FDr.put_req(FDr.Req{c, l, vs}, "")) == _ : String}
      Director.dir_ffi_is_tick(c, l, vs, fits)

def Director.dir_ffi_answers_spelled(q, fits):
  pda.go(q, fits)
