# eukhe: the proof of LAW frames_ffi_left_over
# The reader reads the request back with the input after it; that input
# is not empty, so the request is not the whole input (Wr.end is String.is_empty).

import Base
import ../../bend/ffi_frames.bend as FFr
import ../../bend/wire.bend as Wr
import ../../laws/sandbox.bend as Sandbox
import ./base/frames.bend as LAFr

def Sandbox.frames_ffi_left_over(q, more, fits, some):
  %Equal.sym(String, FFr.ffi(Sandbox.fr_spell_req(q, more)), Sandbox.fr_spec(Sandbox.fr_spell_req(q, more)), LAFr.fr.exact(Sandbox.fr_spell_req(q, more))) : {_ == Sandbox.fr_malformed() : String}
  %Equal.sym(Wr.Dec<FFr.Req>, Sandbox.fr_read_req(Sandbox.fr_spell_req(q, more)), Wr.Got{q, more}, LAFr.fr.rt(q, more, fits)) : {Sandbox.fr_spec.run(_) == Sandbox.fr_malformed() : String}
  %Equal.sym(Bool, String.is_empty(more), False{}, some) : {Sandbox.fr_spec.end(_, q) == Sandbox.fr_malformed() : String}
  {==}
