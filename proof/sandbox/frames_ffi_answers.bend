# eukhe: the proof of LAW frames_ffi_answers
# The entry answers as the laws spell; the reader reads back the request
# Rust writes.

import Base
import ../../bend/ffi_frames.bend as FFr
import ../../bend/wire.bend as Wr
import ../../laws/sandbox.bend as Sandbox
import ./base/frames.bend as LAFr

def Sandbox.frames_ffi_answers(q, fits):
  %Equal.sym(String, FFr.ffi(Sandbox.fr_spell_req(q, "")), Sandbox.fr_spec(Sandbox.fr_spell_req(q, "")), LAFr.fr.exact(Sandbox.fr_spell_req(q, ""))) : {_ == Sandbox.fr_spell_answer(q) : String}
  %Equal.sym(Wr.Dec<FFr.Req>, Sandbox.fr_read_req(Sandbox.fr_spell_req(q, "")), Wr.Got{q, ""}, LAFr.fr.rt(q, "", fits)) : {Sandbox.fr_spec.run(_) == Sandbox.fr_spell_answer(q) : String}
  {==}
