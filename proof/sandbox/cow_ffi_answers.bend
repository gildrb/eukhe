# eukhe: the proof of LAW cow_ffi_answers
# The entry answers as the laws spell; the reader reads back the request
# Rust writes.

import Base
import ../../bend/ffi_sandbox.bend as FSb
import ../../laws/sandbox.bend as Sandbox
import ./base/cow.bend as LACow

def Sandbox.cow_ffi_answers(p, b, c, fits):
  %Equal.sym(String, FSb.ffi(Sandbox.cow_spell_req(p, b, c, "")), Sandbox.cow_spec(Sandbox.cow_spell_req(p, b, c, "")), LACow.cw.exact(Sandbox.cow_spell_req(p, b, c, ""))) : {_ == Sandbox.cow_spell_plan(Sandbox.cow_plan_spec(p, b, c)) : String}
  LACow.cw.answers(p, b, c, fits)
