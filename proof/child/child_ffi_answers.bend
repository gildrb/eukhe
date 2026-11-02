# eukhe: the proof of LAW child_ffi_answers
# The entry answers as the laws spell; the laws' reader reads back the
# request Rust writes.

import Base
import ../../bend/ffi_child.bend as FCh
import ../../laws/child.bend as Child
import ./base/entry.bend as LAE

def Child.child_ffi_answers(q, fits):
  %Equal.sym(String, FCh.ffi(Child.ch_spell_req(q, "")), Child.ch_spec(Child.ch_spell_req(q, "")), LAE.ct.exact(Child.ch_spell_req(q, ""))) : {_ == Child.ch_answer(q) : String}
  LAE.rt.answers(q, fits)
