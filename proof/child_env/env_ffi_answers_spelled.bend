# eukhe: the proof of LAW env_ffi_answers_spelled
#
# PROOF: the spelled request is the entry's own encoding of it, and so is
# the spelled reply (pes.req, pes.vars); on that encoding the entry answers
# the model's environment of the child (env_ffi_is_child).

import Base
import ../../bend/child_env.bend as Env
import ../../bend/ffi_child_env.bend as FEnv
import ../../bend/wire.bend as Wr
import ../../laws/child_env.bend as ChildEnv
import ./env_ffi_is_child.bend as PEnvFfiIsChild
import ./env_ffi_answers_spelled/spell.bend as LS

def pea.go(q: FEnv.Req, fits: {ChildEnv.env_req_fits(q) == True{} : Bool}) -> {FEnv.ffi(ChildEnv.env_spell_req(q, "")) == ChildEnv.env_spell_answer(q) : String}:
  match q:
    case FEnv.Req{+r, +k, +b, +o}:
      %LS.pes.req(FEnv.Req{r, k, b, o}, "") : {FEnv.ffi(_) == ChildEnv.env_spell_vars(Env.child(r, k, b, o), "") : String}
      %LS.pes.vars(Env.child(r, k, b, o), "") : {FEnv.ffi(FEnv.put_req(FEnv.Req{r, k, b, o}, "")) == _ : String}
      ChildEnv.env_ffi_is_child(r, k, b, o, fits)

def ChildEnv.env_ffi_answers_spelled(q, fits):
  pea.go(q, fits)
