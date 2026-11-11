# eukhe: the proof of LAW infer_force_ffi_refuses
#
# PROOF: a request read whole answers its flag (a Bool, never 'E',
# Wire.wire_bool_not_err) or its step (a tag 0, 1 or 2); every other path
# of the entry is the one error form.

import Base
import ../../bend/infer_force.bend as M
import ../../bend/ffi_infer_force.bend as FF
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/infer_force.bend as InferForce

def rf.BD(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# a True that is False proves anything
def rf.absurd(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : rf.BD(_, G)
  Unit{}

def rf.next(n: M.Next) -> {LawsBase.wire_opens_err(FF.put_next(n)) == False{} : Bool}:
  match n:
    case M.Hit{}:
      {==}
    case M.Again{}:
      {==}
    case M.Fails{}:
      {==}

# the answer to a request never opens with 'E'
def rf.ans(q: FF.Req) -> {LawsBase.wire_opens_err(FF.answer(q)) == False{} : Bool}:
  match q:
    case FF.QFlag{i, sup, free}:
      Wire.wire_bool_not_err(M.flag(i, sup, free), "")
    case FF.QAfter{i, r, c}:
      rf.next(M.after(i, r, c))

def rf.run(x: Wr.Dec<FF.Req>, bad: {LawsBase.wire_opens_err(FF.run(x)) == True{} : Bool}) -> {FF.run(x) == SCon{'E', SCon{' ', "infer_force: malformed request"}} : String}:
  match x:
    case Wr.Got{q, rest}:
      match rest:
        case SNil{}:
          rf.absurd({FF.answer(q) == SCon{'E', SCon{' ', "infer_force: malformed request"}} : String},
            Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FF.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FF.answer(q)), True{}, bad), rf.ans(q)))
        case SCon{y, z}:
          {==}
    case Wr.Bad{}:
      {==}

def InferForce.infer_force_ffi_refuses(s, bad):
  rf.run(FF.get_req(s), bad)
