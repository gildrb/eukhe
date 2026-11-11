# eukhe: the proof of LAW infer_threshold_ffi_refuses
#
# PROOF: a request read whole answers its plan, a Nat first (the
# threshold's tag, Wire.wire_nat_not_err), never 'E'; every other branch of
# the entry is its one error form.

import Base
import ../../bend/infer_threshold.bend as M
import ../../bend/ffi_infer_threshold.bend as FT
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/infer_threshold.bend as InferThreshold
import ../wire/base/spell.bend as LAWireSpell

def itf.E(s: String) -> Type:
  {s == SCon{'E', SCon{' ', "infer_threshold: malformed request"}} : String}

# a Nat spelled first never opens with 'E'
def itf.nat(-G: Type, n: Nat, rest: String, bad: {LawsBase.wire_opens_err(Wr.put_nat(n, rest)) == True{} : Bool}) -> G:
  LAWireSpell.ws_absurd(G, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(Wr.put_nat(n, rest)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(Wr.put_nat(n, rest)), True{}, bad), Wire.wire_nat_not_err(n, rest)))

def itf.over(o: M.Over, rest: String, bad: {LawsBase.wire_opens_err(FT.put_over(o, rest)) == True{} : Bool}) -> itf.E(FT.put_over(o, rest)):
  match o:
    case M.Under{}:
      itf.nat(itf.E(FT.put_over(M.Under{}, rest)), 0n, rest, bad)
    case M.Early{}:
      itf.nat(itf.E(FT.put_over(M.Early{}, rest)), 1n, rest, bad)
    case M.Blocks{}:
      itf.nat(itf.E(FT.put_over(M.Blocks{}, rest)), 2n, rest, bad)

def itf.plan(p: M.Plan, bad: {LawsBase.wire_opens_err(FT.put_plan(p)) == True{} : Bool}) -> itf.E(FT.put_plan(p)):
  match p:
    case M.Plan{o, c}:
      itf.over(o, FT.put_cut(c), bad)

def itf.answer(q: FT.Req, bad: {LawsBase.wire_opens_err(FT.answer(q)) == True{} : Bool}) -> itf.E(FT.answer(q)):
  match q:
    case FT.Req{on, t, last, w, r, m, keep, full, xs, cuts}:
      itf.plan(M.plan(on, t, last, w, r, m, keep, full, xs, cuts), bad)

def itf.run(x: Wr.Dec<FT.Req>, bad: {LawsBase.wire_opens_err(FT.run(x)) == True{} : Bool}) -> itf.E(FT.run(x)):
  match x:
    case Wr.Got{q, rest}:
      match rest:
        case SNil{}:
          itf.answer(q, bad)
        case SCon{y, z}:
          {==}
    case Wr.Bad{}:
      {==}

def InferThreshold.infer_threshold_ffi_refuses(s, bad):
  itf.run(FT.get_req(s), bad)
