# eukhe: the proof of LAW infer_force_ffi_after
# The attempt and the retries read back (LWire.pw6.nat); the reply is a
# closed char; the entry writes the model's step as the spec does.

import Base
import ../../bend/infer_force.bend as M
import ../../bend/ffi_infer_force.bend as FF
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/infer_force.bend as InferForce
import ../base/logic/bool.bend as LLogicBool
import ../base/wire.bend as LWire

# the entry writes a step as the spec does
def ifa.next(n: M.Next) -> {FF.put_next(n) == InferForce.spell_next(n) : String}:
  match n:
    case M.Hit{}:
      {==}
    case M.Again{}:
      {==}
    case M.Fails{}:
      {==}

def ifa.called(+i: Nat, +r: Nat, c: Bool) -> {FF.run(FF.get_after.retries(i, Wr.Got{r, Wr.put_bool(c, "")})) == InferForce.spell_next(M.after(i, r, c)) : String}:
  match c:
    case True{}:
      {==}
    case False{}:
      ifa.next(M.after(i, r, False{}))

def ifa.fill(+i: Nat, +r: Nat, +c: Bool, +fits: {Bool.and(LawsBase.wire_fits(i), LawsBase.wire_fits(r)) == True{} : Bool}) -> {FF.ffi(InferForce.spell_after(i, r, c)) == InferForce.spell_next(M.after(i, r, c)) : String}:
  +hi = LLogicBool.wr_and_l(LawsBase.wire_fits(i), LawsBase.wire_fits(r), fits)
  +hr = LLogicBool.wr_and_r(LawsBase.wire_fits(i), LawsBase.wire_fits(r), fits)
  %LWire.pw6.nat(i, Wr.put_nat(r, Wr.put_bool(c, "")), hi) : {FF.run(FF.get_after(_)) == InferForce.spell_next(M.after(i, r, c)) : String}
  %LWire.pw6.nat(r, Wr.put_bool(c, ""), hr) : {FF.run(FF.get_after.retries(i, _)) == InferForce.spell_next(M.after(i, r, c)) : String}
  ifa.called(i, r, c)

def InferForce.infer_force_ffi_after(i, r, c, fits):
  ifa.fill(i, r, c, fits)
