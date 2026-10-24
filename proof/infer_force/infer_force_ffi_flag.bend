# eukhe: the proof of LAW infer_force_ffi_flag
# The attempt reads back (LWire.pw6.nat); the two Bools are a closed
# char each; the entry answers the model's flag.

import Base
import ../../bend/infer_force.bend as M
import ../../bend/ffi_infer_force.bend as FF
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/infer_force.bend as InferForce
import ../base/wire.bend as LWire

def iff.flag(-i: Nat, sup: Bool, free: Bool) -> {FF.run(FF.get_flag(Wr.Got{i, Wr.put_bool(sup, Wr.put_bool(free, ""))})) == Wr.put_bool(M.flag(i, sup, free), "") : String}:
  match sup:
    case True{}:
      match free:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match free:
        case True{}:
          {==}
        case False{}:
          {==}

def InferForce.infer_force_ffi_flag(i, sup, free, fits):
  %LWire.pw6.nat(i, Wr.put_bool(sup, Wr.put_bool(free, "")), fits) : {FF.run(FF.get_flag(_)) == Wr.put_bool(M.flag(i, sup, free), "") : String}
  iff.flag(i, sup, free)
