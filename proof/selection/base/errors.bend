# eukhe: lemmas of the selection stepper's error forms: an answer of the
# model (step.res) never opens with 'E'

import Base
import ../../../bend/selection.bend as M
import ../../../bend/ffi_selection.bend as F
import ../../../laws/base.bend as LawsBase

def se.res_ok(r: M.Res) -> {LawsBase.wire_opens_err(Pair.snd(F.St, String, F.step.res(r))) == False{} : Bool}:
  match r:
    case M.Res{st, o}:
      match o:
        case M.Out{sel, c, p, e}:
          match sel:
            case None{}:
              {==}
            case Some{rg}:
              match rg:
                case M.Rng{a, b}:
                  {==}
