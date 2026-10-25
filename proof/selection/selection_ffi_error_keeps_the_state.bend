# eukhe: the proof of LAW selection_ffi_error_keeps_the_state
#
# A step that reads an event whole answers the model's reply, which opens
# with a Nat (the selection's tag), never the error form
# (wire_nat_not_err); every other step answers the state it was given.

import Base
import ../../bend/selection.bend as M
import ../../bend/ffi_selection.bend as F
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/selection.bend as Selection
import ../base/logic/logic.bend as LLogicLogic

# the model's reply is no error form
def ke.out_ok(o: M.Out) -> {LawsBase.wire_opens_err(F.put_out(o, "")) == False{} : Bool}:
  match o:
    case M.Out{sel, c, p, e}:
      match sel:
        case None{}:
          Wire.wire_nat_not_err(0n, F.put_copy(c, F.put_pan(p, Wr.put_bool(e, ""))))
        case Some{r}:
          match r:
            case M.Rng{a, b}:
              Wire.wire_nat_not_err(1n, F.put_cell(a, F.put_cell(b, F.put_copy(c, F.put_pan(p, Wr.put_bool(e, ""))))))

def ke.res(+s: M.St, r: M.Res, bad: {LawsBase.wire_opens_err(Pair.snd(F.St, String, F.step.res(r))) == True{} : Bool}) -> {Pair.fst(F.St, String, F.step.res(r)) == F.Live{s} : F.St}:
  match r:
    case M.Res{st, +o}:
      +x = LawsBase.wire_opens_err(F.put_out(o, ""))
      LLogicLogic.wr_absurd({F.Live{st} == F.Live{s} : F.St}, Equal.trans(Bool, False{}, x, True{}, Equal.sym(Bool, x, False{}, ke.out_ok(o)), bad))

def ke.end(r: String, +s: M.St, +e: M.Ev, bad: {LawsBase.wire_opens_err(Pair.snd(F.St, String, F.step.end(Wr.end(r), s, e))) == True{} : Bool}) -> {Pair.fst(F.St, String, F.step.end(Wr.end(r), s, e)) == F.Live{s} : F.St}:
  match r:
    case SNil{}:
      ke.res(s, M.step(s, e), bad)
    case SCon{c, t}:
      {==}

def ke.ev(+s: M.St, d: Wr.Dec<M.Ev>, bad: {LawsBase.wire_opens_err(Pair.snd(F.St, String, F.step.ev(s, d))) == True{} : Bool}) -> {Pair.fst(F.St, String, F.step.ev(s, d)) == F.Live{s} : F.St}:
  match d:
    case Wr.Got{+e, +r}:
      ke.end(r, s, e, bad)
    case Wr.Bad{}:
      {==}

def Selection.selection_ffi_error_keeps_the_state(s, str, bad):
  ke.ev(s, F.get_ev(str), bad)
