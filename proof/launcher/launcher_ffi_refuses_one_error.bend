# eukhe: the proof of LAW launcher_ffi_refuses_one_error
#
# The entry answers a request with a Bool or a Nat first (never 'E':
# wire_bool_not_err, wire_nat_not_err), and anything else with the one
# error form; so an answer that opens with 'E' is that error form.

import Base
import ../../bend/wire.bend as Wr
import ../../bend/launcher.bend as La
import ../../bend/ffi_launcher.bend as FLa
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/launcher.bend as Launcher
import ../wire/wire_bool_not_err.bend as PWireBoolNotErr
import ./base.bend as LLa

def lfr.adoption(x: La.Adoption) -> {LawsBase.wire_opens_err(FLa.put_adoption(x, "")) == False{} : Bool}:
  match x:
    case La.Adopt{}:
      {==}
    case La.Replace{}:
      {==}

# no answer to a request opens with 'E'
def lfr.answer(a: La.Ask) -> {LawsBase.wire_opens_err(FLa.answer(a)) == False{} : Bool}:
  match a:
    case La.AskPrompt{c}:
      Wire.wire_bool_not_err(La.admits(c), "")
    case La.AskQuiesce{+b, c}:
      Wire.wire_bool_not_err(La.Wk.closed(La.quiesce(La.Wk{b, c})), Wr.put_bool(La.quiesce.answer(b), ""))
    case La.AskCommit{xs}:
      Wire.wire_bool_not_err(La.commits(xs), "")
    case La.AskAdopt{w}:
      lfr.adoption(La.adoption(0n, w))

def lfr.run(r: Wr.Dec<La.Ask>, bad: {LawsBase.wire_opens_err(FLa.run(r)) == True{} : Bool}) -> {FLa.run(r) == Wr.err("launcher: malformed request") : String}:
  match r:
    case Wr.Got{+a, rest}:
      match rest:
        case SNil{}:
          LLa.la.absurd({FLa.answer(a) == Wr.err("launcher: malformed request") : String}, Equal.trans(Bool, False{}, LawsBase.wire_opens_err(FLa.answer(a)), True{}, Equal.sym(Bool, LawsBase.wire_opens_err(FLa.answer(a)), False{}, lfr.answer(a)), bad))
        case SCon{c, t}:
          {==}
    case Wr.Bad{}:
      {==}

def Launcher.launcher_ffi_refuses_one_error(s, bad):
  lfr.run(FLa.get_ask(s), bad)
