# eukhe: the proof of LAW infer_guard_ffi_refused_run
#
# PROOF: an open whose reply is the error form is the refused open (grr.go:
# a window read whole answers the empty reply); the refused state answers
# every later input with its error (grr.shut, by induction on the inputs).

import Base
import ../../bend/ffi_infer_guard.bend as FG
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/infer_guard.bend as InferGuard
import ./base.bend as LAGuard

# from the refused state that answered o, every later step answers its error
def grr.shut(ins: List<&2, String>, o: String) -> {InferGuard.feed(ins, (FG.Shut{}, o)) == o <> List.replicate(String, List.length(&2, String, ins), SCon{'E', SCon{' ', "infer_guard: the open was refused"}}) : List<&2, String>}:
  match ins:
    case Nil{}:
      {==}
    case i <> t:
      Equal.cong(List<&2, String>, List<&2, String>, z => o <> z, InferGuard.feed(t, (FG.Shut{}, SCon{'E', SCon{' ', "infer_guard: the open was refused"}})), SCon{'E', SCon{' ', "infer_guard: the open was refused"}} <> List.replicate(String, List.length(&2, String, t), SCon{'E', SCon{' ', "infer_guard: the open was refused"}}), grr.shut(t, SCon{'E', SCon{' ', "infer_guard: the open was refused"}}))

# an open answered with the error form is the refused open
def grr.go(d: Wr.Dec<Nat>, no: {LawsBase.wire_opens_err(Pair.snd(FG.St, String, FG.open.go(d))) == True{} : Bool}) -> {FG.open.go(d) == (FG.Shut{}, SCon{'E', SCon{' ', "infer_guard: malformed window"}}) : FG.St & String}:
  match d:
    case Wr.Got{k, rest}:
      match rest:
        case SNil{}:
          LAGuard.gb.absurd_le({FG.open.go(Wr.Got{k, SNil{}}) == (FG.Shut{}, SCon{'E', SCon{' ', "infer_guard: malformed window"}}) : FG.St & String}, no)
        case SCon{y, z}:
          {==}
    case Wr.Bad{}:
      {==}

def InferGuard.infer_guard_ffi_refused_run(s, ins, no):
  %Equal.sym(FG.St & String, FG.open(s), (FG.Shut{}, SCon{'E', SCon{' ', "infer_guard: malformed window"}}), grr.go(Wr.get_nat(s), no)) : {InferGuard.feed(ins, _) == SCon{'E', SCon{' ', "infer_guard: malformed window"}} <> List.replicate(String, List.length(&2, String, ins), SCon{'E', SCon{' ', "infer_guard: the open was refused"}}) : List<&2, String>}
  grr.shut(ins, SCon{'E', SCon{' ', "infer_guard: malformed window"}})
