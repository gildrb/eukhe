# eukhe: the proof of LAW wait_entry_open_malformed_exact
import Base
import ../../bend/wait.bend as Wt
import ../../bend/ffi_wait_race.bend as FWt
import ../../bend/wire.bend as Wr
import ../../laws/wait.bend as WaitLaws
import ./base.bend as LA

# The entry reads every open as the laws reader does (LA.ww.read_dl);
# where that reader finds no whole deadline, the open is refused.

def wom.no(d: Wr.Dec<Maybe<&2, Nat>>, no: {WaitLaws.ww_read_dl.whole(d) == None{} : Maybe<&2, Maybe<&2, Nat>>}) -> {FWt.open.dl(d) == (FWt.Shut{}, SCon{'E', SCon{' ', "wait: malformed open"}}) : FWt.St & String}:
  match d:
    case Wr.Got{x, rest}:
      match rest:
        case SNil{}:
          LA.ww.none_some(Maybe<&2, Nat>, {FWt.open.end(True{}, x) == (FWt.Shut{}, SCon{'E', SCon{' ', "wait: malformed open"}}) : FWt.St & String}, x, Equal.sym(Maybe<&2, Maybe<&2, Nat>>, Some{x}, None{}, no))
        case SCon{c, t}:
          {==}
    case Wr.Bad{}:
      {==}

def WaitLaws.wait_entry_open_malformed_exact(i, no):
  %LA.ww.read_dl(Wr.get_nat(i)) : {FWt.open.dl(_) == (FWt.Shut{}, SCon{'E', SCon{' ', "wait: malformed open"}}) : FWt.St & String}
  wom.no(WaitLaws.ww_read_dl.go(Wr.get_nat(i)), no)
