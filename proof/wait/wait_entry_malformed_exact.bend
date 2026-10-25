# eukhe: the proof of LAW wait_entry_malformed_exact
import Base
import ../../bend/wait.bend as Wt
import ../../bend/ffi_wait_race.bend as FWt
import ../../bend/wire.bend as Wr
import ../../laws/wait.bend as WaitLaws
import ./base.bend as LA

# The entry reads every input as the laws reader does (LA.ww.read);
# where that reader finds no whole poll, the entry keeps the wait and
# answers its error form.

def wm.no(+w: Wt.W, d: Wr.Dec<Wt.Polled>, no: {WaitLaws.ww_read.whole(d) == None{} : Maybe<&2, Wt.Polled>}) -> {FWt.step.poll(w, d) == (FWt.Live{w}, SCon{'E', SCon{' ', "wait: malformed poll"}}) : FWt.St & String}:
  match d:
    case Wr.Got{x, rest}:
      match rest:
        case SNil{}:
          LA.ww.none_some(Wt.Polled, {FWt.step.end(True{}, w, x) == (FWt.Live{w}, SCon{'E', SCon{' ', "wait: malformed poll"}}) : FWt.St & String}, x, Equal.sym(Maybe<&2, Wt.Polled>, Some{x}, None{}, no))
        case SCon{c, t}:
          {==}
    case Wr.Bad{}:
      {==}

def WaitLaws.wait_entry_malformed_exact(w, i, no):
  %LA.ww.read(Wr.get_bool(i)) : {FWt.step.poll(w, _) == (FWt.Live{w}, SCon{'E', SCon{' ', "wait: malformed poll"}}) : FWt.St & String}
  wm.no(w, WaitLaws.ww_read.go(Wr.get_bool(i)), no)
