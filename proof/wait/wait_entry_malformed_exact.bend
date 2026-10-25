# eukhe: the proof of LAW wait_entry_malformed_exact
# The entry's decoder answers what the laws' reader answers (LA.ww.read);
# where that reader finds no whole poll, the entry answers its error form.

import Base
import ../../bend/wait.bend as Wt
import ../../bend/ffi_wait.bend as FWt
import ../../bend/wire.bend as Wr
import ../../laws/wait.bend as WaitLaws
import ./base.bend as LA

def wm.no(d: Wr.Dec<Wt.Polled>, no: {WaitLaws.ww_read.whole(d) == None{} : Maybe<&2, Wt.Polled>}) -> {FWt.run(d) == SCon{'E', SCon{' ', "wait: malformed poll"}} : String}:
  match d:
    case Wr.Got{x, rest}:
      match rest:
        case SNil{}:
          LA.ww.none_some({FWt.run.end(True{}, x) == SCon{'E', SCon{' ', "wait: malformed poll"}} : String}, x, Equal.sym(Maybe<&2, Wt.Polled>, Some{x}, None{}, no))
        case SCon{c, t}:
          {==}
    case Wr.Bad{}:
      {==}

def WaitLaws.wait_entry_malformed_exact(i, no):
  %LA.ww.read(Wr.get_bool(i)) : {FWt.run(_) == SCon{'E', SCon{' ', "wait: malformed poll"}} : String}
  wm.no(WaitLaws.ww_read.go(Wr.get_bool(i)), no)
