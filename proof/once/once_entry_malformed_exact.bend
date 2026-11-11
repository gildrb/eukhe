# eukhe: the proof of LAW once_entry_malformed_exact
#
# PROOF: the entry reads every input as the laws' reader does
# (LE.oe.read); where that reader finds no whole event, the entry keeps
# the life and answers its error form.

import Base
import ../../bend/once.bend as O
import ../../bend/ffi_once.bend as FO
import ../../bend/wire.bend as Wr
import ../../laws/once.bend as Once
import ./base.bend as LA
import ./base/entry.bend as LE

def oem.no(+l: O.Life, d: Wr.Dec<FO.Ev>, no: {Once.on_read.whole(d) == None{} : Maybe<&2, FO.Ev>}) -> {FO.step.got(d, l) == (FO.Eff{l}, SCon{'E', SCon{' ', "once: malformed event"}}) : FO.St & String}:
  match d:
    case Wr.Got{x, rest}:
      match rest:
        case SNil{}:
          LA.ob.none_some(FO.Ev, {FO.step.end(True{}, x, l) == (FO.Eff{l}, SCon{'E', SCon{' ', "once: malformed event"}}) : FO.St & String}, x, Equal.sym(Maybe<&2, FO.Ev>, Some{x}, None{}, no))
        case SCon{h, t}:
          {==}
    case Wr.Bad{}:
      {==}

def Once.once_entry_malformed_exact(l, i, no):
  %LE.oe.read(Wr.get_nat(i)) : {FO.step.got(_, l) == (FO.Eff{l}, SCon{'E', SCon{' ', "once: malformed event"}}) : FO.St & String}
  oem.no(l, Once.on_read.go(Wr.get_nat(i)), no)
