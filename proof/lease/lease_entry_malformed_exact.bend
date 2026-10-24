# eukhe: the proof of LAW lease_entry_malformed_exact
# The entry's decoder answers what the laws' reader answers (LA.le.read);
# where that reader finds no whole event, the entry keeps the lease and
# answers its error form.

import Base
import ../../bend/lease.bend as Ls
import ../../bend/ffi_lease.bend as FLs
import ../../bend/wire.bend as Wr
import ../../laws/lease.bend as Lease
import ./base.bend as LA

def lme.no(+s: Ls.L, d: Wr.Dec<Ls.Ev>, no: {Lease.lw_read.whole(d) == None{} : Maybe<&2, Ls.Ev>}) -> {FLs.step.ev(s, d) == (FLs.Live{s}, SCon{'E', SCon{' ', "lease: malformed event"}}) : FLs.St & String}:
  match d:
    case Wr.Got{x, rest}:
      match rest:
        case SNil{}:
          LA.le.none_some({FLs.step.end(True{}, s, x) == (FLs.Live{s}, SCon{'E', SCon{' ', "lease: malformed event"}}) : FLs.St & String}, x, Equal.sym(Maybe<&2, Ls.Ev>, Some{x}, None{}, no))
        case SCon{c, t}:
          {==}
    case Wr.Bad{}:
      {==}

def Lease.lease_entry_malformed_exact(s, i, no):
  %LA.le.read(Wr.get_nat(i)) : {FLs.step.ev(s, _) == (FLs.Live{s}, SCon{'E', SCon{' ', "lease: malformed event"}}) : FLs.St & String}
  lme.no(s, Lease.lw_read.go(Wr.get_nat(i)), no)
