# eukhe: the proof of LAW once_life_is_spec
#
# PROOF: by the first record. None: absent. Intended: the fold goes on
# from a pending effect (LA.ob.go_pending). Started: from a first launch
# (LA.ob.go_first). An end: every later record is absorbed (LA.ob.go_ran,
# go_lost, go_void), and the spec's first end is that record.

import Base
import ../../bend/once.bend as O
import ../../laws/once.bend as Once
import ./base.bend as LA

def Once.once_life_is_spec(j):
  match j:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case O.Intended{}:
          LA.ob.go_pending(t)
        case O.Started{}:
          LA.ob.go_first(t, True{})
        case O.Finished{}:
          LA.ob.go_ran(t)
        case O.Unknown{}:
          LA.ob.go_lost(t)
        case O.Unstarted{}:
          LA.ob.go_void(t)
