# eukhe: the proof of LAW reload_keeps_exactly_the_live_version

import Base
import ../../bend/doc_seen.bend as Ds
import ../../laws/doc_seen.bend as DocSeen

def pv.keep_eq(+r: Ds.Rec, rest: List<&2, Ds.Rec>, b: Bool) -> {Ds.reload.put(r, rest, b) == DocSeen.seen.Live.keep(r, rest, b) : List<&2, Ds.Rec>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def DocSeen.reload_keeps_exactly_the_live_version(live, log):
  match log:
    case Nil{}:
      {==}
    case +r <> rest:
      match r:
        case Ds.Rec{+t, +s}:
          %DocSeen.reload_keeps_exactly_the_live_version(live, rest) : {Ds.reload.put(Ds.Rec{t, s}, Ds.reload(live, rest), Nat.is_eq(t, live)) == DocSeen.seen.Live.keep(Ds.Rec{t, s}, _, Nat.is_eq(t, live)) : List<&2, Ds.Rec>}
          pv.keep_eq(Ds.Rec{t, s}, Ds.reload(live, rest), Nat.is_eq(t, live))
