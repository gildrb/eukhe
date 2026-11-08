# eukhe: the proof of LAW reload_sees_exactly_the_live_records
# The restored runs of a kept record come first, then the rest's: a line
# is in an append exactly when it is in either side.

import Base
import ../../bend/doc_seen.bend as Ds
import ../../laws/doc_seen.bend as DocSeen

def pv.or_assoc(a: Bool, b: Bool, c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def pv.in_app(+n: Nat, xs: List<&2, Ds.Iv>, +ys: List<&2, Ds.Iv>) -> {DocSeen.seen.In(n, List.append(&2, Ds.Iv, xs, ys)) == Bool.or(DocSeen.seen.In(n, xs), DocSeen.seen.In(n, ys)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(Bool, DocSeen.seen.In(n, List.append(&2, Ds.Iv, rest, ys)), Bool.or(DocSeen.seen.In(n, rest), DocSeen.seen.In(n, ys)), pv.in_app(n, rest, ys)) : {Bool.or(DocSeen.seen.Inside(n, x), _) == Bool.or(Bool.or(DocSeen.seen.Inside(n, x), DocSeen.seen.In(n, rest)), DocSeen.seen.In(n, ys)) : Bool}
      pv.or_assoc(DocSeen.seen.Inside(n, x), DocSeen.seen.In(n, rest), DocSeen.seen.In(n, ys))

# one record of version t: kept (b) or dropped
def pv.held(+n: Nat, +live: Nat, +t: Nat, +s: List<&2, Ds.Iv>, +rest: List<&2, Ds.Rec>, b: Bool, ih: {DocSeen.seen.In(n, Ds.restored(Ds.reload(live, rest))) == DocSeen.seen.HeldLive(n, live, rest) : Bool}) -> {DocSeen.seen.In(n, Ds.restored(Ds.reload.put(Ds.Rec{t, s}, Ds.reload(live, rest), b))) == Bool.or(Bool.and(b, DocSeen.seen.In(n, s)), DocSeen.seen.HeldLive(n, live, rest)) : Bool}:
  match b:
    case True{}:
      %ih : {DocSeen.seen.In(n, List.append(&2, Ds.Iv, s, Ds.restored(Ds.reload(live, rest)))) == Bool.or(DocSeen.seen.In(n, s), _) : Bool}
      pv.in_app(n, s, Ds.restored(Ds.reload(live, rest)))
    case False{}:
      ih

def DocSeen.reload_sees_exactly_the_live_records(n, live, log):
  match log:
    case Nil{}:
      {==}
    case +r <> rest:
      match r:
        case Ds.Rec{+t, +s}:
          pv.held(n, live, t, s, rest, Nat.is_eq(t, live), DocSeen.reload_sees_exactly_the_live_records(n, live, rest))
