# eukhe: the proof of LAW reload_splits
#
# PROOF: by induction on the first records; a record is kept or dropped by
# its own version only.

import Base
import ../../bend/doc_seen.bend as Ds
import ../../laws/doc_seen.bend as DocSeen

def rs.put_app(+r: Ds.Rec, xs: List<&2, Ds.Rec>, ys: List<&2, Ds.Rec>, b: Bool) -> {Ds.reload.put(r, List.append(&2, Ds.Rec, xs, ys), b) == List.append(&2, Ds.Rec, Ds.reload.put(r, xs, b), ys) : List<&2, Ds.Rec>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def DocSeen.reload_splits(live, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case r <> +rest:
      match r:
        case Ds.Rec{+t, +s}:
          +k = Nat.is_eq(t, live)
          %Equal.sym(List<&2, Ds.Rec>, Ds.reload(live, List.append(&2, Ds.Rec, rest, ys)), List.append(&2, Ds.Rec, Ds.reload(live, rest), Ds.reload(live, ys)), DocSeen.reload_splits(live, rest, ys)) : {Ds.reload.put(Ds.Rec{t, s}, _, k) == List.append(&2, Ds.Rec, Ds.reload.put(Ds.Rec{t, s}, Ds.reload(live, rest), k), Ds.reload(live, ys)) : List<&2, Ds.Rec>}
          rs.put_app(Ds.Rec{t, s}, Ds.reload(live, rest), Ds.reload(live, ys), k)
