# eukhe: the proof of LAW write_saw_spec

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit.bend as DocCommit

def ws.put(+x: Nat, r: List<&2, Nat>, b: Bool) -> {Cm.drop.put(x, r, b) == DocCommit.sp_ndrop.keep(b, x, r) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the model's drop is the spec's
def ws.drop(+v: Nat, xs: List<&2, Nat>) -> {Cm.drop(v, xs) == DocCommit.sp_ndrop(v, xs) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %ws.drop(v, rest) : {Cm.drop.put(x, Cm.drop(v, rest), Nat.is_eq(x, v)) == DocCommit.sp_ndrop.keep(Nat.is_eq(x, v), x, _) : List<&2, Nat>}
      ws.put(x, Cm.drop(v, rest), Nat.is_eq(x, v))

def DocCommit.write_saw_spec(v, s):
  Equal.cong(List<&2, Nat>, List<&2, Nat>, z => List.take(&2, Nat, v <> z, 8n), Cm.drop(v, s), DocCommit.sp_ndrop(v, s), ws.drop(v, s))
