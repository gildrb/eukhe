# eukhe: the proof of LAW write_unseen_spec

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit.bend as DocCommit

# the model's membership is the spec's
def wu.mem(+v: Nat, xs: List<&2, Nat>) -> {Cm.mem(v, xs) == DocCommit.sp_nmem(v, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      Equal.cong(Bool, Bool, z => Bool.or(Nat.is_eq(x, v), z), Cm.mem(v, rest), DocCommit.sp_nmem(v, rest), wu.mem(v, rest))

def DocCommit.write_unseen_spec(d, s):
  match d:
    case None{}:
      {==}
    case Some{v}:
      Equal.cong(Bool, Bool, z => Bool.not(z), Cm.mem(v, s), DocCommit.sp_nmem(v, s), wu.mem(v, s))
