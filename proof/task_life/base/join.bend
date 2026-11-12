# eukhe: lemmas of area task_life about the join's marks, shared by its
# laws: a join that marks nothing counts no mark

import Base
import ../../../bend/task_life.bend as Tl
import ../../../spec/durable/task_life.bend as Sp

# keep_all sets no mark
def tlj.count_keep(xs: List<&2, Bool>) -> {Sp.count(Tl.keep_all(xs)) == 0n : Nat}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      tlj.count_keep(t)
