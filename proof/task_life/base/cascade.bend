# eukhe: lemmas of area task_life about a cascade's rows, shared by its
# laws: a reached live foreground task below an owner with intent takes
# the owner's reason, merged into its own mark

import Base
import ../../../bend/task_life.bend as Tl
import ../../../spec/durable/task_life.bend as Sp
import ../base.bend as LB

def tlc.hit(+by: Tl.Mark, rs: List<&2, Tl.Row>, i: Nat, k: Tl.Mark, row: {List.get(&2, Tl.Row, rs, i) == Some{Tl.Row{True{}, False{}, k}} : Maybe<&2, Tl.Row>}) -> {List.get(&2, Tl.Mark, Tl.cascade.rows(True{}, by, rs), i) == Some{Tl.merge(k, by)} : Maybe<&2, Tl.Mark>}:
  match rs:
    case Nil{}:
      LB.tlb.none_some(Tl.Row, Tl.Row{True{}, False{}, k}, {List.get(&2, Tl.Mark, Tl.cascade.rows(True{}, by, Nil{}), i) == Some{Tl.merge(k, by)} : Maybe<&2, Tl.Mark>}, row)
    case +r <> t:
      match i:
        case 0n:
          %Equal.sym(Tl.Row, r, Tl.Row{True{}, False{}, k}, LB.tlb.some_inj(Tl.Row, r, Tl.Row{True{}, False{}, k}, row)) : {Some{Tl.cascade.row(True{}, by, _)} == Some{Tl.merge(k, by)} : Maybe<&2, Tl.Mark>}
          {==}
        case 1n+p:
          tlc.hit(by, t, p, k, row)
