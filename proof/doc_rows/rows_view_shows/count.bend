# eukhe: LAW rows_view_shows, the lines a read counts

import Base
import ../../../bend/doc_lines.bend as Dl
import ../../../bend/doc_rows.bend as Dr
import ../../../laws/doc_rows.bend as DocRows
import ../base.bend as DRB

# the last line counts when it is not empty
def rvs.count_last(l: Dl.Line, +n: Nat) -> {Dr.count.last(l, n) == DocRows.rows.If(Nat, DocRows.rows.Empty(l), n, 1n+n) : Nat}:
  match l:
    case Dl.Line{k, en}:
      match k:
        case 0n:
          {==}
        case 1n+j:
          {==}

# the count from line l on: n, the lines after l, and l when the last is not empty
def rvs.count_go(rest: List<&2, Dl.Line>, +l: Dl.Line, +n: Nat) -> {Dr.count.go(rest, l, n) == DocRows.rows.If(Nat, DocRows.rows.LastEmpty(l <> rest), Nat.add(n, List.length(&2, Dl.Line, rest)), 1n+Nat.add(n, List.length(&2, Dl.Line, rest))) : Nat}:
  match rest:
    case Nil{}:
      %Equal.sym(Nat, Nat.add(n, 0n), n, DRB.drb.add_zero(n)) : {Dr.count.go(Nil{}, l, n) == DocRows.rows.If(Nat, DocRows.rows.Empty(l), _, 1n+_) : Nat}
      rvs.count_last(l, n)
    case +m <> +more:
      %Equal.sym(Nat, Nat.add(n, 1n+List.length(&2, Dl.Line, more)), 1n+Nat.add(n, List.length(&2, Dl.Line, more)), DRB.drb.add_succ(n, List.length(&2, Dl.Line, more))) : {Dr.count.go(m <> more, l, n) == DocRows.rows.If(Nat, DocRows.rows.LastEmpty(m <> more), _, 1n+_) : Nat}
      rvs.count_go(more, m, 1n+n)

# two lines or more: the length is at least 2
def rvs.le_two(k: Nat) -> {Nat.is_le(2n, 2n+k) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      {==}

# the addressable lines are the count of the read rule
def rvs.count(ls: List<&2, Dl.Line>) -> {Dr.count(ls) == DocRows.rows.Count(ls) : Nat}:
  match ls:
    case Nil{}:
      {==}
    case l <> rest:
      match rest:
        case Nil{}:
          {==}
        case +m <> +more:
          %Equal.sym(Bool, Nat.is_le(2n, 2n+List.length(&2, Dl.Line, more)), True{}, rvs.le_two(List.length(&2, Dl.Line, more))) : {Dr.count(l <> m <> more) == DocRows.rows.If(Nat, Bool.and(_, DocRows.rows.LastEmpty(m <> more)), Nat.sub(2n+List.length(&2, Dl.Line, more), 1n), 2n+List.length(&2, Dl.Line, more)) : Nat}
          rvs.count_go(more, m, 1n)

# the lines a read counts: every piece when raw, else the count
def rvs.total(raw: Bool, +ls: List<&2, Dl.Line>) -> {Dr.total(raw, ls) == DocRows.rows.If(Nat, raw, List.length(&2, Dl.Line, ls), DocRows.rows.Count(ls)) : Nat}:
  match raw:
    case True{}:
      {==}
    case False{}:
      rvs.count(ls)
