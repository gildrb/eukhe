# eukhe: the proof of LAW wire_list_reads_items

import Base
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire

# the decoder's cons is the spec's
def wl_cons(-A: Data, -x: A, d: Wr.Dec<List<&2, A>>) ->
  {Wr.get_list.cons(A, x, d) == LawsBase.wire_items.cons(A, x, d) : Wr.Dec<List<&2, A>>}:
  match d:
    case Wr.Got{xs, r}:
      {==}
    case Wr.Bad{}:
      {==}

# the item loop at cur, the answer at the first of m + 1 items, reads the
# spec's m + 1 items
def wl_go(~A: Data, ~get: String -> Wr.Dec<A>, m: Nat, cur: Wr.Dec<A>) ->
  {Wr.get_list.go(~A, ~get, m, cur) == LawsBase.wire_items.then(A, cur, r => LawsBase.wire_items(~A, ~get, m, r)) : Wr.Dec<List<&2, A>>}:
  match m cur:
    case 0n Wr.Got{x, r}:
      {==}
    case 0n Wr.Bad{}:
      {==}
    case 1n++k Wr.Got{+x, +r}:
      Equal.trans(Wr.Dec<List<&2, A>>,
        Wr.get_list.cons(A, x, Wr.get_list.go(~A, ~get, k, get(r))),
        Wr.get_list.cons(A, x, LawsBase.wire_items.then(A, get(r), r2 => LawsBase.wire_items(~A, ~get, k, r2))),
        LawsBase.wire_items.cons(A, x, LawsBase.wire_items.then(A, get(r), r2 => LawsBase.wire_items(~A, ~get, k, r2))),
        Equal.cong(Wr.Dec<List<&2, A>>, Wr.Dec<List<&2, A>>, d => Wr.get_list.cons(A, x, d),
          Wr.get_list.go(~A, ~get, k, get(r)), LawsBase.wire_items.then(A, get(r), r2 => LawsBase.wire_items(~A, ~get, k, r2)),
          wl_go(~A, ~get, k, get(r))),
        wl_cons(A, x, LawsBase.wire_items.then(A, get(r), r2 => LawsBase.wire_items(~A, ~get, k, r2))))
    case 1n+k Wr.Bad{}:
      {==}

def wl_start(~A: Data, ~get: String -> Wr.Dec<A>, d: Wr.Dec<Nat>) ->
  {Wr.get_list.start(~A, ~get, d) == LawsBase.wire_read_list.count(~A, ~get, d) : Wr.Dec<List<&2, A>>}:
  match d:
    case Wr.Got{n, s}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          wl_go(~A, ~get, m, get(s))
    case Wr.Bad{}:
      {==}

def Wire.wire_list_reads_items(A, get, s):
  wl_start(~A, ~get, Wr.get_nat(s))
