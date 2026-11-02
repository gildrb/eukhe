# eukhe: lemmas of the list codec: two item readers (writers) that agree on
# every input give list readers (writers) that agree on every input. The
# laws' spec readers and spellers use Wr.get_list and Wr.put_list with
# their own item codecs; these lemmas meet the entries' item codecs.

import Base
import ../../bend/wire.bend as Wr

# the item loop at cur, with m more items after it
def lx.get_go(~A: Data, ~g1: String -> Wr.Dec<A>, ~g2: String -> Wr.Dec<A>, ~h: @s: String -> {g1(s) == g2(s) : Wr.Dec<A>}, m: Nat, cur: Wr.Dec<A>) -> {Wr.get_list.go(~A, ~g1, m, cur) == Wr.get_list.go(~A, ~g2, m, cur) : Wr.Dec<List<&2, A>>}:
  match m cur:
    case 0n Wr.Got{x, r}:
      {==}
    case 0n Wr.Bad{}:
      {==}
    case 1n++k Wr.Got{+x, +r}:
      %h(r) : {Wr.get_list.cons(A, x, Wr.get_list.go(~A, ~g1, k, g1(r))) == Wr.get_list.cons(A, x, Wr.get_list.go(~A, ~g2, k, _)) : Wr.Dec<List<&2, A>>}
      %lx.get_go(~A, ~g1, ~g2, ~h, k, g1(r)) : {Wr.get_list.cons(A, x, Wr.get_list.go(~A, ~g1, k, g1(r))) == Wr.get_list.cons(A, x, _) : Wr.Dec<List<&2, A>>}
      {==}
    case 1n+k Wr.Bad{}:
      {==}

def lx.get_start(~A: Data, ~g1: String -> Wr.Dec<A>, ~g2: String -> Wr.Dec<A>, ~h: @s: String -> {g1(s) == g2(s) : Wr.Dec<A>}, r: Wr.Dec<Nat>) -> {Wr.get_list.start(~A, ~g1, r) == Wr.get_list.start(~A, ~g2, r) : Wr.Dec<List<&2, A>>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          %h(s) : {Wr.get_list.go(~A, ~g1, m, g1(s)) == Wr.get_list.go(~A, ~g2, m, _) : Wr.Dec<List<&2, A>>}
          lx.get_go(~A, ~g1, ~g2, ~h, m, g1(s))
    case Wr.Bad{}:
      {==}

# the list readers of g1 and g2 agree
def lx.get(~A: Data, ~g1: String -> Wr.Dec<A>, ~g2: String -> Wr.Dec<A>, ~h: @s: String -> {g1(s) == g2(s) : Wr.Dec<A>}, +s: String) -> {Wr.get_list(~A, ~g1, s) == Wr.get_list(~A, ~g2, s) : Wr.Dec<List<&2, A>>}:
  lx.get_start(~A, ~g1, ~g2, ~h, Wr.get_nat(s))

def lx.put_step(~A: Data, ~p1: A -> String -> String, ~p2: A -> String -> String, ~h: @x: A -> @r: String -> {p1(x, r) == p2(x, r) : String}, +x: A, r: Nat & String) -> {Wr.put_list.step(~A, ~p1, x, r) == Wr.put_list.step(~A, ~p2, x, r) : Nat & String}:
  match r:
    case (n, +s):
      %h(x, s) : {(1n+n, p1(x, s)) == (1n+n, _) : Nat & String}
      {==}

def lx.put_go(~A: Data, ~p1: A -> String -> String, ~p2: A -> String -> String, ~h: @x: A -> @r: String -> {p1(x, r) == p2(x, r) : String}, xs: List<&2, A>, +rest: String) -> {Wr.put_list.go(~A, ~p1, xs, rest) == Wr.put_list.go(~A, ~p2, xs, rest) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %lx.put_go(~A, ~p1, ~p2, ~h, t, rest) : {Wr.put_list.step(~A, ~p1, x, Wr.put_list.go(~A, ~p1, t, rest)) == Wr.put_list.step(~A, ~p2, x, _) : Nat & String}
      lx.put_step(~A, ~p1, ~p2, ~h, x, Wr.put_list.go(~A, ~p1, t, rest))

# the list writers of p1 and p2 agree
def lx.put(~A: Data, ~p1: A -> String -> String, ~p2: A -> String -> String, ~h: @x: A -> @r: String -> {p1(x, r) == p2(x, r) : String}, xs: List<&2, A>, +rest: String) -> {Wr.put_list(~A, ~p1, xs, rest) == Wr.put_list(~A, ~p2, xs, rest) : String}:
  %lx.put_go(~A, ~p1, ~p2, ~h, xs, rest) : {Wr.put_list.fin(Wr.put_list.go(~A, ~p1, xs, rest)) == Wr.put_list.fin(_) : String}
  {==}
