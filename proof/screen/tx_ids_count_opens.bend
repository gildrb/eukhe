# eukhe: the proof of LAW tx_ids_count_opens
#
# PROOF: induction on the events, for every blocks and next id. An Open
# appends one block of id n (ids.app) and counts n up (ids.add_succ); a
# grow, a final and a flush keep the ids (ids.edit, ids.flush) and the next
# id; a resize keeps both.

import Base
import ../../bend/screen.bend as Sc
import ../../laws/screen/events.bend as ScreenEvents

def ids.cons(-a: Nat, -xs: List<&2, Nat>, -ys: List<&2, Nat>, e: {xs == ys : List<&2, Nat>}) -> {a <> xs == a <> ys : List<&2, Nat>}:
  %e : {a <> xs == a <> _ : List<&2, Nat>}
  {==}

def ids.app_nil(xs: List<&2, Nat>) -> {xs == List.append(&2, Nat, xs, Nil{}) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case x <> xr:
      ids.cons(x, xr, List.append(&2, Nat, xr, Nil{}), ids.app_nil(xr))

def ids.app(bs: List<&2, Sc.Blk>, -ys: List<&2, Sc.Blk>, -zs: List<&2, Nat>) -> {List.append(&2, Nat, ScreenEvents.tx_ids(List.append(&2, Sc.Blk, bs, ys)), zs) == List.append(&2, Nat, ScreenEvents.tx_ids(bs), List.append(&2, Nat, ScreenEvents.tx_ids(ys), zs)) : List<&2, Nat>}:
  match bs:
    case Nil{}:
      {==}
    case b <> br:
      match b:
        case Sc.Blk{i, s, l}:
          ids.cons(i, List.append(&2, Nat, ScreenEvents.tx_ids(List.append(&2, Sc.Blk, br, ys)), zs), List.append(&2, Nat, ScreenEvents.tx_ids(br), List.append(&2, Nat, ScreenEvents.tx_ids(ys), zs)), ids.app(br, ys, zs))

# an edited block keeps its id
def ids.one(+i: Nat, s: Sc.St, +l: Nat, g: Maybe<&2, Nat>, -rest: List<&2, Sc.Blk>) -> {ScreenEvents.tx_ids(Sc.edit.one(Sc.Blk{i, s, l}, g) <> rest) == i <> ScreenEvents.tx_ids(rest) : List<&2, Nat>}:
  match s g:
    case Sc.Active{} None{}:
      {==}
    case Sc.Active{} Some{n}:
      {==}
    case Sc.Final{} None{}:
      {==}
    case Sc.Final{} Some{n}:
      {==}
    case Sc.Comm{} None{}:
      {==}
    case Sc.Comm{} Some{n}:
      {==}

def ids.edit_at(+i: Nat, s: Sc.St, +l: Nat, +br: List<&2, Sc.Blk>, +x: Nat, +g: Maybe<&2, Nat>, hit: Bool, ih: {ScreenEvents.tx_ids(Sc.edit.go(br, x, g, Sc.bid.at(br, x))) == ScreenEvents.tx_ids(br) : List<&2, Nat>}) -> {ScreenEvents.tx_ids(Sc.edit.go(Sc.Blk{i, s, l} <> br, x, g, hit)) == i <> ScreenEvents.tx_ids(br) : List<&2, Nat>}:
  match hit:
    case True{}:
      Equal.trans(List<&2, Nat>, ScreenEvents.tx_ids(Sc.edit.one(Sc.Blk{i, s, l}, g) <> Sc.edit.go(br, x, g, Sc.bid.at(br, x))), i <> ScreenEvents.tx_ids(Sc.edit.go(br, x, g, Sc.bid.at(br, x))), i <> ScreenEvents.tx_ids(br), ids.one(i, s, l, g, Sc.edit.go(br, x, g, Sc.bid.at(br, x))), ids.cons(i, ScreenEvents.tx_ids(Sc.edit.go(br, x, g, Sc.bid.at(br, x))), ScreenEvents.tx_ids(br), ih))
    case False{}:
      ids.cons(i, ScreenEvents.tx_ids(Sc.edit.go(br, x, g, Sc.bid.at(br, x))), ScreenEvents.tx_ids(br), ih)

def ids.edit(bs: List<&2, Sc.Blk>, +x: Nat, +g: Maybe<&2, Nat>, hit: Bool) -> {ScreenEvents.tx_ids(Sc.edit.go(bs, x, g, hit)) == ScreenEvents.tx_ids(bs) : List<&2, Nat>}:
  match bs:
    case Nil{}:
      {==}
    case b <> +br:
      match b:
        case Sc.Blk{+i, s, +l}:
          ids.edit_at(i, s, l, br, x, g, hit, ids.edit(br, x, g, Sc.bid.at(br, x)))

def ids.flush(bs: List<&2, Sc.Blk>) -> {ScreenEvents.tx_ids(Sc.flush(bs)) == ScreenEvents.tx_ids(bs) : List<&2, Nat>}:
  match bs:
    case Nil{}:
      {==}
    case b <> br:
      match b:
        case Sc.Blk{i, s, l}:
          match s:
            case Sc.Active{}:
              {==}
            case Sc.Final{}:
              ids.cons(i, ScreenEvents.tx_ids(Sc.flush(br)), ScreenEvents.tx_ids(br), ids.flush(br))
            case Sc.Comm{}:
              ids.cons(i, ScreenEvents.tx_ids(Sc.flush(br)), ScreenEvents.tx_ids(br), ids.flush(br))

def ids.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %ids.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def ids.pair(-a: List<&2, Nat>, -c: List<&2, Nat>, -b: Nat, -d: Nat, e1: {a == c : List<&2, Nat>}, e2: {b == d : Nat}) -> {(a, b) == (c, d) : List<&2, Nat> & Nat}:
  %e1 : {(a, b) == (_, d) : List<&2, Nat> & Nat}
  %e2 : {(a, b) == (a, _) : List<&2, Nat> & Nat}
  {==}

def ids.run(es: List<&2, Sc.Ev>, +bs: List<&2, Sc.Blk>, +n: Nat, +w: Nat) -> {ScreenEvents.tx_ids_next(Sc.run(es, Sc.Tx{bs, n, w})) == (List.append(&2, Nat, ScreenEvents.tx_ids(bs), ScreenEvents.tx_from(ScreenEvents.tx_opens(es), n)), Nat.add(ScreenEvents.tx_opens(es), n)) : List<&2, Nat> & Nat}:
  match es:
    case Nil{}:
      %ids.app_nil(ScreenEvents.tx_ids(bs)) : {(ScreenEvents.tx_ids(bs), n) == (_, n) : List<&2, Nat> & Nat}
      {==}
    case e <> +rest:
      match e:
        case Sc.Open{}:
          +bs2 = List.append(&2, Sc.Blk, bs, [Sc.Blk{n, Sc.Active{}, 0n}])
          Equal.trans(List<&2, Nat> & Nat, ScreenEvents.tx_ids_next(Sc.run(rest, Sc.Tx{bs2, 1n+n, w})), (List.append(&2, Nat, ScreenEvents.tx_ids(bs2), ScreenEvents.tx_from(ScreenEvents.tx_opens(rest), 1n+n)), Nat.add(ScreenEvents.tx_opens(rest), 1n+n)), (List.append(&2, Nat, ScreenEvents.tx_ids(bs), n <> ScreenEvents.tx_from(ScreenEvents.tx_opens(rest), 1n+n)), 1n+Nat.add(ScreenEvents.tx_opens(rest), n)), ids.run(rest, bs2, 1n+n, w), ids.pair(List.append(&2, Nat, ScreenEvents.tx_ids(bs2), ScreenEvents.tx_from(ScreenEvents.tx_opens(rest), 1n+n)), List.append(&2, Nat, ScreenEvents.tx_ids(bs), n <> ScreenEvents.tx_from(ScreenEvents.tx_opens(rest), 1n+n)), Nat.add(ScreenEvents.tx_opens(rest), 1n+n), 1n+Nat.add(ScreenEvents.tx_opens(rest), n), ids.app(bs, [Sc.Blk{n, Sc.Active{}, 0n}], ScreenEvents.tx_from(ScreenEvents.tx_opens(rest), 1n+n)), ids.add_succ(ScreenEvents.tx_opens(rest), n)))
        case Sc.Grow{+x, +k}:
          %ids.edit(bs, x, Some{k}, Sc.bid.at(bs, x)) : {ScreenEvents.tx_ids_next(Sc.run(rest, Sc.Tx{Sc.edit(bs, x, Some{k}), n, w})) == (List.append(&2, Nat, _, ScreenEvents.tx_from(ScreenEvents.tx_opens(rest), n)), Nat.add(ScreenEvents.tx_opens(rest), n)) : List<&2, Nat> & Nat}
          ids.run(rest, Sc.edit(bs, x, Some{k}), n, w)
        case Sc.Fin{+x}:
          %ids.edit(bs, x, None{}, Sc.bid.at(bs, x)) : {ScreenEvents.tx_ids_next(Sc.run(rest, Sc.Tx{Sc.edit(bs, x, None{}), n, w})) == (List.append(&2, Nat, _, ScreenEvents.tx_from(ScreenEvents.tx_opens(rest), n)), Nat.add(ScreenEvents.tx_opens(rest), n)) : List<&2, Nat> & Nat}
          ids.run(rest, Sc.edit(bs, x, None{}), n, w)
        case Sc.Flush{}:
          %ids.flush(bs) : {ScreenEvents.tx_ids_next(Sc.run(rest, Sc.Tx{Sc.flush(bs), n, w})) == (List.append(&2, Nat, _, ScreenEvents.tx_from(ScreenEvents.tx_opens(rest), n)), Nat.add(ScreenEvents.tx_opens(rest), n)) : List<&2, Nat> & Nat}
          ids.run(rest, Sc.flush(bs), n, w)
        case Sc.Resize{v}:
          ids.run(rest, bs, n, v)

def ScreenEvents.tx_ids_count_opens(es, bs, n, w):
  ids.run(es, bs, n, w)
