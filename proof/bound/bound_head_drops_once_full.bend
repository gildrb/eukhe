# eukhe: the proof of LAW bound_head_drops_once_full: a head's answer to a text reads only the counts so far (full), never what it stored; the texts so far add their bytes and newlines to the counts

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def hd.act(f: Bool, +c: Bd.Cap, +bb: Nat, +nl: Nat, o: Bool, +sd: Nat, +n: Nat) -> {Bound.bd_snd.act(Bd.out.head(f, c, bb, nl, o, sd, n)) == Bound.bd_head_act(f) : Bd.Act}:
  match f:
    case True{}:
      {==}
    case False{}:
      {==}

# the next text after rest, from the state after one text (stored or dropped)
def hd.step(f: Bool, rest: List<&2, Bound.BdText>, +b: Nat, +l: Nat, +bb: Nat, +nl: Nat, o1: Bool, +sd: Nat, +n1: Nat, +n: Nat, +k: Nat, +o: Bool, ih_drop: {Bound.bd_snd.act(Bd.out(Bound.bd_drive(rest, Bd.St{Bd.Cap{b, l, False{}}, bb, nl, o1, sd}), n, k, o)) == Bound.bd_head_act(Bool.or(Nat.is_lt(b, Nat.add(bb, Bound.bd_sum_n(rest))), Nat.is_le(l, Nat.add(nl, Bound.bd_sum_k(rest))))) : Bd.Act}, ih_store: {Bound.bd_snd.act(Bd.out(Bound.bd_drive(rest, Bd.St{Bd.Cap{b, l, False{}}, bb, nl, o1, Nat.add(sd, n1)}), n, k, o)) == Bound.bd_head_act(Bool.or(Nat.is_lt(b, Nat.add(bb, Bound.bd_sum_n(rest))), Nat.is_le(l, Nat.add(nl, Bound.bd_sum_k(rest))))) : Bd.Act}) -> {Bound.bd_snd.act(Bd.out(Bound.bd_drive(rest, Bound.bd_fst.act(Bd.out.head(f, Bd.Cap{b, l, False{}}, bb, nl, o1, sd, n1))), n, k, o)) == Bound.bd_head_act(Bool.or(Nat.is_lt(b, Nat.add(bb, Bound.bd_sum_n(rest))), Nat.is_le(l, Nat.add(nl, Bound.bd_sum_k(rest))))) : Bd.Act}:
  match f:
    case True{}:
      ih_drop
    case False{}:
      ih_store

# from any head state, the answer to the next text after es
def hd.go(es: List<&2, Bound.BdText>, +b: Nat, +l: Nat, +bb: Nat, +nl: Nat, op: Bool, +sd: Nat, +n: Nat, +k: Nat, +o: Bool) -> {Bound.bd_snd.act(Bd.out(Bound.bd_drive(es, Bd.St{Bd.Cap{b, l, False{}}, bb, nl, op, sd}), n, k, o)) == Bound.bd_head_act(Bool.or(Nat.is_lt(b, Nat.add(bb, Bound.bd_sum_n(es))), Nat.is_le(l, Nat.add(nl, Bound.bd_sum_k(es))))) : Bd.Act}:
  match es:
    case Nil{}:
      %Equal.sym(Nat, Nat.add(bb, 0n), bb, LBound.bnd.add_zero(bb)) : {Bound.bd_snd.act(Bd.out(Bd.St{Bd.Cap{b, l, False{}}, bb, nl, op, sd}, n, k, o)) == Bound.bd_head_act(Bool.or(Nat.is_lt(b, _), Nat.is_le(l, Nat.add(nl, 0n)))) : Bd.Act}
      %Equal.sym(Nat, Nat.add(nl, 0n), nl, LBound.bnd.add_zero(nl)) : {Bound.bd_snd.act(Bd.out(Bd.St{Bd.Cap{b, l, False{}}, bb, nl, op, sd}, n, k, o)) == Bound.bd_head_act(Bool.or(Nat.is_lt(b, bb), Nat.is_le(l, _))) : Bd.Act}
      hd.act(Bool.or(Nat.is_lt(b, bb), Nat.is_le(l, nl)), Bd.Cap{b, l, False{}}, Nat.add(bb, n), Nat.add(nl, k), o, sd, n)
    case +e <> +rest:
      match e:
        case Bound.BdText{+n1, +k1, +o1}:
          %LBound.bnd.add_assoc(bb, n1, Bound.bd_sum_n(rest)) : {Bound.bd_snd.act(Bd.out(Bound.bd_drive(rest, Bound.bd_fst.act(Bd.out(Bd.St{Bd.Cap{b, l, False{}}, bb, nl, op, sd}, n1, k1, o1))), n, k, o)) == Bound.bd_head_act(Bool.or(Nat.is_lt(b, _), Nat.is_le(l, Nat.add(nl, Nat.add(k1, Bound.bd_sum_k(rest)))))) : Bd.Act}
          %LBound.bnd.add_assoc(nl, k1, Bound.bd_sum_k(rest)) : {Bound.bd_snd.act(Bd.out(Bound.bd_drive(rest, Bound.bd_fst.act(Bd.out(Bd.St{Bd.Cap{b, l, False{}}, bb, nl, op, sd}, n1, k1, o1))), n, k, o)) == Bound.bd_head_act(Bool.or(Nat.is_lt(b, Nat.add(Nat.add(bb, n1), Bound.bd_sum_n(rest))), Nat.is_le(l, _))) : Bd.Act}
          hd.step(Bool.or(Nat.is_lt(b, bb), Nat.is_le(l, nl)), rest, b, l, Nat.add(bb, n1), Nat.add(nl, k1), o1, sd, n1, n, k, o, hd.go(rest, b, l, Nat.add(bb, n1), Nat.add(nl, k1), o1, sd, n, k, o), hd.go(rest, b, l, Nat.add(bb, n1), Nat.add(nl, k1), o1, Nat.add(sd, n1), n, k, o))

def Bound.bound_head_drops_once_full(b, l, es, n, k, o):
  hd.go(es, b, l, 0n, 0n, False{}, 0n, n, k, o)
