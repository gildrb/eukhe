# eukhe: the proof of LAW bound_tail_memory: a tail stores the text, and answers a store only when the stored bytes are not past twice its bytes and 8

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def tm.of(tr: Bool, +c: Bd.Cap, +bs: Nat, +nl: Nat, o: Bool, +st: Nat, +b: Nat, e: {Nat.is_lt(Nat.add(Nat.add(b, b), 8n), st) == tr : Bool}) -> {Bound.bd_st_stored(Bound.bd_fst.act(Bd.out.tail(tr, c, bs, nl, o, st))) == st : Nat} & {Bound.bd_tail_within(Bound.bd_snd.act(Bd.out.tail(tr, c, bs, nl, o, st)), st, b) == True{} : Bool}:
  match tr:
    case True{}:
      ({==}, {==})
    case False{}:
      ({==}, LBound.bnd.nlt_le(Nat.add(Nat.add(b, b), 8n), st, e))

def Bound.bound_tail_memory(b, l, bs, nl, op, sd, n, k, o):
  tm.of(Nat.is_lt(Nat.add(Nat.add(b, b), 8n), Nat.add(sd, n)), Bd.Cap{b, l, True{}}, Nat.add(bs, n), Nat.add(nl, k), o, Nat.add(sd, n), b, {==})
