# eukhe: the proof of LAW bound_look_head_keeps: a head's cut is 0, so it stores the whole text

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def lh.of(w: Bd.Win, +b: Nat, +l: Nat, +bs: Nat, +nl: Nat, +op: Bool, +x: Bd.Body, +xs: List<&2, Nat>) -> {Bound.bd_seen_cut(Bound.bd_snd.look(Bd.look.of(Bd.Cap{b, l, False{}}, bs, nl, op, x, Bd.total(xs), w))) == 0n : Nat} & {Bound.bd_st_stored(Bound.bd_fst.look(Bd.look.of(Bd.Cap{b, l, False{}}, bs, nl, op, x, Bd.total(xs), w))) == Bound.bd_total(xs) : Nat}:
  match w:
    case Bd.Win{kb, kl}:
      %Equal.sym(Nat, Nat.sub(Bd.total(xs), 0n), Bd.total(xs), LBound.bnd.sub_zero(Bd.total(xs))) : {0n == 0n : Nat} & {_ == Bound.bd_total(xs) : Nat}
      ({==}, LBound.bnd.total(xs))

def Bound.bound_look_head_keeps(b, l, bs, nl, op, sd, x):
  match x:
    case Bd.Body{+xs, +o, +hc, +tc, +mc}:
      lh.of(Bd.window(Bd.Cap{b, l, False{}}, Bd.Body{xs, o, hc, tc, mc}), b, l, bs, nl, op, Bd.Body{xs, o, hc, tc, mc}, xs)
