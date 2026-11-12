# eukhe: the proof of LAW bound_look_tail_trims: the cut is the text's bytes less the margin, at most the text's bytes; what is stored is at most the margin, which is at most the margin cut

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def lt.of(w: Bd.Win, +b: Nat, +l: Nat, +bs: Nat, +nl: Nat, +op: Bool, +x: Bd.Body, +xs: List<&2, Nat>, +mc: Nat, hm: {Nat.is_le(Bd.margin(Bd.Cap{b, l, True{}}, x), mc) == True{} : Bool}) -> {Nat.add(Bound.bd_seen_cut(Bound.bd_snd.look(Bd.look.of(Bd.Cap{b, l, True{}}, bs, nl, op, x, Bd.total(xs), w))), Bound.bd_st_stored(Bound.bd_fst.look(Bd.look.of(Bd.Cap{b, l, True{}}, bs, nl, op, x, Bd.total(xs), w)))) == Bound.bd_total(xs) : Nat} & {Nat.is_le(Bound.bd_st_stored(Bound.bd_fst.look(Bd.look.of(Bd.Cap{b, l, True{}}, bs, nl, op, x, Bd.total(xs), w))), mc) == True{} : Bool}:
  match w:
    case Bd.Win{kb, kl}:
      +len = Bd.total(xs)
      +m = Bd.margin(Bd.Cap{b, l, True{}}, x)
      +cut = Nat.sub(len, m)
      (Equal.trans(Nat, Nat.add(cut, Nat.sub(len, cut)), len, Bound.bd_total(xs), LBound.bnd.add_sub(cut, len, LBound.bnd.sub_le(len, m)), LBound.bnd.total(xs)), LBound.bnd.le_trans(Nat.sub(len, cut), m, mc, LBound.bnd.subsub_le(len, m), hm))

def Bound.bound_look_tail_trims(b, l, bs, nl, op, sd, xs, o, hc, tc, mc):
  +x = {Bd.Body{xs, o, hc, tc, mc} : Bd.Body}
  lt.of(Bd.window(Bd.Cap{b, l, True{}}, x), b, l, bs, nl, op, x, xs, mc, LBound.bnd.least_le(mc, Bd.margin.lines(Bd.mline(List.reverse(&2, Nat, xs), Bd.lines(l, o)), Bd.total(xs))))
