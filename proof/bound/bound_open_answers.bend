# eukhe: the proof of LAW bound_open_answers: the open reads back whole as the cap

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def oa.of(c: Bd.Cap) -> {FBd.open.of(FBd.cap.lead(Bound.bd_cap(c, Nil{}))) == (FBd.Run{Bd.St{c, 0n, 0n, False{}, 0n}}, Bound.bd_spell([Bound.bd_bit(Bound.bd_cap_tail(c))])) : FBd.St & String}:
  match c:
    case Bd.Cap{b, k, t}:
      match t:
        case False{}:
          {==}
        case True{}:
          {==}

def Bound.bound_open_answers(c, h):
  +xs = {Bound.bd_cap(c, Nil{}) : List<&2, Nat>}
  %LBound.bnd.read(xs, h) : {FBd.open.got(_) == (FBd.Run{Bd.St{c, 0n, 0n, False{}, 0n}}, Bound.bd_spell([Bound.bd_bit(Bound.bd_cap_tail(c))])) : FBd.St & String}
  oa.of(c)
