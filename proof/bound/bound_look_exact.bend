# eukhe: the proof of LAW bound_look_exact: the text's bytes, window and margin are the spec's; the rest computes

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def blk.cut(t: Bool, +c: Bd.Cap, +x: Bd.Body, +len: Nat) -> {Bd.look.cut(t, c, x, len) == Bound.bd_look.cut(t, c, x, len) : Nat}:
  match t:
    case False{}:
      {==}
    case True{}:
      Equal.cong(Nat, Nat, z => Nat.sub(len, z), Bd.margin(c, x), Bound.bd_margin(c, x), LBound.bnd.margin(c, x))

def blk.of(w: Bd.Win, c: Bd.Cap, op: Bool, +b: Nat, +nl: Nat, +x: Bd.Body, +len: Nat) -> {Bd.look.of(c, b, nl, op, x, len, w) == Bound.bd_look.of(c, b, nl, op, x, len, w) : Bd.St & Bd.Seen}:
  match w:
    case Bd.Win{+kb, +kl}:
      match c:
        case Bd.Cap{+cb, +ck, ct}:
          match ct:
            case False{}:
              match op:
                case False{}:
                  {==}
                case True{}:
                  {==}
            case True{}:
              match op:
                case False{}:
                  +cc = {Bd.Cap{cb, ck, True{}} : Bd.Cap}
                  Equal.cong(Nat, Bd.St & Bd.Seen, z => (Bd.St{cc, b, nl, False{}, Nat.sub(len, z)}, Bd.Seen{Bd.Span{Nat.sub(len, kb), len}, Nat.sub(b, kb), Nat.sub(nl, kl), z}), Bd.look.cut(True{}, cc, x, len), Bound.bd_look.cut(True{}, cc, x, len), blk.cut(True{}, cc, x, len))
                case True{}:
                  +cc = {Bd.Cap{cb, ck, True{}} : Bd.Cap}
                  Equal.cong(Nat, Bd.St & Bd.Seen, z => (Bd.St{cc, b, nl, True{}, Nat.sub(len, z)}, Bd.Seen{Bd.Span{Nat.sub(len, kb), len}, Nat.sub(b, kb), Nat.sub(1n+nl, kl), z}), Bd.look.cut(True{}, cc, x, len), Bound.bd_look.cut(True{}, cc, x, len), blk.cut(True{}, cc, x, len))

def Bound.bound_look_exact(s, x):
  match s:
    case Bd.St{+c, +b, +nl, +op, sd}:
      match x:
        case Bd.Body{+xs, +o, +hc, +tc, +mc}:
          +bx = {Bd.Body{xs, o, hc, tc, mc} : Bd.Body}
          %LBound.bnd.total(xs) : {Bd.look.of(c, b, nl, op, bx, Bd.total(xs), Bd.window(c, bx)) == Bound.bd_look.of(c, b, nl, op, bx, _, Bound.bd_window(c, bx)) : Bd.St & Bd.Seen}
          %LBound.bnd.window(c, bx) : {Bd.look.of(c, b, nl, op, bx, Bd.total(xs), Bd.window(c, bx)) == Bound.bd_look.of(c, b, nl, op, bx, Bd.total(xs), _) : Bd.St & Bd.Seen}
          blk.of(Bd.window(c, bx), c, op, b, nl, bx, Bd.total(xs))
