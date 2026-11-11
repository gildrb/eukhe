# eukhe: the proof of LAW restart_window_append
# The window ages and tests each age on its own, in order, so the ages kept
# from xs ++ ys are those kept from xs, then from ys (srw.keep_app); the
# premises name each part (the tail of a list that starts with 0).

import Base
import ../../bend/supervise.bend as Su
import ../../laws/supervise.bend as Supervise

def srw.put_app(b: Bool, +x: Nat, p: List<&2, Nat>, +q: List<&2, Nat>) -> {Su.keep.put(b, x, List.append(&2, Nat, p, q)) == List.append(&2, Nat, Su.keep.put(b, x, p), q) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the ages kept from xs ++ ys: those kept from xs, then those kept from ys
def srw.keep_app(+w: Nat, +g: Nat, xs: List<&2, Nat>, +ys: List<&2, Nat>) -> {Su.keep(w, Su.older(g, List.append(&2, Nat, xs, ys))) == List.append(&2, Nat, Su.keep(w, Su.older(g, xs)), Su.keep(w, Su.older(g, ys))) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      +b = Nat.is_lt(Nat.add(g, x), w)
      +kt = Su.keep(w, Su.older(g, t))
      +ky = Su.keep(w, Su.older(g, ys))
      %Equal.sym(List<&2, Nat>, Su.keep(w, Su.older(g, List.append(&2, Nat, t, ys))), List.append(&2, Nat, kt, ky), srw.keep_app(w, g, t, ys)) : {Su.keep.put(b, Nat.add(g, x), _) == List.append(&2, Nat, Su.keep.put(b, Nat.add(g, x), kt), ky) : List<&2, Nat>}
      srw.put_app(b, Nat.add(g, x), kt, ky)

def srw.tl(l: List<&2, Nat>) -> List<&2, Nat>:
  match l:
    case Nil{}:
      Nil{}
    case x <> t:
      t

def srw.tail(-a: List<&2, Nat>, -b: List<&2, Nat>, e: {0n <> a == 0n <> b : List<&2, Nat>}) -> {a == b : List<&2, Nat>}:
  Equal.cong(List<&2, Nat>, List<&2, Nat>, l => srw.tl(l), 0n <> a, 0n <> b, e)

def Supervise.restart_window_append(c, xs, ys, g, p, q, hp, hq):
  +w = Su.Cfg.w(c)
  +kx = Su.keep(w, Su.older(g, xs))
  +ky = Su.keep(w, Su.older(g, ys))
  %Equal.sym(List<&2, Nat>, Su.keep(w, Su.older(g, List.append(&2, Nat, xs, ys))), List.append(&2, Nat, kx, ky), srw.keep_app(w, g, xs, ys)) : {0n <> _ == 0n <> List.append(&2, Nat, p, q) : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, kx, p, srw.tail(kx, p, hp)) : {0n <> List.append(&2, Nat, _, ky) == 0n <> List.append(&2, Nat, p, q) : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, ky, q, srw.tail(ky, q, hq)) : {0n <> List.append(&2, Nat, p, _) == 0n <> List.append(&2, Nat, p, q) : List<&2, Nat>}
  {==}
