# eukhe: the proof of LAW dyn_drops_quit

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools

# a drop leaves no copy of t; hit is the head test
def pl.drop_go(xs: List<&2, Nat>, +t: Nat, hit: Bool, e: {Tl.is.at(xs, t) == hit : Bool}) -> {Tl.elem(Tl.drop.go(xs, t, hit), t) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +y <> +rest:
      match hit:
        case True{}:
          pl.drop_go(rest, t, Tl.is.at(rest, t), {==})
        case False{}:
          %Equal.sym(Bool, Nat.is_eq(y, t), False{}, e) : {Bool.or(_, Tl.elem(Tl.drop.go(rest, t, Tl.is.at(rest, t)), t)) == False{} : Bool}
          pl.drop_go(rest, t, Tl.is.at(rest, t), {==})

def pl.dyn_drops_quit(+s: Tl.Sess, +t: Nat) -> {Tl.dyn_call(Tl.step(s, Tl.Quit{t}), t) == False{} : Bool}:
  match s:
    case Tl.Sess{r, +d, x}:
      pl.drop_go(d, t, Tl.is.at(d, t), {==})

def Tools.dyn_drops_quit(s, t):
  pl.dyn_drops_quit(s, t)
