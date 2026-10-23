# eukhe: the proof of LAW schema_keeps_params

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools

def pl.or_tr(a: Bool, +b: Bool, hb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      hb

def tools.pl.keep(b: Bool, +ps: List<&2, Nat>, +x: Nat, has: {Tl.elem(ps, x) == True{} : Bool}) -> {Tl.elem(Tl.add_intent(b, ps), x) == True{} : Bool}:
  match b:
    case True{}:
      has
    case False{}:
      pl.or_tr(Nat.is_eq(Tl.intent(), x), Tl.elem(ps, x), has)

def pl.schema_keeps_params(+s: Tl.Schema, +x: Nat, has: {Tl.elem(Tl.Schema.params(s), x) == True{} : Bool}) -> {Tl.elem(Tl.Schema.params(Tl.build(s)), x) == True{} : Bool}:
  match s:
    case Tl.Schema{+ps, v}:
      tools.pl.keep(Tl.elem(ps, Tl.intent()), ps, x, has)

def Tools.schema_keeps_params(s, x, has):
  pl.schema_keeps_params(s, x, has)
