# eukhe: the proof of LAW bind_press_exact
# The bind lookup is the spec's (pxb.bound); a press expands it, which is
# the spec's expansion (alias_expand_exact).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/entry.bend as Cvar
import ./alias_expand_exact.bend as PAE

def pxb.step(b: Bool, +j: Nat, +c: List<&2, Cv.Cmd>, +rest: List<&2, Cv.KeyBind>, +k: Nat, ih: {Cv.bound(rest, k) == Cvar.spec_bound(rest, k) : List<&2, Cv.Cmd>}) -> {Cv.bound.go(Cv.KeyBind{j, c} <> rest, k, b) == Cvar.spec_bound.pick(b, c, Cvar.spec_bound(rest, k)) : List<&2, Cv.Cmd>}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

def pxb.bound(bs: List<&2, Cv.KeyBind>, +k: Nat) -> {Cv.bound(bs, k) == Cvar.spec_bound(bs, k) : List<&2, Cv.Cmd>}:
  match bs:
    case Nil{}:
      {==}
    case Cv.KeyBind{+j, +c} <> +rest:
      pxb.step(Nat.is_eq(j, k), j, c, rest, k, pxb.bound(rest, k))

def pxb.press(+bs: List<&2, Cv.KeyBind>, +k: Nat, +as: List<&2, Cv.Alias>) -> {Cv.press(bs, k, as) == Cvar.spec_press(bs, k, as) : Cv.Exp}:
  %pxb.bound(bs, k) : {Cv.expand(Cv.bound(bs, k), as) == Cvar.spec_expand(_, as) : Cv.Exp}
  PAE.pxx.expand_orig(Cv.bound(bs, k), as)

def Cvar.bind_press_exact(bs, k, as):
  (pxb.press(bs, k, as), pxb.bound(bs, k))

def pxb.press_orig(+bs: List<&2, Cv.KeyBind>, +k: Nat, +as: List<&2, Cv.Alias>) -> {Cv.press(bs, k, as) == Cvar.spec_press(bs, k, as) : Cv.Exp}:
  %pxb.bound(bs, k) : {Cv.expand(Cv.bound(bs, k), as) == Cvar.spec_expand(_, as) : Cv.Exp}
  PAE.pxx.expand_orig(Cv.bound(bs, k), as)
