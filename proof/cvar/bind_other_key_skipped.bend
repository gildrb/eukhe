# eukhe: the proof of LAW bind_other_key_skipped
# The first bind is of another key, so the lookup goes on to the rest.

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/entry.bend as CvarEntry

def CvarEntry.bind_other_key_skipped(j, c, bs, k, as, other):
  %Equal.sym(Bool, Nat.is_eq(j, k), False{}, other) : {Cv.expand(Cv.bound.go(Cv.KeyBind{j, c} <> bs, k, _), as) == Cv.press(bs, k, as) : Cv.Exp}
  {==}
