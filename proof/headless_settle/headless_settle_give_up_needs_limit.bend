# eukhe: the proof of LAW headless_settle_give_up_needs_limit
#
# PROOF: below the limit the model stops or waits, pending or not
# (hs.no_give_up), whatever the facts make pending.

import Base
import ../../bend/headless_settle.bend as Hs
import ../../laws/headless_settle.bend as HeadlessSettle

def hs.no_give_up(p: Bool) -> {HeadlessSettle.gives_up(Hs.decide(p, False{})) == False{} : Bool}:
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

def HeadlessSettle.headless_settle_give_up_needs_limit(b, j, k, c, w, x, u):
  hs.no_give_up(Bool.or(b, Bool.or(Hs.some(j), Bool.or(Hs.some(k), Bool.or(Hs.some(c), Bool.or(Hs.some(w), Bool.or(Hs.some(x), u)))))))
