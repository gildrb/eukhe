# eukhe: the proof of LAW headless_settle_limit_exits
#
# PROOF: at the limit the model stops or gives up, pending or not
# (hs.no_wait), whatever the facts make pending.

import Base
import ../../bend/headless_settle.bend as Hs
import ../../laws/headless_settle.bend as HeadlessSettle

def hs.no_wait(p: Bool) -> {HeadlessSettle.waiting(Hs.decide(p, True{})) == False{} : Bool}:
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

def HeadlessSettle.headless_settle_limit_exits(b, j, k, c, w, x, u):
  hs.no_wait(Bool.or(b, Bool.or(Hs.some(j), Bool.or(Hs.some(k), Bool.or(Hs.some(c), Bool.or(Hs.some(w), Bool.or(Hs.some(x), u)))))))
