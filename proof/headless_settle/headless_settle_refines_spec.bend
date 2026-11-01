# eukhe: the proof of LAW headless_settle_refines_spec
#
# PROOF: case analysis on the facts in the order the model reads them: a
# busy conversation, a nonzero count or an unknown read makes the model
# pending and the spec not quiet, and both then give up exactly at the
# limit (hs.pending); with none of them both stop.

import Base
import ../../bend/headless_settle.bend as Hs
import ../../spec/durable/headless.bend as Sp
import ../../laws/headless_settle.bend as HeadlessSettle

# pending (not quiet): give up at the limit, else wait, in both
def hs.pending(l: Bool) -> {Hs.decide(True{}, l) == Sp.settle_spec.pick(False{}, l) : Hs.Settle}:
  match l:
    case True{}:
      {==}
    case False{}:
      {==}

def HeadlessSettle.headless_settle_refines_spec(f):
  match f:
    case Hs.Facts{b, j, k, c, w, x, u, l}:
      match b:
        case True{}:
          hs.pending(l)
        case False{}:
          match j:
            case 1n+p:
              hs.pending(l)
            case 0n:
              match k:
                case 1n+p:
                  hs.pending(l)
                case 0n:
                  match c:
                    case 1n+p:
                      hs.pending(l)
                    case 0n:
                      match w:
                        case 1n+p:
                          hs.pending(l)
                        case 0n:
                          match x:
                            case 1n+p:
                              hs.pending(l)
                            case 0n:
                              match u:
                                case True{}:
                                  hs.pending(l)
                                case False{}:
                                  {==}
