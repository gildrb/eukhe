# eukhe: the proof of LAW headless_settle_done_iff_quiet
#
# PROOF: case analysis on the facts in the order the model reads them: a
# busy conversation, a nonzero count or an unknown read makes the model
# pending, so it never stops (hs.stays), and makes the run not
# quiet; with none of them the model stops and the run is quiet.

import Base
import ../../bend/headless_settle.bend as Hs
import ../../spec/durable/headless.bend as Sp
import ../../laws/headless_settle.bend as HeadlessSettle
import ./base.bend as LAHeadlessSettle

def HeadlessSettle.headless_settle_done_iff_quiet(f):
  match f:
    case Hs.Facts{b, j, k, c, w, x, u, l}:
      match b:
        case True{}:
          LAHeadlessSettle.hs.stays(l)
        case False{}:
          match j:
            case 1n+p:
              LAHeadlessSettle.hs.stays(l)
            case 0n:
              match k:
                case 1n+p:
                  LAHeadlessSettle.hs.stays(l)
                case 0n:
                  match c:
                    case 1n+p:
                      LAHeadlessSettle.hs.stays(l)
                    case 0n:
                      match w:
                        case 1n+p:
                          LAHeadlessSettle.hs.stays(l)
                        case 0n:
                          match x:
                            case 1n+p:
                              LAHeadlessSettle.hs.stays(l)
                            case 0n:
                              match u:
                                case True{}:
                                  LAHeadlessSettle.hs.stays(l)
                                case False{}:
                                  {==}
