# eukhe: the proof of LAW quirks_verdict_fine
# Induction on the rules and both indexes (QV.qv.fine): at rule i, a fine
# verdict means the clash scan of the later rules found none
# (QV.qv.cg_none).

import Base
import ../../laws/quirks.bend as Quirks
import ./base/verdicts.bend as QV

def Quirks.quirks_verdict_fine(known, rs, i, j, r, s, at, fine, later, after):
  QV.qv.fine(rs, known, 0n, i, j, r, s, at, fine, later, after)
