# eukhe: the proof of LAW quirks_verdict_first
# Induction on the rules and both indexes (QV.qv.first): at rule i, the
# clash scan stops at its first hit, so no rule before it clashes
# (QV.qv.cg_first).

import Base
import ../../laws/quirks.bend as Quirks
import ./base/verdicts.bend as QV

def Quirks.quirks_verdict_first(known, rs, i, j, k, r, s, at, clash, mid, after, before):
  QV.qv.first(rs, known, 0n, i, k, r, s, j, at, clash, mid, after, before)
