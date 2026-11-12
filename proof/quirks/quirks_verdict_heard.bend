# eukhe: the proof of LAW quirks_verdict_heard
# Induction on the rules and the index (QV.qv.heard): the verdict on rule i
# is Unheard exactly when its directive is not one of the known.

import Base
import ../../laws/quirks.bend as Quirks
import ./base/verdicts.bend as QV

def Quirks.quirks_verdict_heard(known, rs, i, r, at):
  QV.qv.heard(rs, known, 0n, i, r, at)
