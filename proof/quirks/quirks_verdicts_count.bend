# eukhe: the proof of LAW quirks_verdicts_count
# One verdict per rule, by induction on the rules (QP.qp.len).

import Base
import ../../laws/quirks.bend as Quirks
import ./base.bend as QP

def Quirks.quirks_verdicts_count(known, rs):
  QP.qp.len(rs, known, 0n)
