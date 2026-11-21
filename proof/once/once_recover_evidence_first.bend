# eukhe: the proof of LAW once_recover_evidence_first
#
# PROOF: by the mode: landed computes to an adopt, clean to the verdict
# of a pending effect (a launch on a resume, an abandon on a stop).

import Base
import ../../bend/once.bend as O
import ../../laws/once.bend as Once

def Once.once_recover_evidence_first(again, m, p, s, q):
  match m:
    case O.Resume{}:
      ({==}, {==})
    case O.Stop{}:
      ({==}, {==})
