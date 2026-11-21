# eukhe: the proof of LAW once_recover_pending_unrun
#
# PROOF: a pending life computes to a launch on a resume and to an
# abandon on a stop.

import Base
import ../../bend/once.bend as O
import ../../laws/once.bend as Once

def Once.once_recover_pending_unrun(s, p):
  ({==}, {==})
