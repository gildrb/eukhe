# eukhe: the proof of LAW family_text_reason_names
#
# PROOF: the words before the values are the witness, one for every value;
# the reason text then computes to the stated end.

import Base
import ../../bend/family.bend as F
import ../../laws/family.bend as Family


def Family.family_text_reason_names():
  ("rlm.spawn task ", d => m => i => {==})
