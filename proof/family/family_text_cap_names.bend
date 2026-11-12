# eukhe: the proof of LAW family_text_cap_names
#
# PROOF: the words before the values are the witness, one for every value;
# the cap text then computes to the stated end.

import Base
import ../../bend/family.bend as F
import ../../laws/family.bend as Family


def Family.family_text_cap_names():
  ("subagent concurrency limit ", d => m => c => {==})
