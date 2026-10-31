# eukhe: the proof of LAW rlm_query_text_spec
#
# PROOF: case analysis on the refusal; each text is the spec's text.

import Base
import ../../bend/rlm_query.bend as Rq
import ../../laws/rlm_query.bend as RlmQuery


def RlmQuery.rlm_query_text_spec(f):
  match f:
    case Rq.OverBudget{t, l, b}:
      {==}
    case Rq.Full{c}:
      {==}
