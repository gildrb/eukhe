# eukhe: the proof of LAW run_context_is_logged
#
# PROOF: by cases on the note; the lines of a request and what the run
# logs of them compute.

import Base
import ../../bend/run/request.bend as RnRequest
import ../../laws/run/model.bend as Run

def Run.run_context_is_logged(ctx, note):
  match note:
    case 0n:
      {==}
    case 1n+k:
      {==}
