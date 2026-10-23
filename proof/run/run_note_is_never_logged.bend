# eukhe: the proof of LAW run_note_is_never_logged

import Base
import ../../bend/run/request.bend as RnRequest
import ../../laws/run.bend as Run

# a note changes what the model reads, never what the run logs
def note_is_never_logged(q: RnRequest.Req) -> {RnRequest.logged(RnRequest.Req.lines(q)) == RnRequest.logged(RnRequest.Req.lines(RnRequest.Req{RnRequest.Req.ctx(q), 0n})) : List<&2, RnRequest.Line>}:
  match q:
    case RnRequest.Req{ctx, note}:
      match note:
        case 0n:
          {==}
        case 1n+k:
          {==}

def Run.run_note_is_never_logged(q):
  note_is_never_logged(q)
