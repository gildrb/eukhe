# eukhe: the proof of LAW run_note_is_never_logged

import Base
import ../../bend/run.bend as Rn
import ../../LAWS.bend as Laws

# a note changes what the model reads, never what the run logs
def note_is_never_logged(q: Rn.Req) -> {Rn.logged(Rn.Req.lines(q)) == Rn.logged(Rn.Req.lines(Rn.Req{Rn.Req.ctx(q), 0n})) : List<&2, Rn.Line>}:
  match q:
    case Rn.Req{ctx, note}:
      match note:
        case 0n:
          {==}
        case 1n+k:
          {==}

def Laws.run_note_is_never_logged(q):
  note_is_never_logged(q)
