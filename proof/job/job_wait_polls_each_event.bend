# eukhe: the proof of LAW job_wait_polls_each_event
# Per event and per budget left (none, or some): both sides compute; a
# tick spends one, so the budget after it is split once more.

import Base
import ../../bend/job.bend as Jb
import ../../laws/job.bend as Job

def Job.job_wait_polls_each_event(e, rest, left):
  match e:
    case Jb.Out{n}:
      match left:
        case 0n:
          {==}
        case 1n+l:
          {==}
    case Jb.Quit{c}:
      match left:
        case 0n:
          {==}
        case 1n+l:
          {==}
    case Jb.Kill{}:
      match left:
        case 0n:
          {==}
        case 1n+l:
          {==}
    case Jb.Tick{}:
      match left:
        case 0n:
          {==}
        case 1n+l:
          match l:
            case 0n:
              {==}
            case 1n+p:
              {==}
