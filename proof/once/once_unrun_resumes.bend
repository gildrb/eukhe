# eukhe: the proof of LAW once_unrun_resumes
#
# PROOF: of every world (so of every world a history reaches): only a
# pending effect with nothing in flight waits, and the restart's verdict
# for a pending effect whose run resumes is a launch, whatever the world
# shows and whatever its policy.

import Base
import ../../bend/once.bend as O
import ../../laws/once.bend as Once
import ../../spec/once/life.bend as S

def ou.all(w: S.World, -look: Bool, -p: O.Policy) -> {Bool.or(Bool.not(Once.wd_waits(w)), Once.wd_live(Once.wd_step(w, S.Tick{O.Resume{}, look}, p))) == True{} : Bool}:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      match l:
        case O.Absent{}:
          {==}
        case O.Pending{}:
          match live:
            case True{}:
              {==}
            case False{}:
              {==}
        case O.Running{again}:
          {==}
        case O.Ran{}:
          {==}
        case O.Unsure{}:
          {==}
        case O.Void{}:
          {==}

def Once.once_unrun_resumes(p, es, look):
  ou.all(Once.wd_run(es, S.w0(), p), look, p)
