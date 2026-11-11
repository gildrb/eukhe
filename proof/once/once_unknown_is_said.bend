# eukhe: the proof of LAW once_unknown_is_said
#
# PROOF: of every world (so of every world a history reaches): only a
# started effect with no end and nothing in flight was cut, and the
# restart's verdict for it, the world not asked and its policy `never`,
# is an interrupt in both modes: unknown is journaled, nothing launches.

import Base
import ../../bend/once.bend as O
import ../../laws/once.bend as Once
import ../../spec/once/life.bend as S

def ok.all(w: S.World, m: O.Mode) -> {Bool.or(Bool.not(Once.wd_cut(w)), Bool.and(Once.wd_lost(Once.wd_step(w, S.Tick{m, False{}}, O.Never{})), Bool.not(Once.wd_live(Once.wd_step(w, S.Tick{m, False{}}, O.Never{}))))) == True{} : Bool}:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      match l:
        case O.Absent{}:
          {==}
        case O.Pending{}:
          {==}
        case O.Running{again}:
          match live:
            case True{}:
              {==}
            case False{}:
              match m:
                case O.Resume{}:
                  {==}
                case O.Stop{}:
                  {==}
        case O.Ran{}:
          {==}
        case O.Lost{}:
          {==}
        case O.Void{}:
          {==}

def Once.once_unknown_is_said(es, m):
  ok.all(Once.wd_run(es, S.w0(), O.Never{}), m)
