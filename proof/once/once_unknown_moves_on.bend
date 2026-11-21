# eukhe: the proof of LAW once_unknown_moves_on
#
# PROOF: of every world (so of every world a history reaches): with a
# launch in flight a resume keeps it; with none, a resume skips or
# settles only an effect with no record or an end on record, launches a
# pending one, and for a started one adopts, launches or journals
# unknown: a keyed one's verdict is a launch or an interrupt
# (LA.ob.dedup_cases).

import Base
import ../../bend/once.bend as O
import ../../laws/once.bend as Once
import ../../spec/once/life.bend as S
import ./base.bend as LA

# a started effect nothing can be asked about, its run resumed: launched
# or journaled unknown, whatever its policy
def mo.dark(again: Nat, p: O.Policy, n: Nat, k: Nat, d: Nat, x: Nat) -> {Bool.or(Once.wd_live(Once.wd_answer(O.recover(O.Running{again}, O.Dark{}, O.Resume{}, p), O.Running{again}, n, k, d, x)), Once.wd_closed(Once.wd_answer(O.recover(O.Running{again}, O.Dark{}, O.Resume{}, p), O.Running{again}, n, k, d, x))) == True{} : Bool}:
  match p:
    case O.Never{}:
      {==}
    case O.Safe{}:
      {==}
    case O.Keyed{dd, cap}:
      LA.ob.dedup_cases(dd, cap, again, v => {Bool.or(Once.wd_live(Once.wd_answer(v, O.Running{again}, n, k, d, x)), Once.wd_closed(Once.wd_answer(v, O.Running{again}, n, k, d, x))) == True{} : Bool}, {==}, {==})

def mo.all(w: S.World, look: Bool, p: O.Policy) -> {Bool.or(Once.wd_live(Once.wd_step(w, S.Tick{O.Resume{}, look}, p)), Once.wd_closed(Once.wd_step(w, S.Tick{O.Resume{}, look}, p))) == True{} : Bool}:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      match l:
        case O.Absent{}:
          match live:
            case True{}:
              {==}
            case False{}:
              {==}
        case O.Pending{}:
          match live:
            case True{}:
              {==}
            case False{}:
              {==}
        case O.Running{again}:
          match live:
            case True{}:
              {==}
            case False{}:
              match k:
                case 0n:
                  match look:
                    case True{}:
                      {==}
                    case False{}:
                      mo.dark(again, p, n, 0n, d, x)
                case 1n+j:
                  match look:
                    case True{}:
                      {==}
                    case False{}:
                      mo.dark(again, p, n, 1n+j, d, x)
        case O.Ran{}:
          match live:
            case True{}:
              {==}
            case False{}:
              {==}
        case O.Unsure{}:
          match live:
            case True{}:
              {==}
            case False{}:
              {==}
        case O.Void{}:
          match live:
            case True{}:
              {==}
            case False{}:
              {==}

def Once.once_unknown_moves_on(p, es, look):
  mo.all(Once.wd_run(es, S.w0(), p), look, p)
