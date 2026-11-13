# eukhe: the proof of LAW once_stop_settles
#
# PROOF: of every world (so of every world a history reaches): with a
# launch in flight the claim holds by its first part; with none, a stop's
# verdict is one of skip (no record), abandon (unstarted journaled),
# adopt (finished journaled), interrupt (unknown journaled) or settled
# (an end already on record), whatever the policy and whatever the world
# shows: none launches, so the launches stay.

import Base
import ../../bend/once.bend as O
import ../../laws/once.bend as Once
import ../../spec/once/life.bend as S
import ../base/nat.bend as N

def ok.all(w: S.World, look: Bool, p: O.Policy) -> {Bool.or(Once.wd_live(w), Bool.and(Once.wd_closed(Once.wd_step(w, S.Tick{O.Stop{}, look}, p)), Bool.and(Bool.not(Once.wd_live(Once.wd_step(w, S.Tick{O.Stop{}, look}, p))), Nat.is_eq(S.launches(Once.wd_step(w, S.Tick{O.Stop{}, look}, p)), S.launches(w))))) == True{} : Bool}:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      match l:
        case O.Absent{}:
          match live:
            case True{}:
              {==}
            case False{}:
              N.cb_nat_refl(n)
        case O.Pending{}:
          match live:
            case True{}:
              {==}
            case False{}:
              N.cb_nat_refl(n)
        case O.Running{again}:
          match live:
            case True{}:
              {==}
            case False{}:
              match k:
                case 0n:
                  match look:
                    case True{}:
                      N.cb_nat_refl(n)
                    case False{}:
                      N.cb_nat_refl(n)
                case 1n+j:
                  match look:
                    case True{}:
                      N.cb_nat_refl(n)
                    case False{}:
                      N.cb_nat_refl(n)
        case O.Ran{}:
          match live:
            case True{}:
              {==}
            case False{}:
              N.cb_nat_refl(n)
        case O.Unsure{}:
          match live:
            case True{}:
              {==}
            case False{}:
              N.cb_nat_refl(n)
        case O.Void{}:
          match live:
            case True{}:
              {==}
            case False{}:
              N.cb_nat_refl(n)

def Once.once_stop_settles(p, es, look):
  ok.all(Once.wd_run(es, S.w0(), p), look, p)
