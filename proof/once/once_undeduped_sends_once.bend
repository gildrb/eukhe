# eukhe: the proof of LAW once_undeduped_sends_once
#
# PROOF: a keyed effect whose target does not drop every repeat of its key
# gets the verdict of a `never` effect at every restart (ou.same), so every
# event moves its world as a `never` effect's (ou.step) and every history
# leaves the same world (ou.run); a `never` effect the world is never
# asked about is launched at most once (once_never_launches_twice).

import Base
import ../../bend/once.bend as O
import ../../laws/once.bend as Once
import ../../spec/once/life.bend as S
import ./base.bend as LA
import ./once_never_launches_twice.bend as POnceNeverLaunchesTwice

# at every restart the verdict of a `never` effect
def ou.same(l: O.Life, s: O.Seen, m: O.Mode, d: O.Dedup, -cap: Nat, no: {S.lasting(d) == False{} : Bool}) -> {O.recover(l, s, m, O.Never{}) == O.recover(l, s, m, O.Keyed{d, cap}) : O.Verdict}:
  match l:
    case O.Absent{}:
      {==}
    case O.Pending{}:
      {==}
    case O.Running{again}:
      match s:
        case O.Dark{}:
          match m:
            case O.Resume{}:
              match d:
                case O.Undeclared{}:
                  {==}
                case O.Lasting{}:
                  LA.ob.true_false({O.Interrupt{} == O.dedup(O.Lasting{}, cap, again) : O.Verdict}, no)
            case O.Stop{}:
              {==}
        case O.Landed{}:
          {==}
        case O.Clean{}:
          {==}
    case O.Ran{}:
      {==}
    case O.Unsure{}:
      {==}
    case O.Void{}:
      {==}

# every event moves the world as a `never` effect's
def ou.step(e: S.Ev, w: S.World, d: O.Dedup, -cap: Nat, no: {S.lasting(d) == False{} : Bool}) -> {Once.wd_step(w, e, O.Never{}) == Once.wd_step(w, e, O.Keyed{d, cap}) : S.World}:
  match e:
    case S.Mean{}:
      match w:
        case S.Wd{l, live, hit, n, k, x1, x2}:
          {==}
    case S.Tick{+m, +look}:
      match w:
        case S.Wd{+l, live, hit, n, +k, x1, x2}:
          match live:
            case True{}:
              {==}
            case False{}:
              %ou.same(l, S.seen(look, k), m, d, cap, no) : {Once.wd_answer(O.recover(l, S.seen(look, k), m, O.Never{}), l, n, k, x1, x2) == Once.wd_answer(_, l, n, k, x1, x2) : S.World}
              {==}
    case S.Land{}:
      match w:
        case S.Wd{l, live, hit, n, k, x1, x2}:
          {==}
    case S.End{}:
      match w:
        case S.Wd{l, live, hit, n, k, x1, x2}:
          {==}
    case S.Crash{}:
      match w:
        case S.Wd{l, live, hit, n, k, x1, x2}:
          {==}

# every history leaves the world a `never` effect's leaves
def ou.run(es: List<&2, S.Ev>, +w: S.World, +d: O.Dedup, +cap: Nat, +no: {S.lasting(d) == False{} : Bool}) -> {Once.wd_run(es, w, O.Never{}) == Once.wd_run(es, w, O.Keyed{d, cap}) : S.World}:
  match es:
    case Nil{}:
      {==}
    case +e <> rest:
      %ou.step(e, w, d, cap, no) : {Once.wd_run(rest, Once.wd_step(w, e, O.Never{}), O.Never{}) == Once.wd_run(rest, _, O.Keyed{d, cap}) : S.World}
      ou.run(rest, Once.wd_step(w, e, O.Never{}), d, cap, no)

def Once.once_undeduped_sends_once(d, no, cap, es):
  %ou.run(S.dim(es), S.w0(), d, cap, no) : {Nat.is_le(S.launches(_), 1n) == True{} : Bool}
  Once.once_never_launches_twice(es)
