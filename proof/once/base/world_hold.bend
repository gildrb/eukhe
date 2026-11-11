# eukhe: lemmas the proofs of area once share: a `never` effect takes hold at most once
#
# The invariant oa.inv holds of the first world, every event keeps it
# (oa.step, by cases: an event that leaves the world as it is keeps it
# by LA.ob.self, every other case computes), so it holds after every
# history (oa.run); a world it holds of took hold at most once (oa.out).

import Base
import ../../../bend/once.bend as O
import ../../../laws/once.bend as Once
import ../../../spec/once/life.bend as S
import ../base.bend as LA

# a running effect: in flight it took hold once exactly when this launch
# did; cut, it took hold at most once
def oa.flight(live: Bool, hit: Bool, k: Nat) -> Bool:
  match live:
    case True{}:
      match hit:
        case True{}:
          Nat.is_eq(k, 1n)
        case False{}:
          Nat.is_eq(k, 0n)
    case False{}:
      Nat.is_le(k, 1n)

# the invariant: an effect never launched never took hold and has no
# launch in flight; an ended one has none in flight and took hold at most
# once
def oa.inv(w: S.World) -> Bool:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      match l:
        case O.Absent{}:
          Bool.and(Bool.not(live), Nat.is_eq(k, 0n))
        case O.Pending{}:
          Bool.and(Bool.not(live), Nat.is_eq(k, 0n))
        case O.Running{again}:
          oa.flight(live, hit, k)
        case O.Ran{}:
          Bool.and(Bool.not(live), Nat.is_le(k, 1n))
        case O.Lost{}:
          Bool.and(Bool.not(live), Nat.is_le(k, 1n))
        case O.Void{}:
          Bool.and(Bool.not(live), Nat.is_le(k, 1n))

def oa.step(e: S.Ev, live: Bool, hit: Bool, l: O.Life, k: Nat, n: Nat, d: Nat, x: Nat) -> {Bool.or(Bool.not(oa.inv(S.Wd{l, live, hit, n, k, d, x})), oa.inv(Once.wd_step(S.Wd{l, live, hit, n, k, d, x}, e, O.Never{}))) == True{} : Bool}:
  match e:
    case S.Mean{}:
      match l:
        case O.Absent{}:
          LA.ob.self(oa.inv(S.Wd{O.Absent{}, live, hit, n, k, d, x}))
        case O.Pending{}:
          LA.ob.self(oa.inv(S.Wd{O.Pending{}, live, hit, n, k, d, x}))
        case O.Running{again}:
          LA.ob.self(oa.inv(S.Wd{O.Running{again}, live, hit, n, k, d, x}))
        case O.Ran{}:
          LA.ob.self(oa.inv(S.Wd{O.Ran{}, live, hit, n, k, d, x}))
        case O.Lost{}:
          LA.ob.self(oa.inv(S.Wd{O.Lost{}, live, hit, n, k, d, x}))
        case O.Void{}:
          LA.ob.self(oa.inv(S.Wd{O.Void{}, live, hit, n, k, d, x}))
    case S.Tick{m, look}:
      match m:
        case O.Resume{}:
          match look:
            case True{}:
              match live:
                case True{}:
                  LA.ob.self(oa.inv(S.Wd{l, True{}, hit, n, k, d, x}))
                case False{}:
                  match l:
                    case O.Absent{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qk:
                          {==}
                    case O.Pending{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qk:
                          {==}
                    case O.Running{again}:
                      match k:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qk:
                          {==}
                    case O.Ran{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qk:
                          {==}
                    case O.Lost{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qk:
                          {==}
                    case O.Void{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qk:
                          {==}
            case False{}:
              match live:
                case True{}:
                  LA.ob.self(oa.inv(S.Wd{l, True{}, hit, n, k, d, x}))
                case False{}:
                  match l:
                    case O.Absent{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qk:
                          {==}
                    case O.Pending{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qk:
                          {==}
                    case O.Running{again}:
                      match k:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qk:
                          {==}
                    case O.Ran{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qk:
                          {==}
                    case O.Lost{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qk:
                          {==}
                    case O.Void{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qk:
                          {==}
        case O.Stop{}:
          match look:
            case True{}:
              match live:
                case True{}:
                  LA.ob.self(oa.inv(S.Wd{l, True{}, hit, n, k, d, x}))
                case False{}:
                  match l:
                    case O.Absent{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qk:
                          {==}
                    case O.Pending{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qk:
                          {==}
                    case O.Running{again}:
                      match k:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qk:
                          {==}
                    case O.Ran{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qk:
                          {==}
                    case O.Lost{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qk:
                          {==}
                    case O.Void{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qk:
                          {==}
            case False{}:
              match live:
                case True{}:
                  LA.ob.self(oa.inv(S.Wd{l, True{}, hit, n, k, d, x}))
                case False{}:
                  match l:
                    case O.Absent{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qk:
                          {==}
                    case O.Pending{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qk:
                          {==}
                    case O.Running{again}:
                      match k:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qk:
                          {==}
                    case O.Ran{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qk:
                          {==}
                    case O.Lost{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qk:
                          {==}
                    case O.Void{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qk:
                          {==}
    case S.Land{}:
      match live:
        case True{}:
          match hit:
            case True{}:
              LA.ob.self(oa.inv(S.Wd{l, True{}, True{}, n, k, d, x}))
            case False{}:
              match l:
                case O.Absent{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
                case O.Pending{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
                case O.Running{again}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
                case O.Ran{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
                case O.Lost{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
                case O.Void{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
        case False{}:
          LA.ob.self(oa.inv(S.Wd{l, False{}, hit, n, k, d, x}))
    case S.End{}:
      match live:
        case True{}:
          match hit:
            case True{}:
              match l:
                case O.Absent{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
                case O.Pending{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
                case O.Running{again}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
                case O.Ran{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
                case O.Lost{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
                case O.Void{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
            case False{}:
              match l:
                case O.Absent{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
                case O.Pending{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
                case O.Running{again}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
                case O.Ran{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
                case O.Lost{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
                case O.Void{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
        case False{}:
          LA.ob.self(oa.inv(S.Wd{l, False{}, hit, n, k, d, x}))
    case S.Crash{}:
      match live:
        case True{}:
          match hit:
            case True{}:
              match l:
                case O.Absent{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
                case O.Pending{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
                case O.Running{again}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
                case O.Ran{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
                case O.Lost{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
                case O.Void{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
            case False{}:
              match l:
                case O.Absent{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
                case O.Pending{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
                case O.Running{again}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
                case O.Ran{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
                case O.Lost{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
                case O.Void{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
        case False{}:
          match hit:
            case True{}:
              match l:
                case O.Absent{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
                case O.Pending{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
                case O.Running{again}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
                case O.Ran{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
                case O.Lost{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
                case O.Void{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qk:
                      {==}
            case False{}:
              LA.ob.self(oa.inv(S.Wd{l, False{}, False{}, n, k, d, x}))

def oa.stepw(w: S.World, e: S.Ev) -> {Bool.or(Bool.not(oa.inv(w)), oa.inv(Once.wd_step(w, e, O.Never{}))) == True{} : Bool}:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      oa.step(e, live, hit, l, k, n, d, x)

# the invariant holds after every history from a world it holds of
def oa.run(es: List<&2, S.Ev>, +w: S.World, h: {oa.inv(w) == True{} : Bool}) -> {oa.inv(Once.wd_run(es, w, O.Never{})) == True{} : Bool}:
  match es:
    case Nil{}:
      h
    case +e <> rest:
      oa.run(rest, Once.wd_step(w, e, O.Never{}), LA.ob.mp(oa.inv(w), oa.inv(Once.wd_step(w, e, O.Never{})), h, oa.stepw(w, e)))

def oa.out(live: Bool, hit: Bool, l: O.Life, k: Nat, n: Nat, d: Nat, x: Nat) -> {Bool.or(Bool.not(oa.inv(S.Wd{l, live, hit, n, k, d, x})), Nat.is_le(S.lands(S.Wd{l, live, hit, n, k, d, x}), 1n)) == True{} : Bool}:
  match live:
    case True{}:
      match hit:
        case True{}:
          match l:
            case O.Absent{}:
              match k:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qk:
                  {==}
            case O.Pending{}:
              match k:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qk:
                  {==}
            case O.Running{again}:
              match k:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qk:
                  {==}
            case O.Ran{}:
              match k:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qk:
                  {==}
            case O.Lost{}:
              match k:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qk:
                  {==}
            case O.Void{}:
              match k:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qk:
                  {==}
        case False{}:
          match l:
            case O.Absent{}:
              match k:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qk:
                  {==}
            case O.Pending{}:
              match k:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qk:
                  {==}
            case O.Running{again}:
              match k:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qk:
                  {==}
            case O.Ran{}:
              match k:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qk:
                  {==}
            case O.Lost{}:
              match k:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qk:
                  {==}
            case O.Void{}:
              match k:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qk:
                  {==}
    case False{}:
      match hit:
        case True{}:
          match l:
            case O.Absent{}:
              match k:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qk:
                  {==}
            case O.Pending{}:
              match k:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qk:
                  {==}
            case O.Running{again}:
              match k:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qk:
                  {==}
            case O.Ran{}:
              match k:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qk:
                  {==}
            case O.Lost{}:
              match k:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qk:
                  {==}
            case O.Void{}:
              match k:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qk:
                  {==}
        case False{}:
          match l:
            case O.Absent{}:
              match k:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qk:
                  {==}
            case O.Pending{}:
              match k:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qk:
                  {==}
            case O.Running{again}:
              match k:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qk:
                  {==}
            case O.Ran{}:
              match k:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qk:
                  {==}
            case O.Lost{}:
              match k:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qk:
                  {==}
            case O.Void{}:
              match k:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qk:
                  {==}

def oa.outw(w: S.World) -> {Bool.or(Bool.not(oa.inv(w)), Nat.is_le(S.lands(w), 1n)) == True{} : Bool}:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      oa.out(live, hit, l, k, n, d, x)
