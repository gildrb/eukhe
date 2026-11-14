# eukhe: lemmas the proofs of area once share: a finished effect took hold
#
# The invariant od.inv holds of the first world, every event keeps it
# for every policy (od.step; a keyed effect's verdict is a launch or an
# interrupt, LA.ob.dedup_cases), so it holds after every history
# (od.run); a world it holds of has a finished effect only when it took
# hold (od.out).

import Base
import ../../../bend/once.bend as O
import ../../../laws/once.bend as Once
import ../../../spec/once/life.bend as S
import ../base.bend as LA

# a launch in flight that took hold: the effect took hold
def od.flight(live: Bool, hit: Bool, k: Nat) -> Bool:
  match live:
    case True{}:
      match hit:
        case True{}:
          Nat.is_le(1n, k)
        case False{}:
          True{}
    case False{}:
      True{}

# the invariant: a finished effect took hold; so did one whose launch in
# flight took hold
def od.inv(w: S.World) -> Bool:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      match l:
        case O.Absent{}:
          od.flight(live, hit, k)
        case O.Pending{}:
          od.flight(live, hit, k)
        case O.Running{again}:
          od.flight(live, hit, k)
        case O.Ran{}:
          Nat.is_le(1n, k)
        case O.Unsure{}:
          od.flight(live, hit, k)
        case O.Void{}:
          od.flight(live, hit, k)

def od.step(e: S.Ev, live: Bool, hit: Bool, l: O.Life, k: Nat, n: Nat, d: Nat, x: Nat, p: O.Policy) -> {Bool.or(Bool.not(od.inv(S.Wd{l, live, hit, n, k, d, x})), od.inv(Once.wd_step(S.Wd{l, live, hit, n, k, d, x}, e, p))) == True{} : Bool}:
  match e:
    case S.Mean{}:
      match l:
        case O.Absent{}:
          LA.ob.self(od.inv(S.Wd{O.Absent{}, live, hit, n, k, d, x}))
        case O.Pending{}:
          LA.ob.self(od.inv(S.Wd{O.Pending{}, live, hit, n, k, d, x}))
        case O.Running{again}:
          LA.ob.self(od.inv(S.Wd{O.Running{again}, live, hit, n, k, d, x}))
        case O.Ran{}:
          LA.ob.self(od.inv(S.Wd{O.Ran{}, live, hit, n, k, d, x}))
        case O.Unsure{}:
          LA.ob.self(od.inv(S.Wd{O.Unsure{}, live, hit, n, k, d, x}))
        case O.Void{}:
          LA.ob.self(od.inv(S.Wd{O.Void{}, live, hit, n, k, d, x}))
    case S.Tick{m, look}:
      match m:
        case O.Resume{}:
          match look:
            case True{}:
              match live:
                case True{}:
                  LA.ob.self(od.inv(S.Wd{l, True{}, hit, n, k, d, x}))
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
                    case O.Unsure{}:
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
                  LA.ob.self(od.inv(S.Wd{l, True{}, hit, n, k, d, x}))
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
                          match p:
                            case O.Never{}:
                              {==}
                            case O.Safe{}:
                              {==}
                            case O.Keyed{dd, cap}:
                              LA.ob.dedup_cases(dd, cap, again, v => {Bool.or(Bool.not(od.inv(S.Wd{O.Running{again}, False{}, hit, n, 0n, d, x})), od.inv(Once.wd_answer(v, O.Running{again}, n, 0n, d, x))) == True{} : Bool}, {==}, {==})
                        case 1n:
                          match p:
                            case O.Never{}:
                              {==}
                            case O.Safe{}:
                              {==}
                            case O.Keyed{dd, cap}:
                              LA.ob.dedup_cases(dd, cap, again, v => {Bool.or(Bool.not(od.inv(S.Wd{O.Running{again}, False{}, hit, n, 1n, d, x})), od.inv(Once.wd_answer(v, O.Running{again}, n, 1n, d, x))) == True{} : Bool}, {==}, {==})
                        case 2n+qk:
                          match p:
                            case O.Never{}:
                              {==}
                            case O.Safe{}:
                              {==}
                            case O.Keyed{dd, cap}:
                              LA.ob.dedup_cases(dd, cap, again, v => {Bool.or(Bool.not(od.inv(S.Wd{O.Running{again}, False{}, hit, n, 2n+qk, d, x})), od.inv(Once.wd_answer(v, O.Running{again}, n, 2n+qk, d, x))) == True{} : Bool}, {==}, {==})
                    case O.Ran{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qk:
                          {==}
                    case O.Unsure{}:
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
                  LA.ob.self(od.inv(S.Wd{l, True{}, hit, n, k, d, x}))
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
                    case O.Unsure{}:
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
                  LA.ob.self(od.inv(S.Wd{l, True{}, hit, n, k, d, x}))
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
                    case O.Unsure{}:
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
              LA.ob.self(od.inv(S.Wd{l, True{}, True{}, n, k, d, x}))
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
                case O.Unsure{}:
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
          LA.ob.self(od.inv(S.Wd{l, False{}, hit, n, k, d, x}))
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
                case O.Unsure{}:
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
                case O.Unsure{}:
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
          LA.ob.self(od.inv(S.Wd{l, False{}, hit, n, k, d, x}))
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
                case O.Unsure{}:
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
                case O.Unsure{}:
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
                case O.Unsure{}:
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
              LA.ob.self(od.inv(S.Wd{l, False{}, False{}, n, k, d, x}))

def od.stepw(w: S.World, e: S.Ev, p: O.Policy) -> {Bool.or(Bool.not(od.inv(w)), od.inv(Once.wd_step(w, e, p))) == True{} : Bool}:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      od.step(e, live, hit, l, k, n, d, x, p)

# the invariant holds after every history from a world it holds of
def od.run(es: List<&2, S.Ev>, +w: S.World, +p: O.Policy, h: {od.inv(w) == True{} : Bool}) -> {od.inv(Once.wd_run(es, w, p)) == True{} : Bool}:
  match es:
    case Nil{}:
      h
    case +e <> rest:
      od.run(rest, Once.wd_step(w, e, p), p, LA.ob.mp(od.inv(w), od.inv(Once.wd_step(w, e, p)), h, od.stepw(w, e, p)))

def od.out(live: Bool, hit: Bool, l: O.Life, k: Nat, n: Nat, d: Nat, x: Nat) -> {Bool.or(Bool.not(od.inv(S.Wd{l, live, hit, n, k, d, x})), Bool.or(Bool.not(S.is_ran(S.life(S.Wd{l, live, hit, n, k, d, x}))), Nat.is_le(1n, S.lands(S.Wd{l, live, hit, n, k, d, x})))) == True{} : Bool}:
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
            case O.Unsure{}:
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
            case O.Unsure{}:
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
            case O.Unsure{}:
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
            case O.Unsure{}:
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

def od.outw(w: S.World) -> {Bool.or(Bool.not(od.inv(w)), Bool.or(Bool.not(S.is_ran(S.life(w))), Nat.is_le(1n, S.lands(w)))) == True{} : Bool}:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      od.out(live, hit, l, k, n, d, x)
