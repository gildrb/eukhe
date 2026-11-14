# eukhe: lemmas the proofs of area once share: an effect ends once
#
# The invariant on.inv holds of the first world, every event keeps it
# for every policy (on.step), so it holds after every history (on.run);
# a world it holds of journaled at most one end (on.out).

import Base
import ../../../bend/once.bend as O
import ../../../laws/once.bend as Once
import ../../../spec/once/life.bend as S
import ../base.bend as LA

# the invariant: an effect not ended has no end journaled; an ended one
# has one at most and no launch in flight
def on.inv(w: S.World) -> Bool:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      match l:
        case O.Absent{}:
          Nat.is_eq(d, 0n)
        case O.Pending{}:
          Nat.is_eq(d, 0n)
        case O.Running{again}:
          Nat.is_eq(d, 0n)
        case O.Ran{}:
          Bool.and(Bool.not(live), Nat.is_le(d, 1n))
        case O.Unsure{}:
          Bool.and(Bool.not(live), Nat.is_le(d, 1n))
        case O.Void{}:
          Bool.and(Bool.not(live), Nat.is_le(d, 1n))

def on.step(e: S.Ev, live: Bool, hit: Bool, l: O.Life, d: Nat, k: Nat, n: Nat, x: Nat, p: O.Policy) -> {Bool.or(Bool.not(on.inv(S.Wd{l, live, hit, n, k, d, x})), on.inv(Once.wd_step(S.Wd{l, live, hit, n, k, d, x}, e, p))) == True{} : Bool}:
  match e:
    case S.Mean{}:
      match l:
        case O.Absent{}:
          LA.ob.self(on.inv(S.Wd{O.Absent{}, live, hit, n, k, d, x}))
        case O.Pending{}:
          LA.ob.self(on.inv(S.Wd{O.Pending{}, live, hit, n, k, d, x}))
        case O.Running{again}:
          LA.ob.self(on.inv(S.Wd{O.Running{again}, live, hit, n, k, d, x}))
        case O.Ran{}:
          LA.ob.self(on.inv(S.Wd{O.Ran{}, live, hit, n, k, d, x}))
        case O.Unsure{}:
          LA.ob.self(on.inv(S.Wd{O.Unsure{}, live, hit, n, k, d, x}))
        case O.Void{}:
          LA.ob.self(on.inv(S.Wd{O.Void{}, live, hit, n, k, d, x}))
    case S.Tick{m, look}:
      match m:
        case O.Resume{}:
          match look:
            case True{}:
              match live:
                case True{}:
                  LA.ob.self(on.inv(S.Wd{l, True{}, hit, n, k, d, x}))
                case False{}:
                  match l:
                    case O.Absent{}:
                      match d:
                        case 0n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 1n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 2n+qd:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                    case O.Pending{}:
                      match d:
                        case 0n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 1n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 2n+qd:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                    case O.Running{again}:
                      match d:
                        case 0n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 1n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 2n+qd:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                    case O.Ran{}:
                      match d:
                        case 0n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 1n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 2n+qd:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                    case O.Unsure{}:
                      match d:
                        case 0n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 1n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 2n+qd:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                    case O.Void{}:
                      match d:
                        case 0n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 1n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 2n+qd:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
            case False{}:
              match live:
                case True{}:
                  LA.ob.self(on.inv(S.Wd{l, True{}, hit, n, k, d, x}))
                case False{}:
                  match l:
                    case O.Absent{}:
                      match d:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qd:
                          {==}
                    case O.Pending{}:
                      match d:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qd:
                          {==}
                    case O.Running{again}:
                      match d:
                        case 0n:
                          match p:
                            case O.Never{}:
                              {==}
                            case O.Safe{}:
                              {==}
                            case O.Keyed{dd, cap}:
                              LA.ob.dedup_cases(dd, cap, again, v => {Bool.or(Bool.not(on.inv(S.Wd{O.Running{again}, False{}, hit, n, k, 0n, x})), on.inv(Once.wd_answer(v, O.Running{again}, n, k, 0n, x))) == True{} : Bool}, {==}, {==})
                        case 1n:
                          match p:
                            case O.Never{}:
                              {==}
                            case O.Safe{}:
                              {==}
                            case O.Keyed{dd, cap}:
                              LA.ob.dedup_cases(dd, cap, again, v => {Bool.or(Bool.not(on.inv(S.Wd{O.Running{again}, False{}, hit, n, k, 1n, x})), on.inv(Once.wd_answer(v, O.Running{again}, n, k, 1n, x))) == True{} : Bool}, {==}, {==})
                        case 2n+qd:
                          match p:
                            case O.Never{}:
                              {==}
                            case O.Safe{}:
                              {==}
                            case O.Keyed{dd, cap}:
                              LA.ob.dedup_cases(dd, cap, again, v => {Bool.or(Bool.not(on.inv(S.Wd{O.Running{again}, False{}, hit, n, k, 2n+qd, x})), on.inv(Once.wd_answer(v, O.Running{again}, n, k, 2n+qd, x))) == True{} : Bool}, {==}, {==})
                    case O.Ran{}:
                      match d:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qd:
                          {==}
                    case O.Unsure{}:
                      match d:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qd:
                          {==}
                    case O.Void{}:
                      match d:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qd:
                          {==}
        case O.Stop{}:
          match look:
            case True{}:
              match live:
                case True{}:
                  LA.ob.self(on.inv(S.Wd{l, True{}, hit, n, k, d, x}))
                case False{}:
                  match l:
                    case O.Absent{}:
                      match d:
                        case 0n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 1n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 2n+qd:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                    case O.Pending{}:
                      match d:
                        case 0n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 1n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 2n+qd:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                    case O.Running{again}:
                      match d:
                        case 0n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 1n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 2n+qd:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                    case O.Ran{}:
                      match d:
                        case 0n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 1n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 2n+qd:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                    case O.Unsure{}:
                      match d:
                        case 0n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 1n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 2n+qd:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                    case O.Void{}:
                      match d:
                        case 0n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 1n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 2n+qd:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
            case False{}:
              match live:
                case True{}:
                  LA.ob.self(on.inv(S.Wd{l, True{}, hit, n, k, d, x}))
                case False{}:
                  match l:
                    case O.Absent{}:
                      match d:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qd:
                          {==}
                    case O.Pending{}:
                      match d:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qd:
                          {==}
                    case O.Running{again}:
                      match d:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qd:
                          {==}
                    case O.Ran{}:
                      match d:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qd:
                          {==}
                    case O.Unsure{}:
                      match d:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qd:
                          {==}
                    case O.Void{}:
                      match d:
                        case 0n:
                          {==}
                        case 1n:
                          {==}
                        case 2n+qd:
                          {==}
    case S.Land{}:
      match live:
        case True{}:
          match hit:
            case True{}:
              LA.ob.self(on.inv(S.Wd{l, True{}, True{}, n, k, d, x}))
            case False{}:
              match l:
                case O.Absent{}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
                case O.Pending{}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
                case O.Running{again}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
                case O.Ran{}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
                case O.Unsure{}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
                case O.Void{}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
        case False{}:
          LA.ob.self(on.inv(S.Wd{l, False{}, hit, n, k, d, x}))
    case S.End{}:
      match live:
        case True{}:
          match hit:
            case True{}:
              match l:
                case O.Absent{}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
                case O.Pending{}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
                case O.Running{again}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
                case O.Ran{}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
                case O.Unsure{}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
                case O.Void{}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
            case False{}:
              match l:
                case O.Absent{}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
                case O.Pending{}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
                case O.Running{again}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
                case O.Ran{}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
                case O.Unsure{}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
                case O.Void{}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
        case False{}:
          LA.ob.self(on.inv(S.Wd{l, False{}, hit, n, k, d, x}))
    case S.Crash{}:
      match live:
        case True{}:
          match hit:
            case True{}:
              match l:
                case O.Absent{}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
                case O.Pending{}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
                case O.Running{again}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
                case O.Ran{}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
                case O.Unsure{}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
                case O.Void{}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
            case False{}:
              match l:
                case O.Absent{}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
                case O.Pending{}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
                case O.Running{again}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
                case O.Ran{}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
                case O.Unsure{}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
                case O.Void{}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
        case False{}:
          match hit:
            case True{}:
              match l:
                case O.Absent{}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
                case O.Pending{}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
                case O.Running{again}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
                case O.Ran{}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
                case O.Unsure{}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
                case O.Void{}:
                  match d:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qd:
                      {==}
            case False{}:
              LA.ob.self(on.inv(S.Wd{l, False{}, False{}, n, k, d, x}))

def on.stepw(w: S.World, e: S.Ev, p: O.Policy) -> {Bool.or(Bool.not(on.inv(w)), on.inv(Once.wd_step(w, e, p))) == True{} : Bool}:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      on.step(e, live, hit, l, d, k, n, x, p)

# the invariant holds after every history from a world it holds of
def on.run(es: List<&2, S.Ev>, +w: S.World, +p: O.Policy, h: {on.inv(w) == True{} : Bool}) -> {on.inv(Once.wd_run(es, w, p)) == True{} : Bool}:
  match es:
    case Nil{}:
      h
    case +e <> rest:
      on.run(rest, Once.wd_step(w, e, p), p, LA.ob.mp(on.inv(w), on.inv(Once.wd_step(w, e, p)), h, on.stepw(w, e, p)))

def on.out(live: Bool, hit: Bool, l: O.Life, d: Nat, k: Nat, n: Nat, x: Nat) -> {Bool.or(Bool.not(on.inv(S.Wd{l, live, hit, n, k, d, x})), Nat.is_le(S.ends(S.Wd{l, live, hit, n, k, d, x}), 1n)) == True{} : Bool}:
  match live:
    case True{}:
      match hit:
        case True{}:
          match l:
            case O.Absent{}:
              match d:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qd:
                  {==}
            case O.Pending{}:
              match d:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qd:
                  {==}
            case O.Running{again}:
              match d:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qd:
                  {==}
            case O.Ran{}:
              match d:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qd:
                  {==}
            case O.Unsure{}:
              match d:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qd:
                  {==}
            case O.Void{}:
              match d:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qd:
                  {==}
        case False{}:
          match l:
            case O.Absent{}:
              match d:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qd:
                  {==}
            case O.Pending{}:
              match d:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qd:
                  {==}
            case O.Running{again}:
              match d:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qd:
                  {==}
            case O.Ran{}:
              match d:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qd:
                  {==}
            case O.Unsure{}:
              match d:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qd:
                  {==}
            case O.Void{}:
              match d:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qd:
                  {==}
    case False{}:
      match hit:
        case True{}:
          match l:
            case O.Absent{}:
              match d:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qd:
                  {==}
            case O.Pending{}:
              match d:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qd:
                  {==}
            case O.Running{again}:
              match d:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qd:
                  {==}
            case O.Ran{}:
              match d:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qd:
                  {==}
            case O.Unsure{}:
              match d:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qd:
                  {==}
            case O.Void{}:
              match d:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qd:
                  {==}
        case False{}:
          match l:
            case O.Absent{}:
              match d:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qd:
                  {==}
            case O.Pending{}:
              match d:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qd:
                  {==}
            case O.Running{again}:
              match d:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qd:
                  {==}
            case O.Ran{}:
              match d:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qd:
                  {==}
            case O.Unsure{}:
              match d:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qd:
                  {==}
            case O.Void{}:
              match d:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qd:
                  {==}

def on.outw(w: S.World) -> {Bool.or(Bool.not(on.inv(w)), Nat.is_le(S.ends(w), 1n)) == True{} : Bool}:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      on.out(live, hit, l, d, k, n, x)
