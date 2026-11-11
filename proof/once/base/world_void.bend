# eukhe: lemmas the proofs of area once share: an effect reported not started never took hold
#
# The invariant ov.inv holds of the first world, every event keeps it
# for every policy (ov.step), so it holds after every history (ov.run);
# a world it holds of has an effect reported not started only when it
# never took hold (ov.out).

import Base
import ../../../bend/once.bend as O
import ../../../laws/once.bend as Once
import ../../../spec/once/life.bend as S
import ../base.bend as LA

# the invariant: an effect never launched, and one reported not started,
# never took hold and has no launch in flight
def ov.inv(w: S.World) -> Bool:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      match l:
        case O.Absent{}:
          Bool.and(Bool.not(live), Nat.is_eq(k, 0n))
        case O.Pending{}:
          Bool.and(Bool.not(live), Nat.is_eq(k, 0n))
        case O.Running{again}:
          True{}
        case O.Ran{}:
          True{}
        case O.Lost{}:
          True{}
        case O.Void{}:
          Bool.and(Bool.not(live), Nat.is_eq(k, 0n))

def ov.step(e: S.Ev, live: Bool, hit: Bool, l: O.Life, k: Nat, n: Nat, d: Nat, x: Nat, p: O.Policy) -> {Bool.or(Bool.not(ov.inv(S.Wd{l, live, hit, n, k, d, x})), ov.inv(Once.wd_step(S.Wd{l, live, hit, n, k, d, x}, e, p))) == True{} : Bool}:
  match e:
    case S.Mean{}:
      match l:
        case O.Absent{}:
          LA.ob.self(ov.inv(S.Wd{O.Absent{}, live, hit, n, k, d, x}))
        case O.Pending{}:
          LA.ob.self(ov.inv(S.Wd{O.Pending{}, live, hit, n, k, d, x}))
        case O.Running{again}:
          LA.ob.self(ov.inv(S.Wd{O.Running{again}, live, hit, n, k, d, x}))
        case O.Ran{}:
          LA.ob.self(ov.inv(S.Wd{O.Ran{}, live, hit, n, k, d, x}))
        case O.Lost{}:
          LA.ob.self(ov.inv(S.Wd{O.Lost{}, live, hit, n, k, d, x}))
        case O.Void{}:
          LA.ob.self(ov.inv(S.Wd{O.Void{}, live, hit, n, k, d, x}))
    case S.Tick{m, look}:
      match m:
        case O.Resume{}:
          match look:
            case True{}:
              match live:
                case True{}:
                  LA.ob.self(ov.inv(S.Wd{l, True{}, hit, n, k, d, x}))
                case False{}:
                  match l:
                    case O.Absent{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n+qk:
                          {==}
                    case O.Pending{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n+qk:
                          {==}
                    case O.Running{again}:
                      match k:
                        case 0n:
                          {==}
                        case 1n+qk:
                          {==}
                    case O.Ran{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n+qk:
                          {==}
                    case O.Lost{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n+qk:
                          {==}
                    case O.Void{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n+qk:
                          {==}
            case False{}:
              match live:
                case True{}:
                  LA.ob.self(ov.inv(S.Wd{l, True{}, hit, n, k, d, x}))
                case False{}:
                  match l:
                    case O.Absent{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n+qk:
                          {==}
                    case O.Pending{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n+qk:
                          {==}
                    case O.Running{again}:
                      match k:
                        case 0n:
                          match p:
                            case O.Never{}:
                              {==}
                            case O.Safe{}:
                              {==}
                            case O.Keyed{cap}:
                              LA.ob.keyed_cases(cap, again, v => {Bool.or(Bool.not(ov.inv(S.Wd{O.Running{again}, False{}, hit, n, 0n, d, x})), ov.inv(Once.wd_answer(v, O.Running{again}, n, 0n, d, x))) == True{} : Bool}, {==}, {==})
                        case 1n+qk:
                          match p:
                            case O.Never{}:
                              {==}
                            case O.Safe{}:
                              {==}
                            case O.Keyed{cap}:
                              LA.ob.keyed_cases(cap, again, v => {Bool.or(Bool.not(ov.inv(S.Wd{O.Running{again}, False{}, hit, n, 1n+qk, d, x})), ov.inv(Once.wd_answer(v, O.Running{again}, n, 1n+qk, d, x))) == True{} : Bool}, {==}, {==})
                    case O.Ran{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n+qk:
                          {==}
                    case O.Lost{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n+qk:
                          {==}
                    case O.Void{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n+qk:
                          {==}
        case O.Stop{}:
          match look:
            case True{}:
              match live:
                case True{}:
                  LA.ob.self(ov.inv(S.Wd{l, True{}, hit, n, k, d, x}))
                case False{}:
                  match l:
                    case O.Absent{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n+qk:
                          {==}
                    case O.Pending{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n+qk:
                          {==}
                    case O.Running{again}:
                      match k:
                        case 0n:
                          {==}
                        case 1n+qk:
                          {==}
                    case O.Ran{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n+qk:
                          {==}
                    case O.Lost{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n+qk:
                          {==}
                    case O.Void{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n+qk:
                          {==}
            case False{}:
              match live:
                case True{}:
                  LA.ob.self(ov.inv(S.Wd{l, True{}, hit, n, k, d, x}))
                case False{}:
                  match l:
                    case O.Absent{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n+qk:
                          {==}
                    case O.Pending{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n+qk:
                          {==}
                    case O.Running{again}:
                      match k:
                        case 0n:
                          {==}
                        case 1n+qk:
                          {==}
                    case O.Ran{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n+qk:
                          {==}
                    case O.Lost{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n+qk:
                          {==}
                    case O.Void{}:
                      match k:
                        case 0n:
                          {==}
                        case 1n+qk:
                          {==}
    case S.Land{}:
      match live:
        case True{}:
          match hit:
            case True{}:
              LA.ob.self(ov.inv(S.Wd{l, True{}, True{}, n, k, d, x}))
            case False{}:
              match l:
                case O.Absent{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
                case O.Pending{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
                case O.Running{again}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
                case O.Ran{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
                case O.Lost{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
                case O.Void{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
        case False{}:
          LA.ob.self(ov.inv(S.Wd{l, False{}, hit, n, k, d, x}))
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
                    case 1n+qk:
                      {==}
                case O.Pending{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
                case O.Running{again}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
                case O.Ran{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
                case O.Lost{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
                case O.Void{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
            case False{}:
              match l:
                case O.Absent{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
                case O.Pending{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
                case O.Running{again}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
                case O.Ran{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
                case O.Lost{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
                case O.Void{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
        case False{}:
          LA.ob.self(ov.inv(S.Wd{l, False{}, hit, n, k, d, x}))
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
                    case 1n+qk:
                      {==}
                case O.Pending{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
                case O.Running{again}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
                case O.Ran{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
                case O.Lost{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
                case O.Void{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
            case False{}:
              match l:
                case O.Absent{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
                case O.Pending{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
                case O.Running{again}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
                case O.Ran{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
                case O.Lost{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
                case O.Void{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
        case False{}:
          match hit:
            case True{}:
              match l:
                case O.Absent{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
                case O.Pending{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
                case O.Running{again}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
                case O.Ran{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
                case O.Lost{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
                case O.Void{}:
                  match k:
                    case 0n:
                      {==}
                    case 1n+qk:
                      {==}
            case False{}:
              LA.ob.self(ov.inv(S.Wd{l, False{}, False{}, n, k, d, x}))

def ov.stepw(w: S.World, e: S.Ev, p: O.Policy) -> {Bool.or(Bool.not(ov.inv(w)), ov.inv(Once.wd_step(w, e, p))) == True{} : Bool}:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      ov.step(e, live, hit, l, k, n, d, x, p)

# the invariant holds after every history from a world it holds of
def ov.run(es: List<&2, S.Ev>, +w: S.World, +p: O.Policy, h: {ov.inv(w) == True{} : Bool}) -> {ov.inv(Once.wd_run(es, w, p)) == True{} : Bool}:
  match es:
    case Nil{}:
      h
    case +e <> rest:
      ov.run(rest, Once.wd_step(w, e, p), p, LA.ob.mp(ov.inv(w), ov.inv(Once.wd_step(w, e, p)), h, ov.stepw(w, e, p)))

def ov.out(live: Bool, hit: Bool, l: O.Life, k: Nat, n: Nat, d: Nat, x: Nat) -> {Bool.or(Bool.not(ov.inv(S.Wd{l, live, hit, n, k, d, x})), Bool.or(Bool.not(S.is_void(S.life(S.Wd{l, live, hit, n, k, d, x}))), Nat.is_eq(S.lands(S.Wd{l, live, hit, n, k, d, x}), 0n))) == True{} : Bool}:
  match live:
    case True{}:
      match hit:
        case True{}:
          match l:
            case O.Absent{}:
              match k:
                case 0n:
                  {==}
                case 1n+qk:
                  {==}
            case O.Pending{}:
              match k:
                case 0n:
                  {==}
                case 1n+qk:
                  {==}
            case O.Running{again}:
              match k:
                case 0n:
                  {==}
                case 1n+qk:
                  {==}
            case O.Ran{}:
              match k:
                case 0n:
                  {==}
                case 1n+qk:
                  {==}
            case O.Lost{}:
              match k:
                case 0n:
                  {==}
                case 1n+qk:
                  {==}
            case O.Void{}:
              match k:
                case 0n:
                  {==}
                case 1n+qk:
                  {==}
        case False{}:
          match l:
            case O.Absent{}:
              match k:
                case 0n:
                  {==}
                case 1n+qk:
                  {==}
            case O.Pending{}:
              match k:
                case 0n:
                  {==}
                case 1n+qk:
                  {==}
            case O.Running{again}:
              match k:
                case 0n:
                  {==}
                case 1n+qk:
                  {==}
            case O.Ran{}:
              match k:
                case 0n:
                  {==}
                case 1n+qk:
                  {==}
            case O.Lost{}:
              match k:
                case 0n:
                  {==}
                case 1n+qk:
                  {==}
            case O.Void{}:
              match k:
                case 0n:
                  {==}
                case 1n+qk:
                  {==}
    case False{}:
      match hit:
        case True{}:
          match l:
            case O.Absent{}:
              match k:
                case 0n:
                  {==}
                case 1n+qk:
                  {==}
            case O.Pending{}:
              match k:
                case 0n:
                  {==}
                case 1n+qk:
                  {==}
            case O.Running{again}:
              match k:
                case 0n:
                  {==}
                case 1n+qk:
                  {==}
            case O.Ran{}:
              match k:
                case 0n:
                  {==}
                case 1n+qk:
                  {==}
            case O.Lost{}:
              match k:
                case 0n:
                  {==}
                case 1n+qk:
                  {==}
            case O.Void{}:
              match k:
                case 0n:
                  {==}
                case 1n+qk:
                  {==}
        case False{}:
          match l:
            case O.Absent{}:
              match k:
                case 0n:
                  {==}
                case 1n+qk:
                  {==}
            case O.Pending{}:
              match k:
                case 0n:
                  {==}
                case 1n+qk:
                  {==}
            case O.Running{again}:
              match k:
                case 0n:
                  {==}
                case 1n+qk:
                  {==}
            case O.Ran{}:
              match k:
                case 0n:
                  {==}
                case 1n+qk:
                  {==}
            case O.Lost{}:
              match k:
                case 0n:
                  {==}
                case 1n+qk:
                  {==}
            case O.Void{}:
              match k:
                case 0n:
                  {==}
                case 1n+qk:
                  {==}

def ov.outw(w: S.World) -> {Bool.or(Bool.not(ov.inv(w)), Bool.or(Bool.not(S.is_void(S.life(w))), Nat.is_eq(S.lands(w), 0n))) == True{} : Bool}:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      ov.out(live, hit, l, k, n, d, x)
