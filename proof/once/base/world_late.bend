# eukhe: lemmas the proofs of area once share: an ended effect is never launched
#
# The invariant ot.inv holds of the first world, every event keeps it
# for every policy (ot.step), so it holds after every history (ot.run);
# a world it holds of made no launch of an ended effect (ot.out).

import Base
import ../../../bend/once.bend as O
import ../../../laws/once.bend as Once
import ../../../spec/once/life.bend as S
import ../base.bend as LA

# the invariant: no launch was made of an ended effect, and an ended
# effect has no launch in flight
def ot.inv(w: S.World) -> Bool:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      match l:
        case O.Absent{}:
          Nat.is_eq(x, 0n)
        case O.Pending{}:
          Nat.is_eq(x, 0n)
        case O.Running{again}:
          Nat.is_eq(x, 0n)
        case O.Ran{}:
          Bool.and(Bool.not(live), Nat.is_eq(x, 0n))
        case O.Unsure{}:
          Bool.and(Bool.not(live), Nat.is_eq(x, 0n))
        case O.Void{}:
          Bool.and(Bool.not(live), Nat.is_eq(x, 0n))

def ot.step(e: S.Ev, live: Bool, hit: Bool, l: O.Life, x: Nat, k: Nat, n: Nat, d: Nat, p: O.Policy) -> {Bool.or(Bool.not(ot.inv(S.Wd{l, live, hit, n, k, d, x})), ot.inv(Once.wd_step(S.Wd{l, live, hit, n, k, d, x}, e, p))) == True{} : Bool}:
  match e:
    case S.Mean{}:
      match l:
        case O.Absent{}:
          LA.ob.self(ot.inv(S.Wd{O.Absent{}, live, hit, n, k, d, x}))
        case O.Pending{}:
          LA.ob.self(ot.inv(S.Wd{O.Pending{}, live, hit, n, k, d, x}))
        case O.Running{again}:
          LA.ob.self(ot.inv(S.Wd{O.Running{again}, live, hit, n, k, d, x}))
        case O.Ran{}:
          LA.ob.self(ot.inv(S.Wd{O.Ran{}, live, hit, n, k, d, x}))
        case O.Unsure{}:
          LA.ob.self(ot.inv(S.Wd{O.Unsure{}, live, hit, n, k, d, x}))
        case O.Void{}:
          LA.ob.self(ot.inv(S.Wd{O.Void{}, live, hit, n, k, d, x}))
    case S.Tick{m, look}:
      match m:
        case O.Resume{}:
          match look:
            case True{}:
              match live:
                case True{}:
                  LA.ob.self(ot.inv(S.Wd{l, True{}, hit, n, k, d, x}))
                case False{}:
                  match l:
                    case O.Absent{}:
                      match x:
                        case 0n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 1n+qx:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                    case O.Pending{}:
                      match x:
                        case 0n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 1n+qx:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                    case O.Running{again}:
                      match x:
                        case 0n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 1n+qx:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                    case O.Ran{}:
                      match x:
                        case 0n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 1n+qx:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                    case O.Unsure{}:
                      match x:
                        case 0n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 1n+qx:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                    case O.Void{}:
                      match x:
                        case 0n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 1n+qx:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
            case False{}:
              match live:
                case True{}:
                  LA.ob.self(ot.inv(S.Wd{l, True{}, hit, n, k, d, x}))
                case False{}:
                  match l:
                    case O.Absent{}:
                      match x:
                        case 0n:
                          {==}
                        case 1n+qx:
                          {==}
                    case O.Pending{}:
                      match x:
                        case 0n:
                          {==}
                        case 1n+qx:
                          {==}
                    case O.Running{again}:
                      match x:
                        case 0n:
                          match p:
                            case O.Never{}:
                              {==}
                            case O.Safe{}:
                              {==}
                            case O.Keyed{cap}:
                              LA.ob.keyed_cases(cap, again, v => {Bool.or(Bool.not(ot.inv(S.Wd{O.Running{again}, False{}, hit, n, k, d, 0n})), ot.inv(Once.wd_answer(v, O.Running{again}, n, k, d, 0n))) == True{} : Bool}, {==}, {==})
                        case 1n+qx:
                          match p:
                            case O.Never{}:
                              {==}
                            case O.Safe{}:
                              {==}
                            case O.Keyed{cap}:
                              LA.ob.keyed_cases(cap, again, v => {Bool.or(Bool.not(ot.inv(S.Wd{O.Running{again}, False{}, hit, n, k, d, 1n+qx})), ot.inv(Once.wd_answer(v, O.Running{again}, n, k, d, 1n+qx))) == True{} : Bool}, {==}, {==})
                    case O.Ran{}:
                      match x:
                        case 0n:
                          {==}
                        case 1n+qx:
                          {==}
                    case O.Unsure{}:
                      match x:
                        case 0n:
                          {==}
                        case 1n+qx:
                          {==}
                    case O.Void{}:
                      match x:
                        case 0n:
                          {==}
                        case 1n+qx:
                          {==}
        case O.Stop{}:
          match look:
            case True{}:
              match live:
                case True{}:
                  LA.ob.self(ot.inv(S.Wd{l, True{}, hit, n, k, d, x}))
                case False{}:
                  match l:
                    case O.Absent{}:
                      match x:
                        case 0n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 1n+qx:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                    case O.Pending{}:
                      match x:
                        case 0n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 1n+qx:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                    case O.Running{again}:
                      match x:
                        case 0n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 1n+qx:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                    case O.Ran{}:
                      match x:
                        case 0n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 1n+qx:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                    case O.Unsure{}:
                      match x:
                        case 0n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 1n+qx:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                    case O.Void{}:
                      match x:
                        case 0n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
                        case 1n+qx:
                          match k:
                            case 0n:
                              {==}
                            case 1n+qk:
                              {==}
            case False{}:
              match live:
                case True{}:
                  LA.ob.self(ot.inv(S.Wd{l, True{}, hit, n, k, d, x}))
                case False{}:
                  match l:
                    case O.Absent{}:
                      match x:
                        case 0n:
                          {==}
                        case 1n+qx:
                          {==}
                    case O.Pending{}:
                      match x:
                        case 0n:
                          {==}
                        case 1n+qx:
                          {==}
                    case O.Running{again}:
                      match x:
                        case 0n:
                          {==}
                        case 1n+qx:
                          {==}
                    case O.Ran{}:
                      match x:
                        case 0n:
                          {==}
                        case 1n+qx:
                          {==}
                    case O.Unsure{}:
                      match x:
                        case 0n:
                          {==}
                        case 1n+qx:
                          {==}
                    case O.Void{}:
                      match x:
                        case 0n:
                          {==}
                        case 1n+qx:
                          {==}
    case S.Land{}:
      match live:
        case True{}:
          match hit:
            case True{}:
              LA.ob.self(ot.inv(S.Wd{l, True{}, True{}, n, k, d, x}))
            case False{}:
              match l:
                case O.Absent{}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
                case O.Pending{}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
                case O.Running{again}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
                case O.Ran{}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
                case O.Unsure{}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
                case O.Void{}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
        case False{}:
          LA.ob.self(ot.inv(S.Wd{l, False{}, hit, n, k, d, x}))
    case S.End{}:
      match live:
        case True{}:
          match hit:
            case True{}:
              match l:
                case O.Absent{}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
                case O.Pending{}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
                case O.Running{again}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
                case O.Ran{}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
                case O.Unsure{}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
                case O.Void{}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
            case False{}:
              match l:
                case O.Absent{}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
                case O.Pending{}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
                case O.Running{again}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
                case O.Ran{}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
                case O.Unsure{}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
                case O.Void{}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
        case False{}:
          LA.ob.self(ot.inv(S.Wd{l, False{}, hit, n, k, d, x}))
    case S.Crash{}:
      match live:
        case True{}:
          match hit:
            case True{}:
              match l:
                case O.Absent{}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
                case O.Pending{}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
                case O.Running{again}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
                case O.Ran{}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
                case O.Unsure{}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
                case O.Void{}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
            case False{}:
              match l:
                case O.Absent{}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
                case O.Pending{}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
                case O.Running{again}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
                case O.Ran{}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
                case O.Unsure{}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
                case O.Void{}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
        case False{}:
          match hit:
            case True{}:
              match l:
                case O.Absent{}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
                case O.Pending{}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
                case O.Running{again}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
                case O.Ran{}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
                case O.Unsure{}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
                case O.Void{}:
                  match x:
                    case 0n:
                      {==}
                    case 1n+qx:
                      {==}
            case False{}:
              LA.ob.self(ot.inv(S.Wd{l, False{}, False{}, n, k, d, x}))

def ot.stepw(w: S.World, e: S.Ev, p: O.Policy) -> {Bool.or(Bool.not(ot.inv(w)), ot.inv(Once.wd_step(w, e, p))) == True{} : Bool}:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      ot.step(e, live, hit, l, x, k, n, d, p)

# the invariant holds after every history from a world it holds of
def ot.run(es: List<&2, S.Ev>, +w: S.World, +p: O.Policy, h: {ot.inv(w) == True{} : Bool}) -> {ot.inv(Once.wd_run(es, w, p)) == True{} : Bool}:
  match es:
    case Nil{}:
      h
    case +e <> rest:
      ot.run(rest, Once.wd_step(w, e, p), p, LA.ob.mp(ot.inv(w), ot.inv(Once.wd_step(w, e, p)), h, ot.stepw(w, e, p)))

def ot.out(live: Bool, hit: Bool, l: O.Life, x: Nat, k: Nat, n: Nat, d: Nat) -> {Bool.or(Bool.not(ot.inv(S.Wd{l, live, hit, n, k, d, x})), Nat.is_eq(S.late(S.Wd{l, live, hit, n, k, d, x}), 0n)) == True{} : Bool}:
  match live:
    case True{}:
      match hit:
        case True{}:
          match l:
            case O.Absent{}:
              match x:
                case 0n:
                  {==}
                case 1n+qx:
                  {==}
            case O.Pending{}:
              match x:
                case 0n:
                  {==}
                case 1n+qx:
                  {==}
            case O.Running{again}:
              match x:
                case 0n:
                  {==}
                case 1n+qx:
                  {==}
            case O.Ran{}:
              match x:
                case 0n:
                  {==}
                case 1n+qx:
                  {==}
            case O.Unsure{}:
              match x:
                case 0n:
                  {==}
                case 1n+qx:
                  {==}
            case O.Void{}:
              match x:
                case 0n:
                  {==}
                case 1n+qx:
                  {==}
        case False{}:
          match l:
            case O.Absent{}:
              match x:
                case 0n:
                  {==}
                case 1n+qx:
                  {==}
            case O.Pending{}:
              match x:
                case 0n:
                  {==}
                case 1n+qx:
                  {==}
            case O.Running{again}:
              match x:
                case 0n:
                  {==}
                case 1n+qx:
                  {==}
            case O.Ran{}:
              match x:
                case 0n:
                  {==}
                case 1n+qx:
                  {==}
            case O.Unsure{}:
              match x:
                case 0n:
                  {==}
                case 1n+qx:
                  {==}
            case O.Void{}:
              match x:
                case 0n:
                  {==}
                case 1n+qx:
                  {==}
    case False{}:
      match hit:
        case True{}:
          match l:
            case O.Absent{}:
              match x:
                case 0n:
                  {==}
                case 1n+qx:
                  {==}
            case O.Pending{}:
              match x:
                case 0n:
                  {==}
                case 1n+qx:
                  {==}
            case O.Running{again}:
              match x:
                case 0n:
                  {==}
                case 1n+qx:
                  {==}
            case O.Ran{}:
              match x:
                case 0n:
                  {==}
                case 1n+qx:
                  {==}
            case O.Unsure{}:
              match x:
                case 0n:
                  {==}
                case 1n+qx:
                  {==}
            case O.Void{}:
              match x:
                case 0n:
                  {==}
                case 1n+qx:
                  {==}
        case False{}:
          match l:
            case O.Absent{}:
              match x:
                case 0n:
                  {==}
                case 1n+qx:
                  {==}
            case O.Pending{}:
              match x:
                case 0n:
                  {==}
                case 1n+qx:
                  {==}
            case O.Running{again}:
              match x:
                case 0n:
                  {==}
                case 1n+qx:
                  {==}
            case O.Ran{}:
              match x:
                case 0n:
                  {==}
                case 1n+qx:
                  {==}
            case O.Unsure{}:
              match x:
                case 0n:
                  {==}
                case 1n+qx:
                  {==}
            case O.Void{}:
              match x:
                case 0n:
                  {==}
                case 1n+qx:
                  {==}

def ot.outw(w: S.World) -> {Bool.or(Bool.not(ot.inv(w)), Nat.is_eq(S.late(w), 0n)) == True{} : Bool}:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      ot.out(live, hit, l, x, k, n, d)
