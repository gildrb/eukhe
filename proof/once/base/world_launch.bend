# eukhe: lemmas the proofs of area once share: a `never` effect the world is never asked about is launched at most once
#
# The invariant ol.inv holds of the first world, every event of a
# history in which the world is never asked keeps it (ol.step), so it
# holds after every such history (ol.run); a world it holds of made at
# most one launch (ol.out).

import Base
import ../../../bend/once.bend as O
import ../../../laws/once.bend as Once
import ../../../spec/once/life.bend as S
import ../base.bend as LA

# the invariant: an effect never launched has no launch made and none in
# flight; a started one was launched at most once; an ended one has none
# in flight
def ol.inv(w: S.World) -> Bool:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      match l:
        case O.Absent{}:
          Bool.and(Bool.not(live), Nat.is_eq(n, 0n))
        case O.Pending{}:
          Bool.and(Bool.not(live), Nat.is_eq(n, 0n))
        case O.Running{again}:
          Nat.is_le(n, 1n)
        case O.Ran{}:
          Bool.and(Bool.not(live), Nat.is_le(n, 1n))
        case O.Unsure{}:
          Bool.and(Bool.not(live), Nat.is_le(n, 1n))
        case O.Void{}:
          Bool.and(Bool.not(live), Nat.is_le(n, 1n))

def ol.step(e: S.Ev, live: Bool, hit: Bool, l: O.Life, n: Nat, k: Nat, d: Nat, x: Nat) -> {Bool.or(Bool.not(ol.inv(S.Wd{l, live, hit, n, k, d, x})), ol.inv(Once.wd_step(S.Wd{l, live, hit, n, k, d, x}, S.dim.ev(e), O.Never{}))) == True{} : Bool}:
  match e:
    case S.Mean{}:
      match l:
        case O.Absent{}:
          LA.ob.self(ol.inv(S.Wd{O.Absent{}, live, hit, n, k, d, x}))
        case O.Pending{}:
          LA.ob.self(ol.inv(S.Wd{O.Pending{}, live, hit, n, k, d, x}))
        case O.Running{again}:
          LA.ob.self(ol.inv(S.Wd{O.Running{again}, live, hit, n, k, d, x}))
        case O.Ran{}:
          LA.ob.self(ol.inv(S.Wd{O.Ran{}, live, hit, n, k, d, x}))
        case O.Unsure{}:
          LA.ob.self(ol.inv(S.Wd{O.Unsure{}, live, hit, n, k, d, x}))
        case O.Void{}:
          LA.ob.self(ol.inv(S.Wd{O.Void{}, live, hit, n, k, d, x}))
    case S.Tick{m, look}:
      match m:
        case O.Resume{}:
          match live:
            case True{}:
              LA.ob.self(ol.inv(S.Wd{l, True{}, hit, n, k, d, x}))
            case False{}:
              match l:
                case O.Absent{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Pending{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Running{again}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Ran{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Unsure{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Void{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
        case O.Stop{}:
          match live:
            case True{}:
              LA.ob.self(ol.inv(S.Wd{l, True{}, hit, n, k, d, x}))
            case False{}:
              match l:
                case O.Absent{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Pending{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Running{again}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Ran{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Unsure{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Void{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
    case S.Land{}:
      match live:
        case True{}:
          match hit:
            case True{}:
              LA.ob.self(ol.inv(S.Wd{l, True{}, True{}, n, k, d, x}))
            case False{}:
              match l:
                case O.Absent{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Pending{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Running{again}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Ran{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Unsure{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Void{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
        case False{}:
          LA.ob.self(ol.inv(S.Wd{l, False{}, hit, n, k, d, x}))
    case S.End{}:
      match live:
        case True{}:
          match hit:
            case True{}:
              match l:
                case O.Absent{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Pending{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Running{again}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Ran{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Unsure{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Void{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
            case False{}:
              match l:
                case O.Absent{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Pending{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Running{again}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Ran{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Unsure{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Void{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
        case False{}:
          LA.ob.self(ol.inv(S.Wd{l, False{}, hit, n, k, d, x}))
    case S.Crash{}:
      match live:
        case True{}:
          match hit:
            case True{}:
              match l:
                case O.Absent{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Pending{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Running{again}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Ran{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Unsure{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Void{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
            case False{}:
              match l:
                case O.Absent{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Pending{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Running{again}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Ran{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Unsure{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Void{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
        case False{}:
          match hit:
            case True{}:
              match l:
                case O.Absent{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Pending{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Running{again}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Ran{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Unsure{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
                case O.Void{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n:
                      {==}
                    case 2n+qn:
                      {==}
            case False{}:
              LA.ob.self(ol.inv(S.Wd{l, False{}, False{}, n, k, d, x}))

def ol.stepw(w: S.World, e: S.Ev) -> {Bool.or(Bool.not(ol.inv(w)), ol.inv(Once.wd_step(w, S.dim.ev(e), O.Never{}))) == True{} : Bool}:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      ol.step(e, live, hit, l, n, k, d, x)

# the invariant holds after every history from a world it holds of
def ol.run(es: List<&2, S.Ev>, +w: S.World, h: {ol.inv(w) == True{} : Bool}) -> {ol.inv(Once.wd_run(S.dim(es), w, O.Never{})) == True{} : Bool}:
  match es:
    case Nil{}:
      h
    case +e <> rest:
      ol.run(rest, Once.wd_step(w, S.dim.ev(e), O.Never{}), LA.ob.mp(ol.inv(w), ol.inv(Once.wd_step(w, S.dim.ev(e), O.Never{})), h, ol.stepw(w, e)))

def ol.out(live: Bool, hit: Bool, l: O.Life, n: Nat, k: Nat, d: Nat, x: Nat) -> {Bool.or(Bool.not(ol.inv(S.Wd{l, live, hit, n, k, d, x})), Nat.is_le(S.launches(S.Wd{l, live, hit, n, k, d, x}), 1n)) == True{} : Bool}:
  match live:
    case True{}:
      match hit:
        case True{}:
          match l:
            case O.Absent{}:
              match n:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qn:
                  {==}
            case O.Pending{}:
              match n:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qn:
                  {==}
            case O.Running{again}:
              match n:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qn:
                  {==}
            case O.Ran{}:
              match n:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qn:
                  {==}
            case O.Unsure{}:
              match n:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qn:
                  {==}
            case O.Void{}:
              match n:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qn:
                  {==}
        case False{}:
          match l:
            case O.Absent{}:
              match n:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qn:
                  {==}
            case O.Pending{}:
              match n:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qn:
                  {==}
            case O.Running{again}:
              match n:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qn:
                  {==}
            case O.Ran{}:
              match n:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qn:
                  {==}
            case O.Unsure{}:
              match n:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qn:
                  {==}
            case O.Void{}:
              match n:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qn:
                  {==}
    case False{}:
      match hit:
        case True{}:
          match l:
            case O.Absent{}:
              match n:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qn:
                  {==}
            case O.Pending{}:
              match n:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qn:
                  {==}
            case O.Running{again}:
              match n:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qn:
                  {==}
            case O.Ran{}:
              match n:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qn:
                  {==}
            case O.Unsure{}:
              match n:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qn:
                  {==}
            case O.Void{}:
              match n:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qn:
                  {==}
        case False{}:
          match l:
            case O.Absent{}:
              match n:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qn:
                  {==}
            case O.Pending{}:
              match n:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qn:
                  {==}
            case O.Running{again}:
              match n:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qn:
                  {==}
            case O.Ran{}:
              match n:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qn:
                  {==}
            case O.Unsure{}:
              match n:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qn:
                  {==}
            case O.Void{}:
              match n:
                case 0n:
                  {==}
                case 1n:
                  {==}
                case 2n+qn:
                  {==}

def ol.outw(w: S.World) -> {Bool.or(Bool.not(ol.inv(w)), Nat.is_le(S.launches(w), 1n)) == True{} : Bool}:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      ol.out(live, hit, l, n, k, d, x)
