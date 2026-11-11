# eukhe: lemmas the proofs of area once share: a keyed effect the world is never asked about is sent at most 1 + cap times
#
# The invariant oc.inv holds of the first world: a running effect was
# launched once more than it was sent again, and sent again at most cap
# times; an ended one was launched at most 1 + cap times. Every event of
# a history in which the world is never asked keeps it (oc.step: a keyed
# effect is sent again only while fewer than cap, LA.ob.keyed_within; a
# running effect that ends is within the bound, oc.bound), so it holds
# after every such history (oc.run); a world it holds of made at most 1
# + cap launches (oc.outw).

import Base
import ../../../bend/once.bend as O
import ../../../laws/once.bend as Once
import ../../../spec/once/life.bend as S
import ../base.bend as LA

# the invariant
def oc.inv(cap: Nat, w: S.World) -> Bool:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      match l:
        case O.Absent{}:
          Bool.and(Bool.not(live), Nat.is_eq(n, 0n))
        case O.Pending{}:
          Bool.and(Bool.not(live), Nat.is_eq(n, 0n))
        case O.Running{+again}:
          Bool.and(Nat.is_le(again, cap), Nat.is_eq(n, 1n+again))
        case O.Ran{}:
          Bool.and(Bool.not(live), Nat.is_le(n, 1n+cap))
        case O.Unsure{}:
          Bool.and(Bool.not(live), Nat.is_le(n, 1n+cap))
        case O.Void{}:
          Bool.and(Bool.not(live), Nat.is_le(n, 1n+cap))

# a and b imply b
def oc.keep(a: Bool, b: Bool) -> {Bool.or(Bool.not(Bool.and(a, b)), b) == True{} : Bool}:
  match a:
    case True{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}

# a <= c and m == a imply m <= c
def oc.le_eq(m: Nat, a: Nat, c: Nat) -> {Bool.or(Bool.not(Bool.and(Nat.is_le(a, c), Nat.is_eq(m, a))), Nat.is_le(m, c)) == True{} : Bool}:
  match m:
    case 0n:
      match a:
        case 0n:
          match c:
            case 0n:
              {==}
            case 1n+c2:
              {==}
        case 1n+a2:
          match c:
            case 0n:
              {==}
            case 1n+c2:
              LA.ob.or_true(Bool.not(Bool.and(Nat.is_le(a2, c2), False{})))
    case 1n+m2:
      match a:
        case 0n:
          match c:
            case 0n:
              {==}
            case 1n+c2:
              {==}
        case 1n+a2:
          match c:
            case 0n:
              {==}
            case 1n+c2:
              oc.le_eq(m2, a2, c2)

# a running effect sent again a times, a <= c, was launched 1 + a times:
# at most 1 + c
def oc.bound(n: Nat, a: Nat, c: Nat) -> {Bool.or(Bool.not(Bool.and(Nat.is_le(a, c), Nat.is_eq(n, 1n+a))), Nat.is_le(n, 1n+c)) == True{} : Bool}:
  match n:
    case 0n:
      LA.ob.or_true(Bool.not(Bool.and(Nat.is_le(a, c), False{})))
    case 1n+m:
      oc.le_eq(m, a, c)

# one more send within the cap keeps the invariant
def oc.launch(cap: Nat, +again: Nat, n: Nat, hl: {Nat.is_le(1n+again, cap) == True{} : Bool}) -> {Bool.or(Bool.not(Bool.and(Nat.is_le(again, cap), Nat.is_eq(n, 1n+again))), Bool.and(Nat.is_le(1n+again, cap), Nat.is_eq(n, 1n+again))) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_le(1n+again, cap), True{}, hl) : {Bool.or(Bool.not(Bool.and(Nat.is_le(again, cap), Nat.is_eq(n, 1n+again))), Bool.and(_, Nat.is_eq(n, 1n+again))) == True{} : Bool}
  oc.keep(Nat.is_le(again, cap), Nat.is_eq(n, 1n+again))

def oc.step(e: S.Ev, live: Bool, hit: Bool, l: O.Life, +n: Nat, +cap: Nat, k: Nat, d: Nat, x: Nat) -> {Bool.or(Bool.not(oc.inv(cap, S.Wd{l, live, hit, n, k, d, x})), oc.inv(cap, Once.wd_step(S.Wd{l, live, hit, n, k, d, x}, S.dim.ev(e), O.Keyed{cap}))) == True{} : Bool}:
  match e:
    case S.Mean{}:
      match l:
        case O.Absent{}:
          LA.ob.self(oc.inv(cap, S.Wd{O.Absent{}, live, hit, n, k, d, x}))
        case O.Pending{}:
          LA.ob.self(oc.inv(cap, S.Wd{O.Pending{}, live, hit, n, k, d, x}))
        case O.Running{again}:
          LA.ob.self(oc.inv(cap, S.Wd{O.Running{again}, live, hit, n, k, d, x}))
        case O.Ran{}:
          LA.ob.self(oc.inv(cap, S.Wd{O.Ran{}, live, hit, n, k, d, x}))
        case O.Unsure{}:
          LA.ob.self(oc.inv(cap, S.Wd{O.Unsure{}, live, hit, n, k, d, x}))
        case O.Void{}:
          LA.ob.self(oc.inv(cap, S.Wd{O.Void{}, live, hit, n, k, d, x}))
    case S.Tick{m, look}:
      match m:
        case O.Resume{}:
          match live:
            case True{}:
              LA.ob.self(oc.inv(cap, S.Wd{l, True{}, hit, n, k, d, x}))
            case False{}:
              match l:
                case O.Absent{}:
                  LA.ob.self(oc.inv(cap, S.Wd{O.Absent{}, False{}, hit, n, k, d, x}))
                case O.Pending{}:
                  match n:
                    case 0n:
                      match cap:
                        case 0n:
                          {==}
                        case 1n+c:
                          {==}
                    case 1n+q:
                      {==}
                case O.Running{+again}:
                  LA.ob.keyed_within(cap, again, v => {Bool.or(Bool.not(oc.inv(cap, S.Wd{O.Running{again}, False{}, hit, n, k, d, x})), oc.inv(cap, Once.wd_answer(v, O.Running{again}, n, k, d, x))) == True{} : Bool}, hl => oc.launch(cap, again, n, hl), oc.bound(n, again, cap))
                case O.Ran{}:
                  LA.ob.self(oc.inv(cap, S.Wd{O.Ran{}, False{}, hit, n, k, d, x}))
                case O.Unsure{}:
                  LA.ob.self(oc.inv(cap, S.Wd{O.Unsure{}, False{}, hit, n, k, d, x}))
                case O.Void{}:
                  LA.ob.self(oc.inv(cap, S.Wd{O.Void{}, False{}, hit, n, k, d, x}))
        case O.Stop{}:
          match live:
            case True{}:
              LA.ob.self(oc.inv(cap, S.Wd{l, True{}, hit, n, k, d, x}))
            case False{}:
              match l:
                case O.Absent{}:
                  LA.ob.self(oc.inv(cap, S.Wd{O.Absent{}, False{}, hit, n, k, d, x}))
                case O.Pending{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n+q:
                      {==}
                case O.Running{+again}:
                  oc.bound(n, again, cap)
                case O.Ran{}:
                  LA.ob.self(oc.inv(cap, S.Wd{O.Ran{}, False{}, hit, n, k, d, x}))
                case O.Unsure{}:
                  LA.ob.self(oc.inv(cap, S.Wd{O.Unsure{}, False{}, hit, n, k, d, x}))
                case O.Void{}:
                  LA.ob.self(oc.inv(cap, S.Wd{O.Void{}, False{}, hit, n, k, d, x}))
    case S.Land{}:
      match live:
        case True{}:
          match hit:
            case True{}:
              LA.ob.self(oc.inv(cap, S.Wd{l, True{}, True{}, n, k, d, x}))
            case False{}:
              match l:
                case O.Absent{}:
                  LA.ob.self(oc.inv(cap, S.Wd{O.Absent{}, True{}, False{}, n, k, d, x}))
                case O.Pending{}:
                  LA.ob.self(oc.inv(cap, S.Wd{O.Pending{}, True{}, False{}, n, k, d, x}))
                case O.Running{again}:
                  LA.ob.self(oc.inv(cap, S.Wd{O.Running{again}, True{}, False{}, n, k, d, x}))
                case O.Ran{}:
                  LA.ob.self(oc.inv(cap, S.Wd{O.Ran{}, True{}, False{}, n, k, d, x}))
                case O.Unsure{}:
                  LA.ob.self(oc.inv(cap, S.Wd{O.Unsure{}, True{}, False{}, n, k, d, x}))
                case O.Void{}:
                  LA.ob.self(oc.inv(cap, S.Wd{O.Void{}, True{}, False{}, n, k, d, x}))
        case False{}:
          LA.ob.self(oc.inv(cap, S.Wd{l, False{}, hit, n, k, d, x}))
    case S.End{}:
      match live:
        case True{}:
          match l:
            case O.Absent{}:
              {==}
            case O.Pending{}:
              {==}
            case O.Running{again}:
              oc.bound(n, again, cap)
            case O.Ran{}:
              {==}
            case O.Unsure{}:
              {==}
            case O.Void{}:
              {==}
        case False{}:
          LA.ob.self(oc.inv(cap, S.Wd{l, False{}, hit, n, k, d, x}))
    case S.Crash{}:
      match live:
        case True{}:
          match l:
            case O.Absent{}:
              {==}
            case O.Pending{}:
              {==}
            case O.Running{again}:
              LA.ob.self(oc.inv(cap, S.Wd{O.Running{again}, True{}, hit, n, k, d, x}))
            case O.Ran{}:
              {==}
            case O.Unsure{}:
              {==}
            case O.Void{}:
              {==}
        case False{}:
          match l:
            case O.Absent{}:
              LA.ob.self(oc.inv(cap, S.Wd{O.Absent{}, False{}, hit, n, k, d, x}))
            case O.Pending{}:
              LA.ob.self(oc.inv(cap, S.Wd{O.Pending{}, False{}, hit, n, k, d, x}))
            case O.Running{again}:
              LA.ob.self(oc.inv(cap, S.Wd{O.Running{again}, False{}, hit, n, k, d, x}))
            case O.Ran{}:
              LA.ob.self(oc.inv(cap, S.Wd{O.Ran{}, False{}, hit, n, k, d, x}))
            case O.Unsure{}:
              LA.ob.self(oc.inv(cap, S.Wd{O.Unsure{}, False{}, hit, n, k, d, x}))
            case O.Void{}:
              LA.ob.self(oc.inv(cap, S.Wd{O.Void{}, False{}, hit, n, k, d, x}))

def oc.stepw(+cap: Nat, w: S.World, e: S.Ev) -> {Bool.or(Bool.not(oc.inv(cap, w)), oc.inv(cap, Once.wd_step(w, S.dim.ev(e), O.Keyed{cap}))) == True{} : Bool}:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      oc.step(e, live, hit, l, n, cap, k, d, x)

# the invariant holds after every history from a world it holds of
def oc.run(es: List<&2, S.Ev>, +w: S.World, +cap: Nat, h: {oc.inv(cap, w) == True{} : Bool}) -> {oc.inv(cap, Once.wd_run(S.dim(es), w, O.Keyed{cap})) == True{} : Bool}:
  match es:
    case Nil{}:
      h
    case +e <> rest:
      oc.run(rest, Once.wd_step(w, S.dim.ev(e), O.Keyed{cap}), cap, LA.ob.mp(oc.inv(cap, w), oc.inv(cap, Once.wd_step(w, S.dim.ev(e), O.Keyed{cap})), h, oc.stepw(cap, w, e)))

# a world the invariant holds of made at most 1 + cap launches
def oc.outw(+cap: Nat, w: S.World) -> {Bool.or(Bool.not(oc.inv(cap, w)), Nat.is_le(S.launches(w), 1n+cap)) == True{} : Bool}:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      match l:
        case O.Absent{}:
          match live:
            case True{}:
              {==}
            case False{}:
              match n:
                case 0n:
                  {==}
                case 1n+q:
                  {==}
        case O.Pending{}:
          match live:
            case True{}:
              {==}
            case False{}:
              match n:
                case 0n:
                  {==}
                case 1n+q:
                  {==}
        case O.Running{again}:
          oc.bound(n, again, cap)
        case O.Ran{}:
          match live:
            case True{}:
              {==}
            case False{}:
              LA.ob.self(Nat.is_le(n, 1n+cap))
        case O.Unsure{}:
          match live:
            case True{}:
              {==}
            case False{}:
              LA.ob.self(Nat.is_le(n, 1n+cap))
        case O.Void{}:
          match live:
            case True{}:
              {==}
            case False{}:
              LA.ob.self(Nat.is_le(n, 1n+cap))
