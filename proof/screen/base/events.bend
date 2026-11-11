# eukhe: lemmas the proofs of laws/screen/events.bend share: equal ids, states and
# lengths compare True, and conjunctions of True are True

import Base
import ../../../bend/screen.bend as Sc
import ../../../laws/screen/events.bend as ScreenEvents

def ev.refl(n: Nat) -> {True{} == Nat.is_eq(n, n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      ev.refl(p)

# a number equals itself
def ev.t(+n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  Equal.sym(Bool, True{}, Nat.is_eq(n, n), ev.refl(n))

def ev.st_refl(s: Sc.St) -> {True{} == ScreenEvents.tx_st_eq(s, s) : Bool}:
  match s:
    case Sc.Active{}:
      {==}
    case Sc.Final{}:
      {==}
    case Sc.Comm{}:
      {==}

# a state equals itself
def ev.st_t(+s: Sc.St) -> {ScreenEvents.tx_st_eq(s, s) == True{} : Bool}:
  Equal.sym(Bool, True{}, ScreenEvents.tx_st_eq(s, s), ev.st_refl(s))

def ev.and_t(+a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def ev.and3(+a: Bool, +b: Bool, +c: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}, hc: {c == True{} : Bool}) -> {Bool.and(a, Bool.and(b, c)) == True{} : Bool}:
  ev.and_t(a, Bool.and(b, c), ha, ev.and_t(b, c, hb, hc))
