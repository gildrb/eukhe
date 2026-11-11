# eukhe: the proof of LAW runners_within_complete
#
# PROOF: induction on the caps: when the head is not a grantable effect in the auto set it is the witness (index 0; the laws' membership is the code's, rwc.has); else the rest is not within it and its witness moves one index on.

import Base
import ../../bend/runners.bend as Ru
import ../../bend/ffi_runners.bend as FRu
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/runners.bend as Runners
import ../base/staging.bend as LStg

def rwc.has(xs: List<&2, Nat>, +x: Nat) -> {Runners.ru_has(xs, x) == Ru.elem(xs, x) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case y <> rest:
      %rwc.has(rest, x) : {Bool.or(Nat.is_eq(y, x), Runners.ru_has(rest, x)) == Bool.or(Nat.is_eq(y, x), _) : Bool}
      {==}

def rwc.G(caps: List<&2, Nat>, auto: List<&2, Nat>) -> Type:
  &i: Nat -> &c: Nat -> ({List.get(&2, Nat, caps, i) == Some{c} : Maybe<&2, Nat>} & {Bool.and(Nat.is_lt(c, 6n), Runners.ru_has(auto, c)) == False{} : Bool})

def rwc.shift(-x: Nat, -rest: List<&2, Nat>, -auto: List<&2, Nat>, r: rwc.G(rest, auto)) -> rwc.G(x <> rest, auto):
  (i, (c, p)) = r
  (1n+i, (c, p))

def rwc.cons(+x: Nat, +rest: List<&2, Nat>, +auto: List<&2, Nat>, b: Bool, +eb: {Bool.and(Nat.is_lt(x, 6n), Ru.elem(auto, x)) == b : Bool}, +held: {Bool.and(Bool.and(Nat.is_lt(x, 6n), Ru.elem(auto, x)), Ru.within(rest, auto)) == False{} : Bool}, ih: {Ru.within(rest, auto) == False{} : Bool} -> rwc.G(rest, auto)) -> rwc.G(x <> rest, auto):
  match b:
    case False{}:
      +hn = Equal.trans(Bool, Bool.and(Nat.is_lt(x, 6n), Runners.ru_has(auto, x)), Bool.and(Nat.is_lt(x, 6n), Ru.elem(auto, x)), False{}, Equal.cong(Bool, Bool, z => Bool.and(Nat.is_lt(x, 6n), z), Runners.ru_has(auto, x), Ru.elem(auto, x), rwc.has(auto, x)), eb)
      (0n, (x, ({==}, hn)))
    case True{}:
      +hw = Equal.trans(Bool, Ru.within(rest, auto), Bool.and(Bool.and(Nat.is_lt(x, 6n), Ru.elem(auto, x)), Ru.within(rest, auto)), False{}, Equal.cong(Bool, Bool, z => Bool.and(z, Ru.within(rest, auto)), True{}, Bool.and(Nat.is_lt(x, 6n), Ru.elem(auto, x)), Equal.sym(Bool, Bool.and(Nat.is_lt(x, 6n), Ru.elem(auto, x)), True{}, eb)), held)
      rwc.shift(x, rest, auto, ih(hw))

def rwc.go(caps: List<&2, Nat>, +auto: List<&2, Nat>, held: {Ru.within(caps, auto) == False{} : Bool}) -> rwc.G(caps, auto):
  match caps:
    case Nil{}:
      LStg.stg.absurd(rwc.G(Nil{}, auto), held)
    case +x <> +rest:
      rwc.cons(x, rest, auto, Bool.and(Nat.is_lt(x, 6n), Ru.elem(auto, x)), {==}, held, h => rwc.go(rest, auto, h))

def Runners.runners_within_complete(caps, auto, held):
  rwc.go(caps, auto, held)
