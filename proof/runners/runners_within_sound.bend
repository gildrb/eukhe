# eukhe: the proof of LAW runners_within_sound
#
# PROOF: induction on the caps and the index: within a cap list, its head is grantable and in the auto set (the laws' membership is the code's, rws.has) and the rest is within it.

import Base
import ../../bend/runners.bend as Ru
import ../../bend/ffi_runners.bend as FRu
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/runners.bend as Runners
import ../base/staging.bend as LStg

# the laws' membership is the code's
def rws.has(xs: List<&2, Nat>, +x: Nat) -> {Runners.ru_has(xs, x) == Ru.elem(xs, x) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case y <> rest:
      %rws.has(rest, x) : {Bool.or(Nat.is_eq(y, x), Runners.ru_has(rest, x)) == Bool.or(Nat.is_eq(y, x), _) : Bool}
      {==}

def rws.MD(m: Maybe<&2, Nat>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

def rws.go(caps: List<&2, Nat>, +auto: List<&2, Nat>, i: Nat, +c: Nat, +free: {Ru.within(caps, auto) == True{} : Bool}, at: {List.get(&2, Nat, caps, i) == Some{c} : Maybe<&2, Nat>}) -> {Bool.and(Nat.is_lt(c, 6n), Runners.ru_has(auto, c)) == True{} : Bool}:
  match caps:
    case Nil{}:
      %at : rws.MD(_, {Bool.and(Nat.is_lt(c, 6n), Runners.ru_has(auto, c)) == True{} : Bool})
      Unit{}
    case +x <> +rest:
      match i:
        case 0n:
          +same = Equal.cong(Maybe<&2, Nat>, Nat, m => Maybe.default(&2, Nat, m, c), Some{x}, Some{c}, at)
          %same : {Bool.and(Nat.is_lt(_, 6n), Runners.ru_has(auto, _)) == True{} : Bool}
          %Equal.sym(Bool, Runners.ru_has(auto, x), Ru.elem(auto, x), rws.has(auto, x)) : {Bool.and(Nat.is_lt(x, 6n), _) == True{} : Bool}
          LStg.stg.and_l(Bool.and(Nat.is_lt(x, 6n), Ru.elem(auto, x)), Ru.within(rest, auto), free)
        case 1n+p:
          rws.go(rest, auto, p, c, LStg.stg.and_r(Bool.and(Nat.is_lt(x, 6n), Ru.elem(auto, x)), Ru.within(rest, auto), free), at)

def Runners.runners_within_sound(caps, auto, i, c, free, at):
  rws.go(caps, auto, i, c, free, at)
