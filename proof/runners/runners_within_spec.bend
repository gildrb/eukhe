# eukhe: the proof of LAW runners_within_spec
# Ru.elem is the spec's membership (ruw.has); then cap by cap.

import Base
import ../../bend/runners.bend as Ru
import ../../laws/runners.bend as Runners

def ruw.has(xs: List<&2, Nat>, +x: Nat) -> {Ru.elem(xs, x) == Runners.ru_has(xs, x) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case y <> rest:
      %ruw.has(rest, x) : {Bool.or(Nat.is_eq(y, x), Ru.elem(rest, x)) == Bool.or(Nat.is_eq(y, x), _) : Bool}
      {==}

def Runners.runners_within_spec(caps, auto):
  match caps:
    case Nil{}:
      {==}
    case +c <> +rest:
      %Runners.runners_within_spec(rest, auto) : {Ru.within(c <> rest, auto) == Bool.and(Bool.and(Runners.ru_grantable(c), Runners.ru_has(auto, c)), _) : Bool}
      %ruw.has(auto, c) : {Ru.within(c <> rest, auto) == Bool.and(Bool.and(Runners.ru_grantable(c), _), Ru.within(rest, auto)) : Bool}
      {==}
