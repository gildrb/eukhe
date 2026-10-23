# eukhe: the proof of LAW guard_keeps_others

import Base
import ../../bend/infer.bend as If
import ../../laws/infer.bend as Infer
import ./base.bend as LA

def pi.or_l(a: Bool, +b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      LA.pi.absurd({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def pi.or_r(a: Bool, +b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      LA.pi.absurd({b == False{} : Bool}, h)
    case False{}:
      h

# a guard on a stream with no periodic window never cuts
def pi.keep_go(+xs: List<&2, Nat>, +k: Nat, +seen: List<&2, Nat>, +n: Nat, hit: Bool, +eh: {If.fire.at(xs, k, seen) == hit : Bool}, +calm: {If.loops.go(xs, k, seen) == False{} : Bool}) -> {If.guard.go(xs, k, seen, n, hit) == If.Whole{} : If.Cut}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      match hit:
        case True{}:
          +cp = pi.or_l(If.periodic(x <> seen, k), If.loops.go(rest, k, x <> seen), calm)
          +fp = Equal.trans(Bool, If.fires(x <> seen, k), If.periodic(x <> seen, k), False{}, LA.pi.fires_periodic(x <> seen, k, If.periods(k)), cp)
          LA.pi.void({If.CutAt{1n+n} == If.Whole{} : If.Cut}, LA.pi.flip(If.fires(x <> seen, k), eh, fp))
        case False{}:
          pi.keep_go(rest, k, x <> seen, 1n+n, If.fire.at(rest, k, x <> seen), {==}, pi.or_r(If.periodic(x <> seen, k), If.loops.go(rest, k, x <> seen), calm))

def pi.guard_keeps_others(+xs: List<&2, Nat>, +k: Nat, calm: {If.loops(xs, k) == False{} : Bool}) -> {If.guard(xs, k) == If.Whole{} : If.Cut}:
  pi.keep_go(xs, k, Nil{}, 0n, If.fire.at(xs, k, Nil{}), {==}, calm)

def Infer.guard_keeps_others(xs, k, calm):
  pi.guard_keeps_others(xs, k, calm)
