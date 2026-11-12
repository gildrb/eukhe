# eukhe: the proof of LAW thread_history_lines_run
#
# PROOF: by induction on the starts. A start below end adds one to the
# count of the rest: the count still fits under the starts, the start
# joins the run below end, and the rest's run ends where it did (the
# induction hypothesis). The first start not below end stops the count at
# 0: no start is counted, and that start is at or past end (thr.not_lt).

import Base
import ../../bend/thread.bend as Th
import ../../spec/memory/thread.bend as S
import ../../laws/thread.bend as Thread
import ./base.bend as LA

# a start not below e is at or past e
def thr.not_lt(x: Nat, e: Nat, h: {Nat.is_lt(x, e) == False{} : Bool}) -> {Nat.is_le(e, x) == True{} : Bool}:
  match x e:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LA.thb.absurd_tf({Nat.is_le(1n+q, 0n) == True{} : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      thr.not_lt(p, q, h)

def thr.step(b: Bool, +x: Nat, +t: List<&2, Nat>, +e: Nat, eb: {Nat.is_lt(x, e) == b : Bool}, ih: {S.leading(e, t, Th.history_lines.go(t, e)) == True{} : Bool}) -> {S.leading(e, x <> t, Th.history_lines.step(b, Th.history_lines.go(t, e))) == True{} : Bool}:
  match b:
    case True{}:
      +n = Th.history_lines.go(t, e)
      %Equal.sym(Bool, Nat.is_lt(x, e), True{}, eb) : {Bool.and(Nat.is_le(1n+n, 1n+List.length(&2, Nat, t)), Bool.and(Bool.and(_, S.all_below(e, List.take(&2, Nat, t, n))), S.opens_at_or_past(e, List.drop(&2, Nat, t, n)))) == True{} : Bool}
      ih
    case False{}:
      thr.not_lt(x, e, eb)

def thr.go(xs: List<&2, Nat>, +e: Nat) -> {S.leading(e, xs, Th.history_lines.go(xs, e)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      thr.step(Nat.is_lt(x, e), x, t, e, {==}, thr.go(t, e))

def Thread.thread_history_lines_run(t, v, xs):
  thr.go(xs, Nat.sub(t, v))
