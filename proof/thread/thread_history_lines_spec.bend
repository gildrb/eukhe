# eukhe: the proof of LAW thread_history_lines_spec
#
# PROOF: by induction on the starts: a start below end adds one to the
# count of the rest, as it adds one item to the spec's run; the first
# start that is not ends both (thl.step, by cases on the comparison).

import Base
import ../../bend/thread.bend as Th
import ../../spec/memory/thread.bend as S
import ../../laws/thread.bend as Thread

def thl.step(b: Bool, x: Nat, rest: List<&2, Nat>, n: Nat, ih: {n == List.length(&2, Nat, rest) : Nat}) -> {Th.history_lines.step(b, n) == List.length(&2, Nat, S.run.keep(b, x, rest)) : Nat}:
  match b:
    case True{}:
      %ih : {1n+n == 1n+_ : Nat}
      {==}
    case False{}:
      {==}

def thl.go(xs: List<&2, Nat>, +e: Nat) -> {Th.history_lines.go(xs, e) == S.lead(e, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      thl.step(Nat.is_lt(x, e), x, S.run(e, t), Th.history_lines.go(t, e), thl.go(t, e))

def Thread.thread_history_lines_spec(t, v, xs):
  thl.go(xs, Nat.sub(t, v))
