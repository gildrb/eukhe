# eukhe: the proof of LAW settle_run_lines
# Induction on the outcomes, over the view: an outcome of a call of line
# j changes line k by Pend.after when j is k and leaves it as it was
# otherwise (srl.hit, by induction on the view and both indexes), so line
# k ends as Pend.run of the outcomes of its own calls (srl.go), which is
# the count's line (pend_run_counts).

import Base
import ../../bend/compactor.bend as C
import ../../laws/compactor.bend as Compactor
import ./pend_run_counts.bend as PPendRunCounts

# a view line after the outcomes os, by Pend.run
def srl.run(os: List<&2, C.Outcome>, m: Maybe<&2, C.Pend>) -> Maybe<&2, C.Pend>:
  match m:
    case None{}:
      None{}
    case Some{p}:
      Some{C.Pend.run(os, p)}

def srl.nil(m: Maybe<&2, C.Pend>) -> {m == srl.run(Nil{}, m) : Maybe<&2, C.Pend>}:
  match m:
    case None{}:
      {==}
    case Some{p}:
      {==}

def srl.hit(ps: List<&2, C.Pend>, j: Nat, k: Nat, +o: C.Outcome, -oo: List<&2, C.Outcome>) -> {srl.run(oo, List.get(&2, C.Pend, C.hit(ps, j, o), k)) == srl.run(Compactor.keep_if(Nat.is_eq(j, k), o, oo), List.get(&2, C.Pend, ps, k)) : Maybe<&2, C.Pend>}:
  match ps j k:
    case Nil{} x y:
      {==}
    case p <> rest 0n 0n:
      {==}
    case p <> rest 0n 1n+y:
      {==}
    case p <> rest 1n+x 0n:
      {==}
    case p <> rest 1n+x 1n+y:
      srl.hit(rest, x, y, o, oo)

def srl.go(es: List<&2, C.End>, +ps: List<&2, C.Pend>, +k: Nat) -> {List.get(&2, C.Pend, C.run(es, ps), k) == srl.run(Compactor.outcomes_of(es, k), List.get(&2, C.Pend, ps, k)) : Maybe<&2, C.Pend>}:
  match es:
    case Nil{}:
      srl.nil(List.get(&2, C.Pend, ps, k))
    case C.End{+j, +o} <> +rest:
      +h = C.hit(ps, j, o)
      +oo = Compactor.outcomes_of(rest, k)
      Equal.trans(Maybe<&2, C.Pend>, List.get(&2, C.Pend, C.run(rest, h), k), srl.run(oo, List.get(&2, C.Pend, h, k)), srl.run(Compactor.keep_if(Nat.is_eq(j, k), o, oo), List.get(&2, C.Pend, ps, k)),
        srl.go(rest, h, k), srl.hit(ps, j, k, o, oo))

# Pend.run is the count's line
def srl.counts(+os: List<&2, C.Outcome>, m: Maybe<&2, C.Pend>) -> {srl.run(os, m) == Compactor.line_after(os, m) : Maybe<&2, C.Pend>}:
  match m:
    case None{}:
      {==}
    case Some{+p}:
      Equal.cong(C.Pend, Maybe<&2, C.Pend>, z => Some{z}, C.Pend.run(os, p), Compactor.after_all(os, p), Compactor.pend_run_counts(os, p))

def Compactor.settle_run_lines(es, ps, k):
  +oo = Compactor.outcomes_of(es, k)
  +m = List.get(&2, C.Pend, ps, k)
  Equal.trans(Maybe<&2, C.Pend>, List.get(&2, C.Pend, C.run(es, ps), k), srl.run(oo, m), Compactor.line_after(oo, m), srl.go(es, ps, k), srl.counts(oo, m))
