# eukhe: lemmas the proofs of area wait share

import Base
import ../../bend/wait.bend as Wt

# ---- wait ----

# proof_wait: the wait laws of LAWS.bend (H6): a wait ends exactly once,
# no later than its deadline or its cancel, and with the event when the
# event comes first. Each lemma speaks of an open wait whose deadline
# passes on the (m + 1)-th tick (`pw.up` names that deadline in ticks
# from now), by induction on the signals it sees.

# Logic
# -----

def pw.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pw.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : pw.BD(_, Unit, A)
  Unit{}

def pw.or_true(a: Bool) -> {True{} == Bool.or(a, True{}) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def pw.le0(t: Nat) -> {True{} == Nat.is_le(0n, t) : Bool}:
  match t:
    case 0n:
      {==}
    case 1n+q:
      {==}

# a deadline of 0 ticks is reached, whatever came
def pw.reached0(+a: Bool, +c: Bool, t: Nat) -> {True{} == Bool.or(a, Bool.or(c, Nat.is_le(0n, t))) : Bool}:
  %pw.le0(t) : {True{} == Bool.or(a, Bool.or(c, _)) : Bool}
  %pw.or_true(c) : {True{} == Bool.or(a, _) : Bool}
  pw.or_true(a)

# the deadline, in ticks from now, of an open wait
def pw.up(l: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match l:
    case None{}:
      None{}
    case Some{m}:
      Some{1n+m}

# an ended wait reports nothing more
def pw.over(xs: List<&2, Wt.Sig>) -> {Nil{} == Wt.go(xs, Wt.Over{}) : List<&2, Wt.End>}:
  match xs:
    case Nil{}:
      {==}
    case s <> rest:
      pw.over(rest)
