# eukhe: lemmas the proofs of area wait share

import Base
import ../../bend/wait.bend as Wt
import ../../bend/ffi_wait.bend as FWt
import ../../bend/wire.bend as Wr
import ../../laws/wait.bend as WaitLaws

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

# The entry (bend/ffi_wait.bend)
# ------------------------------
# The entry reads every input as the laws' reader does (`ww.read`); the
# end it spells for a poll is the laws' (`ww.ans`, eight cases).

def ww.late(w: Bool, c: Bool, r: Wr.Dec<Bool>) -> {WaitLaws.ww_read.late(w, c, r) == FWt.get_ready.late(w, c, r) : Wr.Dec<Wt.Polled>}:
  match r:
    case Wr.Got{l, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ww.cancel(w: Bool, r: Wr.Dec<Bool>) -> {WaitLaws.ww_read.cancel(w, r) == FWt.get_ready.cancel(w, r) : Wr.Dec<Wt.Polled>}:
  match r:
    case Wr.Got{c, s}:
      ww.late(w, c, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

# the entry reads every input as the laws' reader does
def ww.read(r: Wr.Dec<Bool>) -> {WaitLaws.ww_read.go(r) == FWt.get_ready.go(r) : Wr.Dec<Wt.Polled>}:
  match r:
    case Wr.Got{w, s}:
      ww.cancel(w, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

# the entry spells the laws' end for every poll
def ww.ans(r: Wt.Polled) -> {FWt.put_end(Wt.poll(r)) == WaitLaws.ww_spell_end(WaitLaws.ww_end(r)) : String}:
  match r:
    case Wt.Polled{w, c, l}:
      match w c l:
        case True{} True{} True{}:
          {==}
        case True{} True{} False{}:
          {==}
        case True{} False{} True{}:
          {==}
        case True{} False{} False{}:
          {==}
        case False{} True{} True{}:
          {==}
        case False{} True{} False{}:
          {==}
        case False{} False{} True{}:
          {==}
        case False{} False{} False{}:
          {==}

def ww.MD(m: Maybe<&2, Wt.Polled>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

# None is not Some
def ww.none_some(-A: Type, -r: Wt.Polled, h: {None{} == Some{r} : Maybe<&2, Wt.Polled>}) -> A:
  %h : ww.MD(_, A)
  Unit{}

def ww.get(m: Maybe<&2, Wt.Polled>, d: Wt.Polled) -> Wt.Polled:
  match m:
    case None{}:
      d
    case Some{x}:
      x

# Some is injective
def ww.some_inj(+a: Wt.Polled, +b: Wt.Polled, h: {Some{a} == Some{b} : Maybe<&2, Wt.Polled>}) -> {a == b : Wt.Polled}:
  Equal.cong(Maybe<&2, Wt.Polled>, Wt.Polled, m => ww.get(m, a), Some{a}, Some{b}, h)
