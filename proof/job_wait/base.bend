# eukhe: lemmas shared by the proofs of laws/job_wait.bend: the entry's
# turn after a poll is the laws' (jwb.take_poll), one event in any wait is
# the laws' step (jwb.step), the open with a spelled budget (jwb.open), a
# final wait answers its turn forever (jwb.final), a model wait with no
# budget left detaches whatever comes (jwb.zero), and the absurd premises.

import Base
import ../../bend/ffi_job_wait.bend as FJw
import ../../bend/job.bend as M
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/job.bend as Job
import ../../laws/job_wait.bend as JobWait
import ../base/wire.bend as LWire

# Absurd premises
# ---------------

def jwb.BB(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# True is not False
def jwb.tf(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : jwb.BB(_, G)
  Unit{}

def jwb.MB(m: Maybe<&2, Bool>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

# None is not Some (an event read)
def jwb.none_some(-G: Type, -x: Bool, e: {None{} == Some{x} : Maybe<&2, Bool>}) -> G:
  %e : jwb.MB(_, G)
  Unit{}

def jwb.MN(m: Maybe<&2, Nat>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

# None is not Some (a budget read)
def jwb.none_some_nat(-G: Type, -x: Nat, e: {None{} == Some{x} : Maybe<&2, Nat>}) -> G:
  %e : jwb.MN(_, G)
  Unit{}

def jwb.bool_of(m: Maybe<&2, Bool>, d: Bool) -> Bool:
  match m:
    case None{}:
      d
    case Some{x}:
      x

# Some is injective (an event read)
def jwb.some_inj(+a: Bool, +b: Bool, e: {Some{a} == Some{b} : Maybe<&2, Bool>}) -> {a == b : Bool}:
  Equal.cong(Maybe<&2, Bool>, Bool, m => jwb.bool_of(m, a), Some{a}, Some{b}, e)

def jwb.nat_of(m: Maybe<&2, Nat>, d: Nat) -> Nat:
  match m:
    case None{}:
      d
    case Some{x}:
      x

# Some is injective (a budget read)
def jwb.some_inj_nat(+a: Nat, +b: Nat, e: {Some{a} == Some{b} : Maybe<&2, Nat>}) -> {a == b : Nat}:
  Equal.cong(Maybe<&2, Nat>, Nat, m => jwb.nat_of(m, a), Some{a}, Some{b}, e)

# Turns
# -----

# the entry's wait after the model's poll is the laws' (the poll is
# Job.wt_poll_spec: job_wait_poll_exact)
def jwb.take_poll(left: Nat, d: Bool, r: Bool) -> {FJw.take(left, M.poll(d, r)) == JobWait.jw_after(left, Job.wt_poll_spec(d, r)) : FJw.St & String}:
  match d r:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# a tick in a wait with l ticks left is the laws' step
def jwb.tick(l: Nat) -> {FJw.step.wait(FJw.Waiting{l}, False{}) == JobWait.jw_step(FJw.Waiting{l}, False{}) : FJw.St & String}:
  match l:
    case 0n:
      {==}
    case 1n++p:
      jwb.take_poll(p, Nat.is_eq(p, 0n), False{})

# one event in any wait is the laws' step
def jwb.step(w: FJw.Wt, ready: Bool) -> {FJw.step.wait(w, ready) == JobWait.jw_step(w, ready) : FJw.St & String}:
  match w:
    case FJw.Waiting{+l}:
      match ready:
        case True{}:
          jwb.take_poll(l, Nat.is_eq(l, 0n), True{})
        case False{}:
          jwb.tick(l)
    case FJw.Final{t}:
      match t:
        case M.Waits{}:
          {==}
        case M.Settles{}:
          {==}
        case M.Detaches{}:
          {==}

# the open with a spelled budget that fits is the poll at rest
def jwb.open(+b: Nat, fits: {LawsBase.wire_fits(b) == True{} : Bool}) -> {FJw.open(Wr.put_nat(b, "")) == FJw.take(b, M.poll(Nat.is_eq(b, 0n), False{})) : FJw.St & String}:
  %LWire.pw6.nat(b, "", fits) : {FJw.open.go(_) == FJw.take(b, M.poll(Nat.is_eq(b, 0n), False{})) : FJw.St & String}
  {==}

# Runs
# ----

# a final wait answers its turn to every event
def jwb.final(es: List<&2, Maybe<&2, M.End>>, +t: M.Turn) -> {JobWait.jw_last(es, (FJw.Open{FJw.Final{t}}, FJw.put_turn(t))) == FJw.put_turn(t) : String}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      match e:
        case None{}:
          jwb.final(rest, t)
        case Some{x}:
          jwb.final(rest, t)

# no count is below zero
def jwb.lt_zero(n: Nat) -> {Nat.is_lt(n, 0n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# the model's wait with no budget left detaches, whatever comes
def jwb.zero(xs: List<&2, M.JEv>) -> {M.wait(xs, 0n) == Some{M.Detached{}} : Maybe<&2, M.Wait>}:
  match xs:
    case Nil{}:
      {==}
    case e <> rest:
      match e:
        case M.Out{n}:
          {==}
        case M.Quit{c}:
          {==}
        case M.Kill{}:
          {==}
        case M.Tick{}:
          {==}
