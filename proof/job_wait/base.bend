# eukhe: lemmas shared by the proofs of laws/job_wait.bend: the open with
# a spelled budget (jwb.open), a final wait answers its turn forever
# (jwb.final), a model wait with no budget left detaches whatever comes
# (jwb.zero), a turn's reply and a wait's reply never open with 'E'
# (jwb.take_ok, jwb.wait_ok), and the absurd premises.

import Base
import ../../bend/ffi_job_wait.bend as FJw
import ../../bend/job.bend as M
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/job_wait.bend as JobWait
import ../base/wire.bend as LWire
import ../wire/wire_nat_not_err.bend as PWireNatNotErr

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

# Replies
# -------

# the reply of the wait after any turn is a Nat: never 'E'
def jwb.take_ok(+l: Nat, t: M.Turn) -> {LawsBase.wire_opens_err(JobWait.jw_reply(FJw.take(l, t))) == False{} : Bool}:
  match t:
    case M.Waits{}:
      Wire.wire_nat_not_err(0n, "")
    case M.Settles{}:
      Wire.wire_nat_not_err(1n, "")
    case M.Detaches{}:
      Wire.wire_nat_not_err(2n, "")

# the reply of a tick with l ticks left is a Nat: never 'E'
def jwb.tick_ok(l: Nat) -> {LawsBase.wire_opens_err(JobWait.jw_reply(FJw.tick(l))) == False{} : Bool}:
  match l:
    case 0n:
      jwb.take_ok(0n, M.poll(True{}, False{}))
    case 1n++q:
      jwb.take_ok(q, M.poll(Nat.is_eq(q, 0n), False{}))

# the reply of one event in any wait is a Nat: never 'E'
def jwb.wait_ok(w: FJw.Wt, ready: Bool) -> {LawsBase.wire_opens_err(JobWait.jw_reply(FJw.step.wait(w, ready))) == False{} : Bool}:
  match w:
    case FJw.Waiting{+l}:
      match ready:
        case True{}:
          jwb.take_ok(l, M.poll(Nat.is_eq(l, 0n), True{}))
        case False{}:
          jwb.tick_ok(l)
    case FJw.Final{t}:
      match t:
        case M.Waits{}:
          Wire.wire_nat_not_err(0n, "")
        case M.Settles{}:
          Wire.wire_nat_not_err(1n, "")
        case M.Detaches{}:
          Wire.wire_nat_not_err(2n, "")

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
