# eukhe: the proof of LAW job_wait_never_settles_and_detaches
# The open with a spelled budget is the poll at rest (JWB.jwb.open). While
# the wait waits its replies are 0; a settled wait answers 1 forever (no
# 2 among its replies), a detached one 2 forever (no 1 among them).

import Base
import ../../bend/ffi_job_wait.bend as FJw
import ../../bend/job.bend as M
import ../../bend/wire.bend as Wr
import ../../laws/job_wait.bend as JobWait
import ./base.bend as JWB

def jwn.and_f(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# a settled wait never answers 2
def jwn.s2(es: List<&2, Maybe<&2, M.End>>) -> {JobWait.jw_has(JobWait.jw_feed(es, (FJw.Open{FJw.Final{M.Settles{}}}, FJw.put_turn(M.Settles{}))), Wr.put_nat(2n, "")) == False{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      match e:
        case None{}:
          jwn.s2(rest)
        case Some{x}:
          jwn.s2(rest)

# a detached wait never answers 1
def jwn.d1(es: List<&2, Maybe<&2, M.End>>) -> {JobWait.jw_has(JobWait.jw_feed(es, (FJw.Open{FJw.Final{M.Detaches{}}}, FJw.put_turn(M.Detaches{}))), Wr.put_nat(1n, "")) == False{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      match e:
        case None{}:
          jwn.d1(rest)
        case Some{x}:
          jwn.d1(rest)

def jwn.detached(+es: List<&2, Maybe<&2, M.End>>) -> {Bool.and(JobWait.jw_has(JobWait.jw_feed(es, (FJw.Open{FJw.Final{M.Detaches{}}}, FJw.put_turn(M.Detaches{}))), Wr.put_nat(1n, "")), JobWait.jw_has(JobWait.jw_feed(es, (FJw.Open{FJw.Final{M.Detaches{}}}, FJw.put_turn(M.Detaches{}))), Wr.put_nat(2n, ""))) == False{} : Bool}:
  %Equal.sym(Bool, JobWait.jw_has(JobWait.jw_feed(es, (FJw.Open{FJw.Final{M.Detaches{}}}, FJw.put_turn(M.Detaches{}))), Wr.put_nat(1n, "")), False{}, jwn.d1(es)) : {Bool.and(_, JobWait.jw_has(JobWait.jw_feed(es, (FJw.Open{FJw.Final{M.Detaches{}}}, FJw.put_turn(M.Detaches{}))), Wr.put_nat(2n, ""))) == False{} : Bool}
  {==}

def jwn.settled(+es: List<&2, Maybe<&2, M.End>>) -> {Bool.and(JobWait.jw_has(JobWait.jw_feed(es, (FJw.Open{FJw.Final{M.Settles{}}}, FJw.put_turn(M.Settles{}))), Wr.put_nat(1n, "")), JobWait.jw_has(JobWait.jw_feed(es, (FJw.Open{FJw.Final{M.Settles{}}}, FJw.put_turn(M.Settles{}))), Wr.put_nat(2n, ""))) == False{} : Bool}:
  %Equal.sym(Bool, JobWait.jw_has(JobWait.jw_feed(es, (FJw.Open{FJw.Final{M.Settles{}}}, FJw.put_turn(M.Settles{}))), Wr.put_nat(2n, "")), False{}, jwn.s2(es)) : {Bool.and(JobWait.jw_has(JobWait.jw_feed(es, (FJw.Open{FJw.Final{M.Settles{}}}, FJw.put_turn(M.Settles{}))), Wr.put_nat(1n, "")), _) == False{} : Bool}
  jwn.and_f(JobWait.jw_has(JobWait.jw_feed(es, (FJw.Open{FJw.Final{M.Settles{}}}, FJw.put_turn(M.Settles{}))), Wr.put_nat(1n, "")))

# from a wait with 1+p ticks left
def jwn.go(es: List<&2, Maybe<&2, M.End>>, +p: Nat) -> {Bool.and(JobWait.jw_has(JobWait.jw_feed(es, (FJw.Open{FJw.Waiting{1n+p}}, Wr.put_nat(0n, ""))), Wr.put_nat(1n, "")), JobWait.jw_has(JobWait.jw_feed(es, (FJw.Open{FJw.Waiting{1n+p}}, Wr.put_nat(0n, ""))), Wr.put_nat(2n, ""))) == False{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      match e:
        case None{}:
          match p:
            case 0n:
              jwn.detached(rest)
            case 1n+q:
              jwn.go(rest, q)
        case Some{x}:
          jwn.settled(rest)

def jwn.top(+b: Nat, es: List<&2, Maybe<&2, M.End>>) -> {Bool.and(JobWait.jw_has(JobWait.jw_feed(es, FJw.take(b, M.poll(Nat.is_eq(b, 0n), False{}))), Wr.put_nat(1n, "")), JobWait.jw_has(JobWait.jw_feed(es, FJw.take(b, M.poll(Nat.is_eq(b, 0n), False{}))), Wr.put_nat(2n, ""))) == False{} : Bool}:
  match b:
    case 0n:
      jwn.detached(es)
    case 1n+p:
      jwn.go(es, p)

def JobWait.job_wait_never_settles_and_detaches(b, fits, es):
  %Equal.sym(FJw.St & String, FJw.open(Wr.put_nat(b, "")), FJw.take(b, M.poll(Nat.is_eq(b, 0n), False{})), JWB.jwb.open(b, fits)) : {Bool.and(JobWait.jw_has(JobWait.jw_feed(es, _), Wr.put_nat(1n, "")), JobWait.jw_has(JobWait.jw_feed(es, _), Wr.put_nat(2n, ""))) == False{} : Bool}
  jwn.top(b, es)
