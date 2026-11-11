# eukhe: the desk restated for the proofs of laws/auth_flight/: the
# shape the safety proofs case-split on (af_desk, helper for helper the
# desk of bend/auth_flight.bend section The desk the Rust runs), proven
# equal to F.desk.step by LAE.ae.desk (base/entry.bend). Not a law and
# not a spec: no law states anything through it.

import Base
import ../../../bend/auth_flight.bend as F
import ../../../laws/auth_flight/entry.bend as S

def af_set.pick(hit: Bool, x: F.Cl, +a: F.At, t: List<&2, F.Cl>, r: List<&2, F.Cl>) -> List<&2, F.Cl>:
  match hit:
    case True{}:
      match x:
        case F.Cl{j, p, o}:
          F.Cl{j, p, a} <> t
    case False{}:
      x <> r

# the callers with the first numbered k standing at a
def af_set(+k: Nat, +a: F.At, cs: List<&2, F.Cl>) -> List<&2, F.Cl>:
  match cs:
    case Nil{}:
      Nil{}
    case x <> +t:
      match x:
        case F.Cl{+j, +p, +o}:
          af_set.pick(Nat.is_eq(j, k), F.Cl{j, p, o}, a, t, af_set(k, a, t))

def af_cut.pick(hit: Bool, x: F.Cl, t: List<&2, F.Cl>, r: List<&2, F.Cl>) -> List<&2, F.Cl>:
  match hit:
    case True{}:
      t
    case False{}:
      x <> r

# the callers without the first numbered k
def af_cut(+k: Nat, cs: List<&2, F.Cl>) -> List<&2, F.Cl>:
  match cs:
    case Nil{}:
      Nil{}
    case x <> +t:
      match x:
        case F.Cl{+j, +p, +o}:
          af_cut.pick(Nat.is_eq(j, k), F.Cl{j, p, o}, t, af_cut(k, t))

def af_unwait.pick(hit: Bool, x: F.Cl, r: List<&2, F.Cl>) -> List<&2, F.Cl>:
  match hit:
    case True{}:
      r
    case False{}:
      x <> r

# the callers without those waiting on p's flight
def af_unwait(+p: String, cs: List<&2, F.Cl>) -> List<&2, F.Cl>:
  match cs:
    case Nil{}:
      Nil{}
    case +x <> t:
      af_unwait.pick(S.af_waits(p, x), x, af_unwait(p, t))

def af_wake.pick(hit: Bool, x: F.Cl, +a: F.Act, r: List<&2, F.To>) -> List<&2, F.To>:
  match hit:
    case True{}:
      match x:
        case F.Cl{j, q, o}:
          F.To{j, a} <> r
    case False{}:
      r

# each caller waiting on p's flight, in order, does a
def af_wake(+p: String, +a: F.Act, cs: List<&2, F.Cl>) -> List<&2, F.To>:
  match cs:
    case Nil{}:
      Nil{}
    case +x <> t:
      af_wake.pick(S.af_waits(p, x), x, a, af_wake(p, a, t))

# how many wait on p's flight
def af_joined(+p: String, cs: List<&2, F.Cl>) -> Nat:
  match cs:
    case Nil{}:
      0n
    case +x <> t:
      Nat.add(S.af_bit(S.af_waits(p, x)), af_joined(p, t))

# the leader k of p's flight lands it: k, then each caller waiting on the
# flight, is done with this event's payload, and all of them leave
def af_land(+k: Nat, +p: String, cs: List<&2, F.Cl>, n: Nat) -> F.DRes:
  +rest = af_cut(k, cs)
  F.DRes{F.Desk{af_unwait(p, rest), n}, F.Acts{F.To{k, F.DoDone{}} <> af_wake(p, F.DoDone{}, rest)}}

# caller k's credential expired: it joins p's flight in flight (fl) and
# waits, or leads a new one and checks
def af_board(fl: Bool, +k: Nat, cs: List<&2, F.Cl>, n: Nat) -> F.DRes:
  match fl:
    case True{}:
      F.DRes{F.Desk{af_set(k, F.Waits{}, cs), n}, F.Acts{[F.To{k, F.DoWait{}}]}}
    case False{}:
      F.DRes{F.Desk{af_set(k, F.Checks{}, cs), n}, F.Acts{[F.To{k, F.DoCheck{}}]}}

# caller k of p found fd at the step it is on: a fresh credential at the
# load, or no refresh at all, is done and leaves; an expired one joins p's
# flight in flight (wait) or leads a new one (check); the check lands on a
# fresh credential and fetches otherwise; a fetched credential is stored,
# a failed fetch lands; the store's outcome lands
def af_found(fd: F.Fd, +k: Nat, +p: String, +cs: List<&2, F.Cl>, +n: Nat) -> F.DRes:
  match fd:
    case F.LoadFresh{}:
      F.DRes{F.Desk{af_cut(k, cs), n}, F.Acts{[F.To{k, F.DoDone{}}]}}
    case F.LoadExpired{}:
      af_board(S.af_inflight(p, cs), k, cs, n)
    case F.LoadFailed{}:
      F.DRes{F.Desk{af_cut(k, cs), n}, F.Acts{[F.To{k, F.DoDone{}}]}}
    case F.CheckFresh{}:
      af_land(k, p, cs, n)
    case F.CheckExpired{}:
      F.DRes{F.Desk{af_set(k, F.Fetches{}, cs), n}, F.Acts{[F.To{k, F.DoFetch{}}]}}
    case F.FetchOk{}:
      F.DRes{F.Desk{af_set(k, F.Stores{}, cs), n}, F.Acts{[F.To{k, F.DoStore{}}]}}
    case F.FetchFailed{}:
      af_land(k, p, cs, n)
    case F.Stored{}:
      af_land(k, p, cs, n)

def af_found_fit(fit: Bool, fd: F.Fd, +k: Nat, +p: String, +cs: List<&2, F.Cl>, +n: Nat) -> F.DRes:
  match fit:
    case True{}:
      af_found(fd, k, p, cs, n)
    case False{}:
      F.DRes{F.Desk{cs, n}, F.Off{}}

def af_found_at(m: Maybe<&2, F.Cl>, +fd: F.Fd, +k: Nat, +cs: List<&2, F.Cl>, +n: Nat) -> F.DRes:
  match m:
    case None{}:
      F.DRes{F.Desk{cs, n}, F.Off{}}
    case Some{x}:
      match x:
        case F.Cl{j, p, a}:
          af_found_fit(S.af_takes(a, fd), fd, k, p, cs, n)

# caller k of p unwinds: a leader's flight lands with S.af_gone(p), served
# to each caller waiting on it, who leave with it; any other caller just
# leaves
def af_unwind_lead(lead: Bool, +k: Nat, +p: String, cs: List<&2, F.Cl>, n: Nat) -> F.DRes:
  match lead:
    case True{}:
      +rest = af_cut(k, cs)
      F.DRes{F.Desk{af_unwait(p, rest), n}, F.Acts{af_wake(p, F.DoFail{S.af_gone(p)}, rest)}}
    case False{}:
      F.DRes{F.Desk{af_cut(k, cs), n}, F.Acts{Nil{}}}

def af_unwind_at(m: Maybe<&2, F.Cl>, +k: Nat, +cs: List<&2, F.Cl>, +n: Nat) -> F.DRes:
  match m:
    case None{}:
      F.DRes{F.Desk{cs, n}, F.Off{}}
    case Some{x}:
      match x:
        case F.Cl{j, p, a}:
          af_unwind_lead(S.af_leads(a), k, p, cs, n)

def af_joiners(fl: Bool, +p: String, cs: List<&2, F.Cl>) -> Maybe<&2, Nat>:
  match fl:
    case True{}:
      Some{af_joined(p, cs)}
    case False{}:
      None{}

# the desk after event e, and its answer: an arrival is caller n (the
# next number), asked to load, newest first; a found or an unwind of a
# live caller as above; one naming no live caller, or a found the
# caller's step does not give, is out of turn and keeps the desk;
# joiners counts the callers waiting on p's flight, none when p has no
# flight in flight
def af_desk(d: F.Desk, e: F.DEv) -> F.DRes:
  match d:
    case F.Desk{+cs, +n}:
      match e:
        case F.Comes{p}:
          F.DRes{F.Desk{F.Cl{n, p, F.Loads{}} <> cs, 1n+n}, F.Acts{[F.To{n, F.DoLoad{}}]}}
        case F.Found{+k, fd}:
          af_found_at(S.af_find(k, cs), fd, k, cs, n)
        case F.Unwinds{+k}:
          af_unwind_at(S.af_find(k, cs), k, cs, n)
        case F.Joiners{+p}:
          F.DRes{F.Desk{cs, n}, F.Joined{af_joiners(S.af_inflight(p, cs), p, cs)}}
