# eukhe: the laws of area auth_flight: the desk's entry, event by event

import Base
import ../../bend/auth_flight.bend as F
import ../../bend/ffi_auth_flight.bend as FA
import ../../bend/wire.bend as Wr
import ../base.bend as LawsBase

# (A1) The desk the Rust refresh runs, as compiled Bend
# -----------------------------------------------------
# The Rust refresh (crates/eukhe-core/src/auth/flight.rs) is an event loop
# with no policy: one stepper (bend/ffi_auth_flight.bend) per auth
# document behind a mutex; each caller's thread sends it its caller's
# events in the order they come and delivers each (caller, act) pair of
# the reply to that caller's mailbox. These laws pin every reply for every
# desk and every input (the spec below spells events and replies with the
# wire primitives, never with the entry's codec, and states the desk on
# its own), tie each caller's next act to the model's step
# (flight_step_is_model), and state what no order of events breaks: one
# leader and one fetch per provider, no caller waiting on a flight nobody
# leads, every caller of a flight served the landing event's payload, one
# end per caller and nothing after it. The laws over many events run the
# desk the entry steps (F.desk.step) over any list of events: every input
# string steps it as the event it reads, or keeps it (flight_step_reads,
# flight_step_malformed_exact), so they hold for every byte sequence the
# host sends. The grammar, restated from the entry's header:
#
#   open    the empty input                                 reply: empty
#   Ev      0 arrive (provider: String) | 1 found (caller: Nat, what: Nat)
#           | 2 unwind (caller: Nat) | 3 joiners (provider: String)
#   what    0 load fresh | 1 load expired | 2 load failed | 3 check fresh
#           | 4 check expired | 5 fetch ok | 6 fetch failed | 7 stored
#   reply   to 0, 1, 2: List of (caller: Nat, Act); to 3: Maybe<Nat>
#   Act     0 load | 1 check | 2 fetch | 3 store | 4 wait | 5 done
#           | 6 failed (text: String)
#   errors  "auth_flight: out of turn", "auth_flight: malformed event"
#           (the desk kept), "auth_flight: malformed open",
#           "auth_flight: the open was refused"

# 1 for True, 0 for False
def af_bit(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# Spelling

# what a found is on the wire
def af_what(fd: F.Fd) -> Nat:
  match fd:
    case F.LoadFresh{}:
      0n
    case F.LoadExpired{}:
      1n
    case F.LoadFailed{}:
      2n
    case F.CheckFresh{}:
      3n
    case F.CheckExpired{}:
      4n
    case F.FetchOk{}:
      5n
    case F.FetchFailed{}:
      6n
    case F.Stored{}:
      7n

# the event Rust writes
def af_spell_ev(e: F.DEv) -> String:
  match e:
    case F.Comes{p}:
      Wr.put_nat(0n, Wr.put_str(p, ""))
    case F.Found{k, fd}:
      Wr.put_nat(1n, Wr.put_nat(k, Wr.put_nat(af_what(fd), "")))
    case F.Unwinds{k}:
      Wr.put_nat(2n, Wr.put_nat(k, ""))
    case F.Joiners{p}:
      Wr.put_nat(3n, Wr.put_str(p, ""))

# its provider's length or its caller fits the wire
def af_ev_fits(e: F.DEv) -> Bool:
  match e:
    case F.Comes{p}:
      LawsBase.wire_fits(String.length(p))
    case F.Found{k, fd}:
      LawsBase.wire_fits(k)
    case F.Unwinds{k}:
      LawsBase.wire_fits(k)
    case F.Joiners{p}:
      LawsBase.wire_fits(String.length(p))

def af_spell_act(a: F.Act, rest: String) -> String:
  match a:
    case F.DoLoad{}:
      Wr.put_nat(0n, rest)
    case F.DoCheck{}:
      Wr.put_nat(1n, rest)
    case F.DoFetch{}:
      Wr.put_nat(2n, rest)
    case F.DoStore{}:
      Wr.put_nat(3n, rest)
    case F.DoWait{}:
      Wr.put_nat(4n, rest)
    case F.DoDone{}:
      Wr.put_nat(5n, rest)
    case F.DoFail{e}:
      Wr.put_nat(6n, Wr.put_str(e, rest))

def af_spell_tos(xs: List<&2, F.To>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      match x:
        case F.To{k, a}:
          Wr.put_nat(k, af_spell_act(a, af_spell_tos(t, rest)))

# the reply Rust reads: the pairs (their count, then each caller and its
# act); the count of the callers waiting on a flight (0 for none, 1 and
# the count); out of turn: exactly the error form
def af_spell_out(o: F.DOut) -> String:
  match o:
    case F.Acts{+xs}:
      Wr.put_nat(List.length(&2, F.To, xs), af_spell_tos(xs, ""))
    case F.Joined{j}:
      match j:
        case None{}:
          Wr.put_nat(0n, "")
        case Some{n}:
          Wr.put_nat(1n, Wr.put_nat(n, ""))
    case F.Off{}:
      Wr.err("auth_flight: out of turn")

# Reading

def af_read_ev.what(k: Nat, t: Nat, s: String) -> Wr.Dec<F.DEv>:
  match t:
    case 0n:
      Wr.Got{F.Found{k, F.LoadFresh{}}, s}
    case 1n:
      Wr.Got{F.Found{k, F.LoadExpired{}}, s}
    case 2n:
      Wr.Got{F.Found{k, F.LoadFailed{}}, s}
    case 3n:
      Wr.Got{F.Found{k, F.CheckFresh{}}, s}
    case 4n:
      Wr.Got{F.Found{k, F.CheckExpired{}}, s}
    case 5n:
      Wr.Got{F.Found{k, F.FetchOk{}}, s}
    case 6n:
      Wr.Got{F.Found{k, F.FetchFailed{}}, s}
    case 7n:
      Wr.Got{F.Found{k, F.Stored{}}, s}
    case 8n+q:
      Wr.Bad{}

def af_read_ev.found(k: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<F.DEv>:
  match r:
    case Wr.Got{t, s}:
      af_read_ev.what(k, t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def af_read_ev.caller(r: Wr.Dec<Nat>) -> Wr.Dec<F.DEv>:
  match r:
    case Wr.Got{k, s}:
      af_read_ev.found(k, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def af_read_ev.unwind(r: Wr.Dec<Nat>) -> Wr.Dec<F.DEv>:
  match r:
    case Wr.Got{k, s}:
      Wr.Got{F.Unwinds{k}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def af_read_ev.comes(r: Wr.Dec<String>) -> Wr.Dec<F.DEv>:
  match r:
    case Wr.Got{p, s}:
      Wr.Got{F.Comes{p}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def af_read_ev.joiners(r: Wr.Dec<String>) -> Wr.Dec<F.DEv>:
  match r:
    case Wr.Got{p, s}:
      Wr.Got{F.Joiners{p}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def af_read_ev.tag(t: Nat, s: String) -> Wr.Dec<F.DEv>:
  match t:
    case 0n:
      af_read_ev.comes(Wr.get_str(s))
    case 1n:
      af_read_ev.caller(Wr.get_nat(s))
    case 2n:
      af_read_ev.unwind(Wr.get_nat(s))
    case 3n:
      af_read_ev.joiners(Wr.get_str(s))
    case 4n+p:
      Wr.Bad{}

def af_read_ev.go(r: Wr.Dec<Nat>) -> Wr.Dec<F.DEv>:
  match r:
    case Wr.Got{t, s}:
      af_read_ev.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def af_whole(-A: Data, whole: Bool, x: A) -> Maybe<&2, A>:
  match whole:
    case True{}:
      Some{x}
    case False{}:
      None{}

def af_read_ev.whole(r: Wr.Dec<F.DEv>) -> Maybe<&2, F.DEv>:
  match r:
    case Wr.Got{e, s}:
      af_whole(F.DEv, Wr.end(s), e)
    case Wr.Bad{}:
      None{}

# the event s is, when s is exactly one event
def af_read_ev(s: String) -> Maybe<&2, F.DEv>:
  af_read_ev.whole(af_read_ev.go(Wr.get_nat(s)))

# The desk, stated on its own

# a caller at a leads its provider's flight (at its check, fetch or store)
def af_leads(a: F.At) -> Bool:
  match a:
    case F.Loads{}:
      False{}
    case F.Checks{}:
      True{}
    case F.Fetches{}:
      True{}
    case F.Stores{}:
      True{}
    case F.Waits{}:
      False{}

# the step a caller at a is on: 0 its load, 1 its check, 2 its fetch, 3
# its store, 4 none (it waits)
def af_stage(a: F.At) -> Nat:
  match a:
    case F.Loads{}:
      0n
    case F.Checks{}:
      1n
    case F.Fetches{}:
      2n
    case F.Stores{}:
      3n
    case F.Waits{}:
      4n

# the step a found comes from
def af_fd_stage(fd: F.Fd) -> Nat:
  match fd:
    case F.LoadFresh{}:
      0n
    case F.LoadExpired{}:
      0n
    case F.LoadFailed{}:
      0n
    case F.CheckFresh{}:
      1n
    case F.CheckExpired{}:
      1n
    case F.FetchOk{}:
      2n
    case F.FetchFailed{}:
      2n
    case F.Stored{}:
      3n

# a caller at a takes fd: fd comes from the step it is on
def af_takes(a: F.At, fd: F.Fd) -> Bool:
  Nat.is_eq(af_stage(a), af_fd_stage(fd))

# a found that lands the leader's flight: a fresh credential at the
# check, a failed fetch, the store's outcome
def af_lands(a: F.At, fd: F.Fd) -> Bool:
  match a:
    case F.Loads{}:
      False{}
    case F.Checks{}:
      match fd:
        case F.LoadFresh{}:
          False{}
        case F.LoadExpired{}:
          False{}
        case F.LoadFailed{}:
          False{}
        case F.CheckFresh{}:
          True{}
        case F.CheckExpired{}:
          False{}
        case F.FetchOk{}:
          False{}
        case F.FetchFailed{}:
          False{}
        case F.Stored{}:
          False{}
    case F.Fetches{}:
      match fd:
        case F.LoadFresh{}:
          False{}
        case F.LoadExpired{}:
          False{}
        case F.LoadFailed{}:
          False{}
        case F.CheckFresh{}:
          False{}
        case F.CheckExpired{}:
          False{}
        case F.FetchOk{}:
          False{}
        case F.FetchFailed{}:
          True{}
        case F.Stored{}:
          False{}
    case F.Stores{}:
      match fd:
        case F.LoadFresh{}:
          False{}
        case F.LoadExpired{}:
          False{}
        case F.LoadFailed{}:
          False{}
        case F.CheckFresh{}:
          False{}
        case F.CheckExpired{}:
          False{}
        case F.FetchOk{}:
          False{}
        case F.FetchFailed{}:
          False{}
        case F.Stored{}:
          True{}
    case F.Waits{}:
      False{}

def af_find.pick(hit: Bool, x: F.Cl, r: Maybe<&2, F.Cl>) -> Maybe<&2, F.Cl>:
  match hit:
    case True{}:
      Some{x}
    case False{}:
      r

# the first live caller numbered k
def af_find(+k: Nat, cs: List<&2, F.Cl>) -> Maybe<&2, F.Cl>:
  match cs:
    case Nil{}:
      None{}
    case x <> t:
      match x:
        case F.Cl{+j, +p, +a}:
          af_find.pick(Nat.is_eq(j, k), F.Cl{j, p, a}, af_find(k, t))

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

# x waits on the flight of provider p
def af_waits(+p: String, x: F.Cl) -> Bool:
  match x:
    case F.Cl{j, q, a}:
      match a:
        case F.Loads{}:
          False{}
        case F.Checks{}:
          False{}
        case F.Fetches{}:
          False{}
        case F.Stores{}:
          False{}
        case F.Waits{}:
          String.eq(q, p)

# x leads the flight of provider p
def af_lead(+p: String, x: F.Cl) -> Bool:
  match x:
    case F.Cl{j, q, a}:
      Bool.and(af_leads(a), String.eq(q, p))

# provider p has a flight in flight: a live caller leads it
def af_inflight(+p: String, cs: List<&2, F.Cl>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case +x <> t:
      Bool.or(af_lead(p, x), af_inflight(p, t))

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
      af_unwait.pick(af_waits(p, x), x, af_unwait(p, t))

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
      af_wake.pick(af_waits(p, x), x, a, af_wake(p, a, t))

# how many wait on p's flight
def af_joined(+p: String, cs: List<&2, F.Cl>) -> Nat:
  match cs:
    case Nil{}:
      0n
    case +x <> t:
      Nat.add(af_bit(af_waits(p, x)), af_joined(p, t))

# the failure served to the callers waiting on p's flight when its leader
# unwinds with no outcome
def af_gone(p: String) -> String:
  String.append("the token refresh of ", String.append(p, " ended without an outcome"))

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
      af_board(af_inflight(p, cs), k, cs, n)
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
          af_found_fit(af_takes(a, fd), fd, k, p, cs, n)

# caller k of p unwinds: a leader's flight lands with af_gone(p), served
# to each caller waiting on it, who leave with it; any other caller just
# leaves
def af_unwind_lead(lead: Bool, +k: Nat, +p: String, cs: List<&2, F.Cl>, n: Nat) -> F.DRes:
  match lead:
    case True{}:
      +rest = af_cut(k, cs)
      F.DRes{F.Desk{af_unwait(p, rest), n}, F.Acts{af_wake(p, F.DoFail{af_gone(p)}, rest)}}
    case False{}:
      F.DRes{F.Desk{af_cut(k, cs), n}, F.Acts{Nil{}}}

def af_unwind_at(m: Maybe<&2, F.Cl>, +k: Nat, +cs: List<&2, F.Cl>, +n: Nat) -> F.DRes:
  match m:
    case None{}:
      F.DRes{F.Desk{cs, n}, F.Off{}}
    case Some{x}:
      match x:
        case F.Cl{j, p, a}:
          af_unwind_lead(af_leads(a), k, p, cs, n)

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
          af_found_at(af_find(k, cs), fd, k, cs, n)
        case F.Unwinds{+k}:
          af_unwind_at(af_find(k, cs), k, cs, n)
        case F.Joiners{+p}:
          F.DRes{F.Desk{cs, n}, F.Joined{af_joiners(af_inflight(p, cs), p, cs)}}

def af_step_of(r: F.DRes) -> FA.St & String:
  match r:
    case F.DRes{d, o}:
      (FA.Open{d}, af_spell_out(o))

# The model's next leg, as the act the desk answers

# the act of a model leg: a land is done in the same event (the desk
# lands inside it); a board is never a caller's next act (the desk boards
# inside the event that found the credential expired)
def af_leg_act(l: F.Leg) -> F.Act:
  match l:
    case F.Load{}:
      F.DoLoad{}
    case F.Board{}:
      F.DoLoad{}
    case F.Check{f}:
      F.DoCheck{}
    case F.Fetch{f}:
      F.DoFetch{}
    case F.Store{f, c}:
      F.DoStore{}
    case F.Land{f, o}:
      F.DoDone{}
    case F.Waiting{f}:
      F.DoWait{}
    case F.Served{v, o}:
      F.DoDone{}

# the model's next leg after the step that found fd, in the world w with
# its store at credential c (fresh or expired as fd found it), on flight f;
# fl: the provider has a flight in flight (an expired load boards). The
# model has no failed load: a load that found no refresh can start is
# done with what it found.
def af_model_fd(fd: F.Fd, fl: Bool, +c: Nat, +f: Nat, +w: F.W) -> F.Act:
  match fd:
    case F.LoadFresh{}:
      af_leg_act(F.Adv.l(F.adv.load(F.Sto{c, True{}}, w)))
    case F.LoadExpired{}:
      af_leg_act(F.Adv.l(F.adv.board(F.W{F.Sto{c, False{}}, fl, F.W.landed(w), F.W.n(w)})))
    case F.LoadFailed{}:
      F.DoDone{}
    case F.CheckFresh{}:
      af_leg_act(F.Adv.l(F.adv.check(f, F.Sto{c, True{}}, w)))
    case F.CheckExpired{}:
      af_leg_act(F.Adv.l(F.adv.check(f, F.Sto{c, False{}}, w)))
    case F.FetchOk{}:
      af_leg_act(F.Adv.l(F.adv.fetch(f, w, True{})))
    case F.FetchFailed{}:
      af_leg_act(F.Adv.l(F.adv.fetch(f, w, False{})))
    case F.Stored{}:
      af_leg_act(F.Adv.l(F.adv.store(f, c, w)))

# the live callers of a desk
def af_cs(d: F.Desk) -> List<&2, F.Cl>:
  match d:
    case F.Desk{cs, n}:
      cs

def af_reply(r: FA.St & String) -> String:
  match r:
    case (st, out):
      out

# every reply, from the state and reply r through the inputs ins
def af_feed(ins: List<&2, String>, r: FA.St & String) -> List<&2, String>:
  match ins:
    case Nil{}:
      (st, out) = r
      [out]
    case i <> t:
      (st, out) = r
      out <> af_feed(t, FA.step(st, i))

# e names no live caller of cs, or a found its caller's step does not give
def af_off.at(m: Maybe<&2, F.Cl>, fd: F.Fd) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      match x:
        case F.Cl{j, p, a}:
          Bool.not(af_takes(a, fd))

def af_off(e: F.DEv, +cs: List<&2, F.Cl>) -> Bool:
  match e:
    case F.Comes{p}:
      False{}
    case F.Found{k, fd}:
      af_off.at(af_find(k, cs), fd)
    case F.Unwinds{k}:
      Maybe.is_none(&2, F.Cl, af_find(k, cs))
    case F.Joiners{p}:
      False{}

# the unwind of caller k of p, standing where a leader does (lead) or not
def af_unwound(lead: Bool, +k: Nat, +p: String, +cs: List<&2, F.Cl>, n: Nat) -> FA.St & String:
  match lead:
    case True{}:
      (FA.Open{F.Desk{af_unwait(p, af_cut(k, cs)), n}}, af_spell_out(F.Acts{af_wake(p, F.DoFail{af_gone(p)}, af_cut(k, cs))}))
    case False{}:
      (FA.Open{F.Desk{af_cut(k, cs), n}}, Wr.put_nat(0n, ""))

# Laws: the entry

# LAW flight_open_empty: the stepper opens on the empty input with an
# empty desk (no caller, the next caller numbered 0) and the empty reply
# EXCLUDES: a desk that starts with callers, or numbers from another start
law flight_open_empty:
  {FA.open("") == (FA.Open{F.Desk{Nil{}, 0n}}, "") : FA.St & String}

# LAW flight_open_refuses: any other open is refused with exactly the
# error form, and the refused stepper answers every event with exactly the
# error form
# EXCLUDES: a desk opened on input Rust never writes, a refused stepper
#   that decides
law flight_open_refuses:
  for +s: String
  for ne: {String.is_empty(s) == False{} : Bool}
  for +e: String
  {FA.open(s) == (FA.Shut{}, SCon{'E', SCon{' ', "auth_flight: malformed open"}}) : FA.St & String} & {FA.step(FA.Shut{}, e) == (FA.Shut{}, SCon{'E', SCon{' ', "auth_flight: the open was refused"}}) : FA.St & String}

# LAW flight_step_answers: on every event Rust writes (within the wire),
# from every desk, the stepper's desk and reply are the desk's (af_desk),
# spelled
# EXCLUDES: a misread event, caller, provider or found; a board that leads
#   while the provider is in flight or joins while it is not; a land that
#   keeps a caller of the flight, wakes another provider's caller or
#   serves another payload; an unwind that strands the joiners or wakes
#   others; a caller number reused; an out-of-turn event that changes the
#   desk; a wrong count; a reply in another order or tag
law flight_step_answers:
  for +d: F.Desk
  for +e: F.DEv
  for fits: {af_ev_fits(e) == True{} : Bool}
  {FA.step(FA.Open{d}, af_spell_ev(e)) == af_step_of(af_desk(d, e)) : FA.St & String}

# LAW flight_desk_is_entry: the desk the safety laws run (F.desk.step) is
# the laws' desk (af_desk), the one the entry's step is pinned to
# (flight_step_answers, flight_step_reads), for every desk and every
# event: the laws over runs of F.desk.step speak of the desk the entry
# steps
# EXCLUDES: safety laws made vacuous by a F.desk.step the entry does not
#   run (a desk that never changes while the entry steps another one)
law flight_desk_is_entry:
  for +d: F.Desk
  for +e: F.DEv
  {F.desk.step(d, e) == af_desk(d, e) : F.DRes}

# LAW flight_step_reads: every input that is exactly one event (as the
# wire primitives read it) steps the desk as that event
# EXCLUDES: a decision on another reading of the input
law flight_step_reads:
  for +d: F.Desk
  for +s: String
  for +e: F.DEv
  for got: {af_read_ev(s) == Some{e} : Maybe<&2, F.DEv>}
  {FA.step(FA.Open{d}, s) == af_step_of(af_desk(d, e)) : FA.St & String}

# LAW flight_step_malformed_exact: every input that is not exactly one
# event keeps the desk and answers exactly the error form 'E ', then
# "auth_flight: malformed event"
# EXCLUDES: a guessed event, a desk changed by garbage, an event with
#   input after it decided
law flight_step_malformed_exact:
  for +d: F.Desk
  for +s: String
  for no: {af_read_ev(s) == None{} : Maybe<&2, F.DEv>}
  {FA.step(FA.Open{d}, s) == (FA.Open{d}, SCon{'E', SCon{' ', "auth_flight: malformed event"}}) : FA.St & String}

# LAW flight_step_unknown_tag: an event tag past 3, or a found past 7
# (any number of digits, whatever follows), keeps the desk and answers
# exactly the malformed-event error form
# EXCLUDES: an unknown event read as a known one, an unknown found read
#   as a known one (a failure read as a credential)
law flight_step_unknown_tag:
  for +d: F.Desk
  for +n: Nat
  for +rest: String
  for +k: Nat
  for fits: {LawsBase.wire_fits(k) == True{} : Bool}
  {FA.step(FA.Open{d}, Wr.put_nat(4n+n, rest)) == (FA.Open{d}, SCon{'E', SCon{' ', "auth_flight: malformed event"}}) : FA.St & String} & {FA.step(FA.Open{d}, Wr.put_nat(1n, Wr.put_nat(k, Wr.put_nat(8n+n, rest)))) == (FA.Open{d}, SCon{'E', SCon{' ', "auth_flight: malformed event"}}) : FA.St & String}

# Laws: one event

# LAW flight_step_is_model: when a live caller reports what its read,
# fetch or write found at the step it is on, the reply's first pair tells
# that caller the model's next leg after that step (adv.load, adv.board,
# adv.check, adv.fetch, adv.store), in every model world that agrees with
# what was found; a land the model takes next happens in the same event
# (the caller is done); a load that found no refresh can start is done
# EXCLUDES: a desk whose decisions are not the steps the A1 laws are
#   proved of: a fetch on a fresh credential, a store of a failure, a
#   board that leads while the provider is in flight or joins while it is
#   not, a check skipped, a leader left waiting, an act sent to another
#   caller
law flight_step_is_model:
  for +cs: List<&2, F.Cl>
  for +n: Nat
  for +k: Nat
  for fits: {LawsBase.wire_fits(k) == True{} : Bool}
  for +j: Nat
  for +p: String
  for +a: F.At
  for at: {af_find(k, cs) == Some{F.Cl{j, p, a}} : Maybe<&2, F.Cl>}
  for +fd: F.Fd
  for +c: Nat
  for +f: Nat
  for +w: F.W
  for takes: {af_takes(a, fd) == True{} : Bool}
  exs rest: List<&2, F.To>
  {af_reply(FA.step(FA.Open{F.Desk{cs, n}}, af_spell_ev(F.Found{k, fd}))) == af_spell_out(F.Acts{F.To{k, af_model_fd(fd, af_inflight(p, cs), c, f, w)} <> rest}) : String}

# LAW flight_wake_carries_its_outcome: when the leader of p's flight
# reports a found that lands it (a fresh credential at the check, a
# failed fetch, the store's outcome), the reply serves that leader, then
# every caller waiting on p's flight in order, done with this event's
# payload (the landed outcome), and all of them leave the desk; nobody
# else is served and nobody else leaves
# EXCLUDES: a joiner never woken (a lost wake-up), a joiner served
#   another flight's or another caller's outcome, another provider's
#   caller woken, a land that keeps its leader or a joiner, a woken joiner
#   left waiting
law flight_wake_carries_its_outcome:
  for +cs: List<&2, F.Cl>
  for +n: Nat
  for +k: Nat
  for fits: {LawsBase.wire_fits(k) == True{} : Bool}
  for +j: Nat
  for +p: String
  for +a: F.At
  for at: {af_find(k, cs) == Some{F.Cl{j, p, a}} : Maybe<&2, F.Cl>}
  for +fd: F.Fd
  for lands: {af_lands(a, fd) == True{} : Bool}
  {FA.step(FA.Open{F.Desk{cs, n}}, af_spell_ev(F.Found{k, fd})) == (FA.Open{F.Desk{af_unwait(p, af_cut(k, cs)), n}}, af_spell_out(F.Acts{F.To{k, F.DoDone{}} <> af_wake(p, F.DoDone{}, af_cut(k, cs))})) : FA.St & String}

# LAW flight_unwind_lands: a live caller that unwinds (leaves with no
# outcome) leaves the desk; when it leads p's flight, the flight lands
# with exactly "the token refresh of <p> ended without an outcome",
# served to every caller waiting on it, in order, who leave with it; any
# other caller (loading, or waiting) leaves alone and the reply is empty
# EXCLUDES: an unwinding leader whose joiners wait forever, a failure made
#   from another provider or text, a waiting caller's unwind that wakes or
#   drops the others, an unwind that keeps the caller
law flight_unwind_lands:
  for +cs: List<&2, F.Cl>
  for +n: Nat
  for +k: Nat
  for fits: {LawsBase.wire_fits(k) == True{} : Bool}
  for +j: Nat
  for +p: String
  for +a: F.At
  for at: {af_find(k, cs) == Some{F.Cl{j, p, a}} : Maybe<&2, F.Cl>}
  {FA.step(FA.Open{F.Desk{cs, n}}, af_spell_ev(F.Unwinds{k})) == af_unwound(af_leads(a), k, p, cs, n) : FA.St & String}

# LAW flight_step_out_of_turn: an event that names no live caller (one
# never arrived, or done), or a found the caller's step does not give,
# keeps the desk and answers exactly the error form 'E ', then
# "auth_flight: out of turn"
# EXCLUDES: a finished caller served again, an unknown caller's event that
#   changes the desk, a found from the wrong step acted on (a fetch result
#   while loading, any found from a waiting caller)
law flight_step_out_of_turn:
  for +d: F.Desk
  for +e: F.DEv
  for fits: {af_ev_fits(e) == True{} : Bool}
  for off: {af_off(e, af_cs(d)) == True{} : Bool}
  {FA.step(FA.Open{d}, af_spell_ev(e)) == (FA.Open{d}, SCon{'E', SCon{' ', "auth_flight: out of turn"}}) : FA.St & String}

# LAW flight_step_example: anchor: the bytes Rust writes and reads: x's
# first caller arrives (caller 0), finds its credential expired and leads
# (check); a second x caller (1) joins (wait); one waits on x's flight;
# the leader's check finds a fresh credential: 0 and 1 are done; an
# unknown caller and a found from a gone one are out of turn; a y caller
# (2) leads, a y caller (3) joins, the leader unwinds: 3 fails with the
# made text; the store's found of a loading caller is out of turn; a bad
# tag, a bad found and input left over are malformed
# EXCLUDES: a tag numbering or field order other than Rust's
law flight_step_example:
  {af_feed(["0,1,x", "1,0,1,", "0,1,x", "1,1,1,", "3,1,x", "1,0,3,", "1,1,4,", "2,9,"], FA.open("")) == ["", "1,0,0,", "1,0,1,", "1,1,0,", "1,1,4,", "1,1,", "2,0,5,1,5,", "E auth_flight: out of turn", "E auth_flight: out of turn"] : List<&2, String>} &
  {af_feed(["0,1,y", "1,0,1,", "0,1,y", "1,1,1,", "2,0,", "0,1,y", "1,2,7,", "4,", "1,2,8,", "2,2,x"], FA.open("")) == ["", "1,0,0,", "1,0,1,", "1,1,0,", "1,1,4,", "1,1,6,47,the token refresh of y ended without an outcome", "1,2,0,", "E auth_flight: out of turn", "E auth_flight: malformed event", "E auth_flight: malformed event", "E auth_flight: malformed event"] : List<&2, String>} &
  {[af_ev_fits(F.Found{1n, F.Stored{}}), af_takes(F.Loads{}, F.LoadFresh{}), af_lands(F.Checks{}, F.CheckFresh{}), af_off(F.Unwinds{0n}, Nil{})] == [True{}, True{}, True{}, True{}] : List<&2, Bool>}
