# eukhe: the laws of area revive

import Base
import ../bend/revive.bend as Rv
import ../bend/ffi_revive.bend as FR
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# The restart-budget entry of the compiled core (bend/ffi_supervise.bend)

# LAW revive_after_refresh: a run of any length revives: a boot within the boot window b after
# the crash finds its busy evidence fresh, with a refresh every h > 0 ms
# and the max age h + b
law revive_after_refresh:
  for +h: Nat
  for pos: {Nat.is_lt(0n, h) == True{} : Bool}
  for +b: Nat
  for +c: Nat
  for +d: Nat
  for soon: {Nat.is_le(d, b) == True{} : Bool}
  {Rv.fresh(Nat.add(h, b), Rv.age(h, c, d)) == True{} : Bool}

# (D1) The revival veto's entry of the compiled core
# --------------------------------------------------
# docs/daemon.md D1: a supervisor boot relaunches a dead worker only when
# the journal proves interrupted live work this boot must heal. Rust
# `revival_gate::revival_veto` gathers the facts (the descriptor's
# lifecycle, the session file's archived belt, the live lease holder, the
# newest busy record's stamp, the clock) and the entry
# (bend/ffi_revive.bend) decides: no Rust copy of the vetoes. Every input
# is free: any facts, any times, any max age and skew.
#
# The spec below spells the request and the reply with the wire primitives
# (bend/wire.bend), never with the entry's own codec, and states the
# vetoes in their order on its own.

# Spec
# ----

def rv_spell_bool(b: Bool, rest: String) -> String:
  Wr.put_bool(b, rest)

def rv_spell_lease(l: Maybe<&2, Nat>, rest: String) -> String:
  match l:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{p}:
      Wr.put_nat(1n, Wr.put_nat(p, rest))

def rv_spell_busy(b: Rv.Busy, rest: String) -> String:
  match b:
    case Rv.NoBusy{}:
      Wr.put_nat(0n, rest)
    case Rv.Unread{}:
      Wr.put_nat(1n, rest)
    case Rv.Stamp{at}:
      Wr.put_nat(2n, Wr.put_nat(at, rest))

# the request Rust writes for the facts f
def rv_spell(f: Rv.Facts) -> String:
  match f:
    case Rv.Facts{fl, a, l, b, n, m, k}:
      Wr.put_bool(fl, Wr.put_bool(a, rv_spell_lease(l, rv_spell_busy(b, Wr.put_nat(n, Wr.put_nat(m, Wr.put_nat(k, "")))))))

def rv_lease_fits(l: Maybe<&2, Nat>) -> Bool:
  match l:
    case None{}:
      True{}
    case Some{p}:
      LawsBase.wire_fits(p)

def rv_busy_fits(b: Rv.Busy) -> Bool:
  match b:
    case Rv.NoBusy{}:
      True{}
    case Rv.Unread{}:
      True{}
    case Rv.Stamp{at}:
      LawsBase.wire_fits(at)

# every number of the facts fits the wire
def rv_fits(f: Rv.Facts) -> Bool:
  match f:
    case Rv.Facts{fl, a, l, b, n, m, k}:
      Bool.and(rv_lease_fits(l), Bool.and(rv_busy_fits(b), Bool.and(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(k)))))

def rv_fresh.of(past: Bool, at: Nat, now: Nat, max: Nat, skew: Nat) -> Bool:
  match past:
    case True{}:
      Nat.is_le(Nat.sub(now, at), max)
    case False{}:
      Nat.is_le(Nat.sub(at, now), skew)

# a stamp at `at` proves fresh work at `now`: dated at most `skew` ms after
# now, and at most `max` ms old (a stamp after now is 0 ms old)
def rv_fresh(+at: Nat, +now: Nat, max: Nat, skew: Nat) -> Bool:
  rv_fresh.of(Nat.is_le(at, now), at, now, max, skew)

def rv_reply.fresh(ok: Bool) -> String:
  match ok:
    case True{}:
      Wr.put_nat(0n, "")
    case False{}:
      Wr.put_nat(5n, "")

# the reply: 0 revive, 1 gave up, 2 archived, 3 leased (then the pid), 4 no
# busy evidence, 5 stale busy evidence
def rv_reply.busy(b: Rv.Busy, now: Nat, max: Nat, skew: Nat) -> String:
  match b:
    case Rv.NoBusy{}:
      Wr.put_nat(4n, "")
    case Rv.Unread{}:
      Wr.put_nat(5n, "")
    case Rv.Stamp{at}:
      rv_reply.fresh(rv_fresh(at, now, max, skew))

# the vetoes in their order: the give-up verdict, the archived belt, a
# live lease, then the busy evidence: none with a stamp, or a stamp that
# cannot be read or is not fresh; else the worker revives
def rv_reply(f: Rv.Facts) -> String:
  match f:
    case Rv.Facts{fl, a, l, b, n, m, k}:
      match fl:
        case True{}:
          Wr.put_nat(1n, "")
        case False{}:
          match a:
            case True{}:
              Wr.put_nat(2n, "")
            case False{}:
              match l:
                case Some{p}:
                  Wr.put_nat(3n, Wr.put_nat(p, ""))
                case None{}:
                  rv_reply.busy(b, n, m, k)

# Reader: the requests the entry accepts, read with the wire primitives

def rv_read.k(fl: Bool, a: Bool, l: Maybe<&2, Nat>, b: Rv.Busy, n: Nat, m: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Rv.Facts>:
  match r:
    case Wr.Got{k, s}:
      Wr.Got{Rv.Facts{fl, a, l, b, n, m, k}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def rv_read.m(fl: Bool, a: Bool, l: Maybe<&2, Nat>, b: Rv.Busy, n: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Rv.Facts>:
  match r:
    case Wr.Got{m, s}:
      rv_read.k(fl, a, l, b, n, m, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def rv_read.n(fl: Bool, a: Bool, l: Maybe<&2, Nat>, b: Rv.Busy, r: Wr.Dec<Nat>) -> Wr.Dec<Rv.Facts>:
  match r:
    case Wr.Got{n, s}:
      rv_read.m(fl, a, l, b, n, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def rv_read.at(fl: Bool, a: Bool, l: Maybe<&2, Nat>, r: Wr.Dec<Nat>) -> Wr.Dec<Rv.Facts>:
  match r:
    case Wr.Got{at, s}:
      rv_read.n(fl, a, l, Rv.Stamp{at}, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def rv_read.busy.tag(fl: Bool, a: Bool, l: Maybe<&2, Nat>, t: Nat, s: String) -> Wr.Dec<Rv.Facts>:
  match t:
    case 0n:
      rv_read.n(fl, a, l, Rv.NoBusy{}, Wr.get_nat(s))
    case 1n:
      rv_read.n(fl, a, l, Rv.Unread{}, Wr.get_nat(s))
    case 2n:
      rv_read.at(fl, a, l, Wr.get_nat(s))
    case 3n+p:
      Wr.Bad{}

def rv_read.busy(fl: Bool, a: Bool, l: Maybe<&2, Nat>, r: Wr.Dec<Nat>) -> Wr.Dec<Rv.Facts>:
  match r:
    case Wr.Got{t, s}:
      rv_read.busy.tag(fl, a, l, t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def rv_read.pid(fl: Bool, a: Bool, r: Wr.Dec<Nat>) -> Wr.Dec<Rv.Facts>:
  match r:
    case Wr.Got{p, s}:
      rv_read.busy(fl, a, Some{p}, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def rv_read.lease.tag(fl: Bool, a: Bool, t: Nat, s: String) -> Wr.Dec<Rv.Facts>:
  match t:
    case 0n:
      rv_read.busy(fl, a, None{}, Wr.get_nat(s))
    case 1n:
      rv_read.pid(fl, a, Wr.get_nat(s))
    case 2n+p:
      Wr.Bad{}

def rv_read.lease(fl: Bool, a: Bool, r: Wr.Dec<Nat>) -> Wr.Dec<Rv.Facts>:
  match r:
    case Wr.Got{t, s}:
      rv_read.lease.tag(fl, a, t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def rv_read.archived(fl: Bool, r: Wr.Dec<Bool>) -> Wr.Dec<Rv.Facts>:
  match r:
    case Wr.Got{a, s}:
      rv_read.lease(fl, a, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def rv_read.failed(r: Wr.Dec<Bool>) -> Wr.Dec<Rv.Facts>:
  match r:
    case Wr.Got{fl, s}:
      rv_read.archived(fl, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def rv_read.end(whole: Bool, f: Rv.Facts) -> Maybe<&2, Rv.Facts>:
  match whole:
    case True{}:
      Some{f}
    case False{}:
      None{}

def rv_read.whole(r: Wr.Dec<Rv.Facts>) -> Maybe<&2, Rv.Facts>:
  match r:
    case Wr.Got{f, s}:
      rv_read.end(Wr.end(s), f)
    case Wr.Bad{}:
      None{}

# the facts s is, when s is exactly one request
def rv_read(s: String) -> Maybe<&2, Rv.Facts>:
  rv_read.whole(rv_read.failed(Wr.get_bool(s)))

# Laws
# ----

# LAW revive_ffi_answers: on every request Rust writes (every number within the wire), the
# entry answers the vetoes in their order: a worker the supervisor gave up
# stays given up; else an archived session stays down; else a live lease
# holder (its pid) keeps it; else no stamped busy record, or a stamp that
# cannot be read, more than the skew in the future or older than the max
# age, keeps it down; a fresh stamp revives it
# EXCLUDES: a misread or swapped fact, a veto out of order (a lease or a
#   fresh stamp reviving a given-up or archived session), a stale or
#   future stamp that revives, an unreadable stamp taken as fresh, a fresh
#   stamp refused, a max age or skew bound off by one
law revive_ffi_answers:
  for +f: Rv.Facts
  for fits: {rv_fits(f) == True{} : Bool}
  {FR.ffi(rv_spell(f)) == rv_reply(f) : String}

# LAW revive_ffi_reads: every input that is exactly one request (as the wire primitives read
# it) gets the veto on its facts
# EXCLUDES: a reply on another reading of the input
law revive_ffi_reads:
  for +s: String
  for +f: Rv.Facts
  for got: {rv_read(s) == Some{f} : Maybe<&2, Rv.Facts>}
  {FR.ffi(s) == rv_reply(f) : String}

# LAW revive_ffi_malformed_exact: every input that is not exactly one request (an unknown tag, a
# number past the wire, input left over) gets exactly the error form 'E ',
# then "revive: malformed request"
# EXCLUDES: a revival on garbage, a request with input after it answered
law revive_ffi_malformed_exact:
  for +s: String
  for no: {rv_read(s) == None{} : Maybe<&2, Rv.Facts>}
  {FR.ffi(s) == SCon{'E', SCon{' ', "revive: malformed request"}} : String}

# LAW revive_veto_ages_as_model: the entry's model (Rv.veto) judges a stamp a ms old by the
# busy-evidence model's freshness (Rv.fresh, which revive_after_refresh
# speaks of): with no other veto, a record a ms before the boot revives
# exactly when Rv.fresh(m, a)
# EXCLUDES: a veto whose age is not the model's (revive_after_refresh
#   proved of another freshness than the one that runs)
law revive_veto_ages_as_model:
  for +at: Nat
  for +a: Nat
  for +m: Nat
  for +k: Nat
  {Rv.veto(Rv.Facts{False{}, False{}, None{}, Rv.Stamp{at}, Nat.add(at, a), m, k}) == Rv.veto.fresh(Rv.fresh(m, a)) : Rv.Veto}

# LAW revive_ffi_ages_as_model: the entry itself judges a stamp a ms before the boot (no other
# veto) by the busy-evidence model's freshness (Rv.fresh, which
# revive_after_refresh speaks of): it revives (0) exactly when
# Rv.fresh(m, a), and answers stale (5) otherwise
# EXCLUDES: an entry whose freshness is not the one revive_after_refresh is
#   proved of (that law would then say nothing about the boots that run)
law revive_ffi_ages_as_model:
  for +at: Nat
  for +a: Nat
  for +m: Nat
  for +k: Nat
  for fits: {rv_fits(Rv.Facts{False{}, False{}, None{}, Rv.Stamp{at}, Nat.add(at, a), m, k}) == True{} : Bool}
  {FR.ffi(rv_spell(Rv.Facts{False{}, False{}, None{}, Rv.Stamp{at}, Nat.add(at, a), m, k})) == rv_reply.fresh(Rv.fresh(m, a)) : String}

# LAW revive_ffi_example: anchor: the strings Rust writes and the replies it reads: a fresh
# stamp revives, a live lease (pid 77) and the give-up verdict veto, a stamp
# past the skew is stale, a missing stamp is no evidence, the skew's and the
# max age's edges are inside; input left over is refused
# EXCLUDES: a field order or tag numbering other than Rust's
law revive_ffi_example:
  {FR.ffi("FF0,2,10,15,1800,60,") == "0," : String} &
  {FR.ffi("FF1,77,2,10,15,1800,60,") == "3,77," : String} &
  {FR.ffi("TT1,77,2,10,15,1800,60,") == "1," : String} &
  {FR.ffi("FT0,2,10,15,1800,60,") == "2," : String} &
  {FR.ffi("FF0,2,76,15,1800,60,") == "5," : String} &
  {FR.ffi("FF0,2,75,15,1800,60,") == "0," : String} &
  {FR.ffi("FF0,2,0,1800,1800,60,") == "0," : String} &
  {FR.ffi("FF0,2,0,1801,1800,60,") == "5," : String} &
  {FR.ffi("FF0,0,15,1800,60,") == "4," : String} &
  {FR.ffi("FF0,1,15,1800,60,") == "5," : String} &
  {FR.ffi("FF0,0,15,1800,60,x") == Wr.err("revive: malformed request") : String}
