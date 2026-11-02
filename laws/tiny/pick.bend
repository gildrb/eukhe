# eukhe: the laws of area tiny, section pick: the chain of models and the
# worker of one model (bend/tiny.bend sections 1 and 2), and the pick's
# entry (bend/ffi_tiny.bend)

import Base
import ../../bend/ffi_tiny.bend as FTn
import ../../bend/tiny.bend as Tn
import ../../bend/wire.bend as Wr
import ../base.bend as LawsBase

# (S9) Local tiny models
# ----------------------
# the model in bend/tiny.bend. Every input is free:
# any chain of models, any set of available models, any needs of any
# processes with any tags, any worker exits, in any order.

# LAW tiny_pick_in_chain: a task uses only a model of its chain that is available
law tiny_pick_in_chain:
  for +chain: List<&2, Nat>
  for +up: List<&2, Nat>
  for +m: Nat
  for used: {Tn.pick(chain, up) == Tn.Use{m} : Tn.Pick}
  {Bool.and(Tn.elem(chain, m), Tn.elem(up, m)) == True{} : Bool}

# LAW tiny_pick_first: it uses the first available model of the chain
law tiny_pick_first:
  for +pre: List<&2, Nat>
  for +m: Nat
  for +post: List<&2, Nat>
  for +up: List<&2, Nat>
  for before: {Tn.none_up(pre, up) == True{} : Bool}
  for here: {Tn.elem(up, m) == True{} : Bool}
  {Tn.pick(List.append(&2, Nat, pre, m <> post), up) == Tn.Use{m} : Tn.Pick}

# LAW tiny_pick_unavailable: with no model of the chain available the task fails as
# Unavailable: it never runs on a model outside the chain
law tiny_pick_unavailable:
  for +chain: List<&2, Nat>
  for +up: List<&2, Nat>
  for none: {Tn.none_up(chain, up) == True{} : Bool}
  {Tn.pick(chain, up) == Tn.Unavailable{} : Tn.Pick}

# the spec of the terms the pick laws read: x is among xs; no model of
# xs is among up
def sp_in(xs: List<&2, Nat>, +x: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(Nat.is_eq(y, x), sp_in(rest, x))

def sp_none_up(xs: List<&2, Nat>, +up: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> rest:
      Bool.and(Bool.not(sp_in(up, x)), sp_none_up(rest, up))

# LAW tiny_terms_exact: the model's terms the pick laws read (`elem`,
# `none_up`) mean what the laws say: membership, and no model available
# EXCLUDES: a `none_up` that is False for every chain (it would make
#   tiny_pick_unavailable and tiny_pick_first vacuous), an `elem` that
#   answers True for anything (a mutation probe found the first free)
law tiny_terms_exact:
  for +xs: List<&2, Nat>
  for +up: List<&2, Nat>
  for +x: Nat
  {Tn.elem(xs, x) == sp_in(xs, x) : Bool} & {Tn.none_up(xs, up) == sp_none_up(xs, up) : Bool}

# LAW tiny_every_need_served: every need of a process gets exactly one outcome: it joins, starts
# or replaces the worker
law tiny_every_need_served:
  for +es: List<&2, Tn.Ev>
  for +w: Tn.W
  {List.length(&2, Tn.Got, Tn.gots(es, w)) == Tn.needs(es) : Nat}

# LAW tiny_worker_current: after any events, the worker runs with the tag of the last need
# since the last exit: a stale worker never serves a process
law tiny_worker_current:
  for +es: List<&2, Tn.Ev>
  {Tn.W.tag(Tn.run(es, Tn.NoWorker{})) == Tn.last_tag(es, None{}) : Maybe<&2, Nat>}

# the spec of the terms the worker laws read: the number of needs, the
# tag of the last need since the last exit, the tag a worker runs with
def sp_needs(es: List<&2, Tn.Ev>) -> Nat:
  match es:
    case Nil{}:
      0n
    case e <> rest:
      match e:
        case Tn.Need{p, t}:
          1n+sp_needs(rest)
        case Tn.Gone{}:
          sp_needs(rest)

def sp_last_tag(es: List<&2, Tn.Ev>, m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match es:
    case Nil{}:
      m
    case e <> rest:
      match e:
        case Tn.Need{p, t}:
          sp_last_tag(rest, Some{t})
        case Tn.Gone{}:
          sp_last_tag(rest, None{})

def sp_wtag(w: Tn.W) -> Maybe<&2, Nat>:
  match w:
    case Tn.NoWorker{}:
      None{}
    case Tn.Worker{o, t}:
      Some{t}

# LAW tiny_worker_terms_exact: the model's terms tiny_every_need_served and
# tiny_worker_current read (`needs`, `last_tag`, `W.tag`) mean what the
# laws say
# EXCLUDES: a worker model that never starts a worker and reports no
#   outcome, with `needs` and `last_tag` redefined to match (a fresh
#   specification-completeness review passed every law that way)
law tiny_worker_terms_exact:
  for +es: List<&2, Tn.Ev>
  for +m: Maybe<&2, Nat>
  for +w: Tn.W
  {Tn.needs(es) == sp_needs(es) : Nat} & {Tn.last_tag(es, m) == sp_last_tag(es, m) : Maybe<&2, Nat>} & {Tn.W.tag(w) == sp_wtag(w) : Maybe<&2, Nat>}

# LAW tiny_same_tag_joins: a need with the running worker's tag joins it: no restart churn
law tiny_same_tag_joins:
  for +o: Nat
  for +t: Nat
  for +p: Nat
  {Tn.got(Tn.Worker{o, t}, Tn.Need{p, t}) == [Tn.Joined{}] : List<&2, Tn.Got>}

# LAW tiny_ffi_request_round_trip (compiled core): the tiny pick entry (bend/ffi_tiny.bend) reads back
# a chain and the available models as Rust writes it, and leaves what follows untouched
# EXCLUDES: a request field misread, dropped, reordered or shifted; a
#   decoder that eats the input after the request
law tiny_ffi_request_round_trip:
  for +chain: List<&2, Nat>
  for +up: List<&2, Nat>
  for +rest: String
  for h: {Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, chain)), LawsBase.wire_nats_fit(chain)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, up)), LawsBase.wire_nats_fit(up))) == True{} : Bool}
  {FTn.get_req(FTn.put_req(FTn.Req{chain, up}, rest)) == Wr.Got{FTn.Req{chain, up}, rest} : Wr.Dec<FTn.Req>}

# LAW tiny_ffi_answers (compiled core): the tiny pick entry answers a whole request with the
# model's pick
# EXCLUDES: an entry that answers another rule, a default, or a reply for
#   a request it misread
law tiny_ffi_answers:
  for +chain: List<&2, Nat>
  for +up: List<&2, Nat>
  for h: {Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, chain)), LawsBase.wire_nats_fit(chain)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, up)), LawsBase.wire_nats_fit(up))) == True{} : Bool}
  {FTn.ffi(FTn.put_req(FTn.Req{chain, up}, "")) == FTn.put_pick(Tn.pick(chain, up), "") : String}

# LAW tiny_ffi_rejects_malformed (compiled core): the tiny pick entry answers a malformed request with
# the error form, never a default
# EXCLUDES: a decision made on input that is no request
law tiny_ffi_rejects_malformed:
  for +s: String
  for bad: {FTn.get_req(s) == Wr.Bad{} : Wr.Dec<FTn.Req>}
  {LawsBase.wire_opens_err(FTn.ffi(s)) == True{} : Bool}

# LAW tiny_ffi_rejects_left_over (compiled core): and a request followed by more input with the error
# form
# EXCLUDES: an entry that ignores input left over (a second request, a
#   truncated one)
law tiny_ffi_rejects_left_over:
  for +s: String
  for +q: FTn.Req
  for +r: String
  for got: {FTn.get_req(s) == Wr.Got{q, r} : Wr.Dec<FTn.Req>}
  for more: {String.is_empty(r) == False{} : Bool}
  {LawsBase.wire_opens_err(FTn.ffi(s)) == True{} : Bool}

# The pick's entry from the requirement
# -------------------------------------
# The spec of the whole entry, written from the requirement (S9: a task
# uses the first model of its chain that is available, else it fails as
# Unavailable) and the wire's primitives only: no function of
# bend/tiny.bend or bend/ffi_tiny.bend (their types only).

# m when it is available (here), else the pick of the rest
def sp_pick.at(here: Bool, m: Nat, r: Tn.Pick) -> Tn.Pick:
  match here:
    case True{}:
      Tn.Use{m}
    case False{}:
      r

# the first model of chain among up, else Unavailable
def sp_pick(chain: List<&2, Nat>, +up: List<&2, Nat>) -> Tn.Pick:
  match chain:
    case Nil{}:
      Tn.Unavailable{}
    case +m <> rest:
      sp_pick.at(sp_in(up, m), m, sp_pick(rest, up))

# a pick on the wire: 0 then the model, or 1
def sp_spell_pick(p: Tn.Pick) -> String:
  match p:
    case Tn.Use{m}:
      Wr.put_nat(0n, Wr.put_nat(m, ""))
    case Tn.Unavailable{}:
      Wr.put_nat(1n, "")

def sp_read.up(c: List<&2, Nat>, r: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<FTn.Req>:
  match r:
    case Wr.Got{u, s}:
      Wr.Got{FTn.Req{c, u}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def sp_read.chain(r: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<FTn.Req>:
  match r:
    case Wr.Got{c, s}:
      sp_read.up(c, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case Wr.Bad{}:
      Wr.Bad{}

# the chain and the available models s starts with (two lists of Nats),
# and what follows
def sp_read(s: String) -> Wr.Dec<FTn.Req>:
  sp_read.chain(Wr.get_list(~Nat, ~Wr.get_nat, s))

def sp_pick_end(whole: Bool, q: FTn.Req) -> String:
  match whole:
    case True{}:
      match q:
        case FTn.Req{c, u}:
          sp_spell_pick(sp_pick(c, u))
    case False{}:
      Wr.err("tiny: input left over")

def sp_pick_run(r: Wr.Dec<FTn.Req>) -> String:
  match r:
    case Wr.Got{q, s}:
      sp_pick_end(Wr.end(s), q)
    case Wr.Bad{}:
      Wr.err("tiny: malformed request")

# the entry's answer to the input s
def sp_pick_entry(s: String) -> String:
  sp_pick_run(sp_read(s))

# LAW tiny_ffi_exact (compiled core): on every input the tiny pick entry answers the spec's
# pick of the chain and the available models the input is exactly (the
# first model of the chain that is available, else Unavailable), exactly
# "tiny: input left over" for a request followed by more input, and
# exactly "tiny: malformed request" for any other input
# EXCLUDES: a model outside the chain or not available, a later one, a
#   misread request, a pick spelled otherwise, a default for malformed
#   input, input left over ignored, another error text
law tiny_ffi_exact:
  for +s: String
  {FTn.ffi(s) == sp_pick_entry(s) : String}
