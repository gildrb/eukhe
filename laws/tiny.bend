# eukhe: the laws of area tiny

import Base
import ../bend/ffi_tiny.bend as FTn
import ../bend/ffi_tiny_elect.bend as FTe
import ../bend/tiny.bend as Tn
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (S9) Local tiny models
# ----------------------
# docs/inference.md S9, the model in bend/tiny.bend. Every input is free:
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

# (S9) One process's election
# ---------------------------
# bend/tiny.bend section 3, run as the compiled core by
# bend/ffi_tiny_elect.bend (crates/eukhe-tiny election.rs). Every input
# is free: any probe of the socket with any tag, any launch tag, any
# answer to a shutdown, any start and launch.
#
# R1: a worker that answers with the process's tag (the same text, char
#     by char) is joined; one with another tag is replaced; with no
#     worker (no socket, a refused one, or one that hangs up on the ping)
#     the process starts one; a socket that fails otherwise or speaks out
#     of protocol is an IO error, never a join or a start.
# R2: a shutdown answered with bye, or cut by the worker's own exit, lets
#     the start go on; another answer is out of protocol; another failure
#     is an IO error.
# R3: a start the process made gets Started (first worker) or Replaced
#     (replacement) when its worker bound the socket, Joined when another
#     worker took the socket first.
# R4: after a start, only a worker with the process's tag is used; another
#     tag or no worker fails the start; a failing socket is an IO error.
# R6: a started worker leaves a live worker of any tag in place (it is
#     adopted), takes a socket with no live worker, and fails on a socket
#     that fails otherwise or speaks out of protocol.
# R5: the entry answers each request Rust writes with the choice of R1-R4
#     and R6, reads exactly the request and nothing after it, and answers
#     any other input with the exact error form.

# Spec helpers
# ------------

def sp_pong(b: Bool, j: Tn.Act, r: Tn.Act) -> Tn.Act:
  match b:
    case True{}:
      j
    case False{}:
      r

# R1
def sp_elect(p: Tn.Probe, +m: String) -> Tn.Act:
  match p:
    case Tn.Missing{}:
      Tn.Start{}
    case Tn.Unreachable{}:
      Tn.Broken{}
    case Tn.Pong{t}:
      sp_pong(LawsBase.text_same(t, m), Tn.Join{}, Tn.Replace{})
    case Tn.Odd{}:
      Tn.Broken{}
    case Tn.Garbled{}:
      Tn.Broken{}
    case Tn.Hung{}:
      Tn.Start{}

# R2
def sp_shut(h: Tn.Heard) -> Tn.Shut:
  match h:
    case Tn.Bye{}:
      Tn.Down{}
    case Tn.Other{}:
      Tn.Spoke{}
    case Tn.Eof{}:
      Tn.Down{}
    case Tn.Lost{}:
      Tn.Cut{}

# R3
def sp_launched(l: Tn.Launch, f: Tn.Fresh) -> Tn.Got:
  match l:
    case Tn.Adopted{}:
      Tn.Joined{}
    case Tn.Bound{}:
      match f:
        case Tn.First{}:
          Tn.Started{}
        case Tn.Again{}:
          Tn.Replaced{}

def sp_check(b: Bool) -> Tn.Check:
  match b:
    case True{}:
      Tn.Serving{}
    case False{}:
      Tn.Mistagged{}

# R4
def sp_confirm(p: Tn.Probe, +m: String) -> Tn.Check:
  match p:
    case Tn.Missing{}:
      Tn.Vacant{}
    case Tn.Unreachable{}:
      Tn.Faulty{}
    case Tn.Pong{t}:
      sp_check(LawsBase.text_same(t, m))
    case Tn.Odd{}:
      Tn.Faulty{}
    case Tn.Garbled{}:
      Tn.Faulty{}
    case Tn.Hung{}:
      Tn.Vacant{}

# R6
def sp_bind(p: Tn.Probe) -> Tn.Seat:
  match p:
    case Tn.Missing{}:
      Tn.Take{}
    case Tn.Unreachable{}:
      Tn.Fault{}
    case Tn.Pong{t}:
      Tn.Adopt{}
    case Tn.Odd{}:
      Tn.Fault{}
    case Tn.Garbled{}:
      Tn.Fault{}
    case Tn.Hung{}:
      Tn.Take{}

# what a need of the worker model gets from a choice whose start bound
def sp_need(a: Tn.Act) -> List<&2, Tn.Got>:
  match a:
    case Tn.Join{}:
      [Tn.Joined{}]
    case Tn.Replace{}:
      [Tn.Replaced{}]
    case Tn.Start{}:
      [Tn.Started{}]
    case Tn.Broken{}:
      Nil{}

# The spelling of a request and of its reply, from the wire primitives
# (R5): a probe is its tag (Pong: then its tag text); a request is its
# tag, then its fields; a reply is the tag of the choice.

def sp_w_probe(p: Tn.Probe, rest: String) -> String:
  match p:
    case Tn.Missing{}:
      Wr.put_nat(0n, rest)
    case Tn.Unreachable{}:
      Wr.put_nat(1n, rest)
    case Tn.Pong{t}:
      Wr.put_nat(2n, Wr.put_str(t, rest))
    case Tn.Odd{}:
      Wr.put_nat(3n, rest)
    case Tn.Garbled{}:
      Wr.put_nat(4n, rest)
    case Tn.Hung{}:
      Wr.put_nat(5n, rest)

def sp_w_heard(h: Tn.Heard) -> Nat:
  match h:
    case Tn.Bye{}:
      0n
    case Tn.Other{}:
      1n
    case Tn.Eof{}:
      2n
    case Tn.Lost{}:
      3n

def sp_w_fresh(f: Tn.Fresh) -> Nat:
  match f:
    case Tn.First{}:
      0n
    case Tn.Again{}:
      1n

def sp_w_launch(l: Tn.Launch) -> Nat:
  match l:
    case Tn.Bound{}:
      0n
    case Tn.Adopted{}:
      1n

def sp_w_req(q: FTe.Req, rest: String) -> String:
  match q:
    case FTe.QElect{p, m}:
      Wr.put_nat(0n, sp_w_probe(p, Wr.put_str(m, rest)))
    case FTe.QShut{h}:
      Wr.put_nat(1n, Wr.put_nat(sp_w_heard(h), rest))
    case FTe.QLaunched{f, l}:
      Wr.put_nat(2n, Wr.put_nat(sp_w_fresh(f), Wr.put_nat(sp_w_launch(l), rest)))
    case FTe.QConfirm{p, m}:
      Wr.put_nat(3n, sp_w_probe(p, Wr.put_str(m, rest)))
    case FTe.QBind{p}:
      Wr.put_nat(4n, sp_w_probe(p, rest))

def sp_w_act(a: Tn.Act) -> Nat:
  match a:
    case Tn.Join{}:
      0n
    case Tn.Replace{}:
      1n
    case Tn.Start{}:
      2n
    case Tn.Broken{}:
      3n

def sp_w_shut(x: Tn.Shut) -> Nat:
  match x:
    case Tn.Down{}:
      0n
    case Tn.Spoke{}:
      1n
    case Tn.Cut{}:
      2n

def sp_w_got(g: Tn.Got) -> Nat:
  match g:
    case Tn.Started{}:
      0n
    case Tn.Joined{}:
      1n
    case Tn.Replaced{}:
      2n

def sp_w_check(c: Tn.Check) -> Nat:
  match c:
    case Tn.Serving{}:
      0n
    case Tn.Mistagged{}:
      1n
    case Tn.Vacant{}:
      2n
    case Tn.Faulty{}:
      3n

def sp_w_seat(x: Tn.Seat) -> Nat:
  match x:
    case Tn.Adopt{}:
      0n
    case Tn.Take{}:
      1n
    case Tn.Fault{}:
      2n

# the reply Rust reads: the spelled choice of the spec (R1-R4, R6)
def sp_w_reply(q: FTe.Req) -> String:
  match q:
    case FTe.QElect{p, +m}:
      Wr.put_nat(sp_w_act(sp_elect(p, m)), "")
    case FTe.QShut{h}:
      Wr.put_nat(sp_w_shut(sp_shut(h)), "")
    case FTe.QLaunched{f, l}:
      Wr.put_nat(sp_w_got(sp_launched(l, f)), "")
    case FTe.QConfirm{p, +m}:
      Wr.put_nat(sp_w_check(sp_confirm(p, m)), "")
    case FTe.QBind{p}:
      Wr.put_nat(sp_w_seat(sp_bind(p)), "")

def sp_fit_probe(p: Tn.Probe) -> Bool:
  match p:
    case Tn.Missing{}:
      True{}
    case Tn.Unreachable{}:
      True{}
    case Tn.Pong{t}:
      LawsBase.wire_fits(String.length(t))
    case Tn.Odd{}:
      True{}
    case Tn.Garbled{}:
      True{}
    case Tn.Hung{}:
      True{}

# every length of the request fits the wire
def sp_fit_req(q: FTe.Req) -> Bool:
  match q:
    case FTe.QElect{p, m}:
      Bool.and(sp_fit_probe(p), LawsBase.wire_fits(String.length(m)))
    case FTe.QShut{h}:
      True{}
    case FTe.QLaunched{f, l}:
      True{}
    case FTe.QConfirm{p, m}:
      Bool.and(sp_fit_probe(p), LawsBase.wire_fits(String.length(m)))
    case FTe.QBind{p}:
      sp_fit_probe(p)

# Laws: the choices
# -----------------

# LAW tiny_elect_spec (R1): the first choice of a process is the spec's:
# join its tag, replace another tag, start with no worker, an IO error on
# a failing socket
# EXCLUDES: tags compared by prefix, length or case; a hung-up worker
#   taken for an error, or a failing socket for a missing worker; a
#   worker of another tag joined
law tiny_elect_spec:
  for +p: Tn.Probe
  for +m: String
  {Tn.elect(p, m) == sp_elect(p, m) : Tn.Act}

# LAW tiny_shut_spec (R2): what a shutdown's answer means
# EXCLUDES: a start on top of a worker that answered out of protocol; an
#   error for a worker that exited on its own meanwhile
law tiny_shut_spec:
  for +h: Tn.Heard
  {Tn.shut(h) == sp_shut(h) : Tn.Shut}

# LAW tiny_launched_spec (R3): what a need that started a worker got
# EXCLUDES: a replacement reported as a first start, an adopted worker
#   reported as started by this process
law tiny_launched_spec:
  for +f: Tn.Fresh
  for +l: Tn.Launch
  {Tn.launched(f, l) == sp_launched(l, f) : Tn.Got}

# LAW tiny_confirm_spec (R4): after a start only a worker with the
# process's tag is used
# EXCLUDES: a stale worker of another tag used after a start; a vacant
#   socket taken for a running worker
law tiny_confirm_spec:
  for +p: Tn.Probe
  for +m: String
  {Tn.confirm(p, m) == sp_confirm(p, m) : Tn.Check}

# LAW tiny_bind_spec (R6): a started worker adopts a live worker of any
# tag and binds only a socket with no live worker
# EXCLUDES: two workers bound on one socket; a live worker's socket
#   removed; a failing socket taken for a free one
law tiny_bind_spec:
  for +p: Tn.Probe
  {Tn.bind(p) == sp_bind(p) : Tn.Seat}

# LAW tiny_elect_is_worker_model (R1, R3): a process's choice, with its
# start bound, is what the worker model's need gets: with a worker of tag
# t running and a need of tag m (the texts a and b name them: the same
# text exactly when t = m), and with no worker
# EXCLUDES: a process election that drifts from the worker model of
#   tiny_same_tag_joins and tiny_worker_current
law tiny_elect_is_worker_model:
  for +o: Nat
  for +t: Nat
  for +q: Nat
  for +m: Nat
  for +a: String
  for +b: String
  for named: {LawsBase.text_same(a, b) == Nat.is_eq(t, m) : Bool}
  {sp_need(Tn.elect(Tn.Pong{a}, b)) == Tn.got(Tn.Worker{o, t}, Tn.Need{q, m}) : List<&2, Tn.Got>} & {sp_need(Tn.elect(Tn.Missing{}, b)) == Tn.got(Tn.NoWorker{}, Tn.Need{q, m}) : List<&2, Tn.Got>}

# Laws: the entry (R5)
# --------------------

# LAW tiny_elect_entry_answers (R5): the election entry answers every
# request Rust spells, every length within the wire, with the spelled
# choice of the spec
# EXCLUDES: a field misread, swapped or dropped; a request answered with
#   another request's choice, a default, or a reply spelled otherwise
law tiny_elect_entry_answers:
  for +q: FTe.Req
  for h: {sp_fit_req(q) == True{} : Bool}
  {FTe.ffi(sp_w_req(q, "")) == sp_w_reply(q) : String}

# LAW tiny_elect_entry_reads (R5): the entry's decoder reads a spelled
# request back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request, or
#   reads a field from it
law tiny_elect_entry_reads:
  for +q: FTe.Req
  for +rest: String
  for h: {sp_fit_req(q) == True{} : Bool}
  {FTe.get_req(sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FTe.Req>}

# LAW tiny_elect_entry_exact (R5): every input the entry does not answer
# with the error form is a spelled request that fits the wire
# EXCLUDES: a choice made on input that is no request (an unknown tag, a
#   malformed field, input left over)
law tiny_elect_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FTe.ffi(s)) == False{} : Bool}
  exs r: FTe.Req
  {s == sp_w_req(r, "") : String} & {sp_fit_req(r) == True{} : Bool}

# LAW tiny_elect_entry_refuses (R5): every error the entry answers is
# exactly `E tiny_elect: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law tiny_elect_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FTe.ffi(s)) == True{} : Bool}
  {FTe.ffi(s) == Wr.err("tiny_elect: malformed request") : String}

# LAW tiny_elect_entry_example (R5): anchor: the wire strings Rust sends
# and the replies it reads; an unknown tag and input left over
# EXCLUDES: tags in another order, a field order other than Rust's
law tiny_elect_entry_example:
  {[FTe.ffi("0,2,3,abc3,abc"), FTe.ffi("0,2,3,abc3,abd"), FTe.ffi("0,5,1,x"), FTe.ffi("1,2,"), FTe.ffi("2,1,1,"), FTe.ffi("2,1,0,"), FTe.ffi("3,2,1,a1,b"), FTe.ffi("3,0,0,"), FTe.ffi("4,2,1,z"), FTe.ffi("4,5,"), FTe.ffi("5,"), FTe.ffi("1,2,x")] == ["0,", "1,", "2,", "0,", "1,", "2,", "1,", "2,", "0,", "1,", Wr.err("tiny_elect: malformed request"), Wr.err("tiny_elect: malformed request")] : List<&2, String>}
