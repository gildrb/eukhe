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

# The pick entry, spelled
# -----------------------
# The entry laws above read and write through the entry's own encoders
# (FTn.put_req, FTn.put_pick): a tag drift both sides share (the pick tags
# swapped, the two lists swapped) passes them. The laws below spell the
# request and the reply with the wire primitives as Rust writes and reads
# them (crates/eukhe-tiny/src/roles.rs `decide`): the chain, then the
# available models, each a wire list of Nats (a model is the index of
# its first equal one in the chain, then the available models); the reply
# is 0 then the model for Use, 1 for Unavailable.

# a request as Rust spells it: the chain, the available models, then rest
def tiny_spell_req(q: FTn.Req, rest: String) -> String:
  match q:
    case FTn.Req{c, u}:
      LawsBase.wire_spell_nats(c, LawsBase.wire_spell_nats(u, rest))

# every count and model of a request fits the wire
def tiny_req_fits(q: FTn.Req) -> Bool:
  match q:
    case FTn.Req{+c, +u}:
      Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, c)), LawsBase.wire_nats_fit(c)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, u)), LawsBase.wire_nats_fit(u)))

# a pick as Rust reads it: 0 then the model (Use), 1 (Unavailable)
def tiny_spell_pick(p: Tn.Pick) -> String:
  match p:
    case Tn.Use{m}:
      Wr.put_nat(0n, Wr.put_nat(m, ""))
    case Tn.Unavailable{}:
      Wr.put_nat(1n, "")

# the spelled reply to a request: the model's pick (tiny_pick_first,
# tiny_pick_unavailable and tiny_terms_exact pin it)
def tiny_spell_answer(q: FTn.Req) -> String:
  match q:
    case FTn.Req{+c, +u}:
      tiny_spell_pick(Tn.pick(c, u))

# LAW tiny_ffi_answers_spelled: a request spelled as Rust writes it, every count and model
# within the wire, is answered with the pick as Rust reads it: 0 then the
# first model of the chain that is available, or 1 when none is
# EXCLUDES: a request or reply tag drift both sides of the Bend entry share
#   (Use and Unavailable swapped, the chain and the available models read
#   in the other order), a model id offset, a field lost or defaulted
law tiny_ffi_answers_spelled:
  for +q: FTn.Req
  for fits: {tiny_req_fits(q) == True{} : Bool}
  {FTn.ffi(tiny_spell_req(q, "")) == tiny_spell_answer(q) : String}

# LAW tiny_ffi_left_over_spelled: a spelled request that fits, followed by any more input,
# answers the error form "tiny: input left over"
# EXCLUDES: trailing input ignored, or read as part of the request, or
#   answered with another error text
law tiny_ffi_left_over_spelled:
  for +q: FTn.Req
  for fits: {tiny_req_fits(q) == True{} : Bool}
  for +c: Char
  for +t: String
  {FTn.ffi(tiny_spell_req(q, SCon{c, t})) == Wr.err("tiny: input left over") : String}

# LAW tiny_ffi_reads_only_requests: an answer that is not the error form answers a request: the
# input is exactly the spelling of a request whose counts and models fit
# the wire, and the answer is the spelled pick
# EXCLUDES: a decoder that accepts a missing list, a short list or input
#   left over, and answers it anyway (a default instead of the error form)
law tiny_ffi_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FTn.ffi(s)) == False{} : Bool}
  exs q: FTn.Req
  {(s, (tiny_req_fits(q), FTn.ffi(s))) == (tiny_spell_req(q, ""), (True{}, tiny_spell_answer(q))) : String & (Bool & String)}

# LAW tiny_ffi_malformed_unless_request: every answer but the error form "tiny: malformed
# request" comes from an input that begins with a spelled request that
# fits (with tiny_ffi_answers_spelled and tiny_ffi_left_over_spelled this
# pins the entry's answer to every input)
# EXCLUDES: the left-over error (or any answer) for input that does not
#   begin with a request, the malformed error spelled with another text
law tiny_ffi_malformed_unless_request:
  for +s: String
  for other: {String.eq(FTn.ffi(s), Wr.err("tiny: malformed request")) == False{} : Bool}
  exs q: FTn.Req
  exs rest: String
  {(s, tiny_req_fits(q)) == (tiny_spell_req(q, rest), True{}) : String & Bool}

# LAW tiny_ffi_tags_example: anchor: the bytes Rust sends and reads: the chain [a, b] with b
# available (ids 0, 1; b is 1 again in the available list) uses b (0,1,);
# the chain [a] with only c available (id 1) is Unavailable (1,); an empty
# chain is Unavailable; the chain [a, b] with a available uses a (0,0,); a
# missing available list and a short one are malformed; input after the
# request is left over
# EXCLUDES: a tag table both sides of the Bend entry agree on but Rust does
#   not (Use 0, Unavailable 1), the lists read in the other order
law tiny_ffi_tags_example:
  {[FTn.ffi("2,0,1,1,1,"), FTn.ffi("1,0,1,1,"), FTn.ffi("0,1,0,"), FTn.ffi("2,0,1,1,0,"), FTn.ffi("1,0,"), FTn.ffi("0,2,0,"), FTn.ffi("1,0,0,x")] == ["0,1,", "1,", "1,", "0,0,", Wr.err("tiny: malformed request"), Wr.err("tiny: malformed request"), Wr.err("tiny: input left over")] : List<&2, String>}
