# eukhe: the laws of area tiny, section pick: the chain of models and the
# worker of one model (bend/tiny.bend sections 1 and 2), and the pick's
# entry (bend/ffi_tiny.bend)
#
# (S9) Local tiny models: the model in bend/tiny.bend (its header, lines
# 1-11: a role names a chain of models, the first available one serves).
# Every input is free: any chain of models, any
# set of available models, any needs of any processes with any tags, any
# worker exits, in any order.
#
# S9: a task goes to the first model of its chain that is available;
#     with none available it fails as Unavailable, never on a model
#     outside the chain [tiny_pick_in_chain, tiny_pick_first,
#     tiny_pick_unavailable]. One worker per model: every need of a
#     process gets exactly one outcome (joined, started, replaced)
#     [tiny_every_need_served]; a need with the running worker's tag
#     joins it [tiny_same_tag_joins]; after any events the worker runs
#     with the tag of the last need since the last exit
#     [tiny_worker_current]; the process election refines this model
#     (laws/tiny/elect.bend tiny_elect_is_worker_model, laws/tiny/run.bend
#     tiny_run_is_model).
# A1: the pick entry reads a request (the chain, then the available
#     models, as crates/eukhe-tiny/src/roles.rs writes them) and answers
#     the pick as Rust reads it; it decides only on such a request and
#     answers every other input with its exact error
#     [tiny_ffi_request_round_trip, tiny_ffi_answers,
#     tiny_ffi_answers_spelled, tiny_ffi_left_over_spelled,
#     tiny_ffi_reads_only_requests, tiny_ffi_malformed_unless_request;
#     anchor tiny_ffi_tags_example].
# A2: the model's terms the S9 laws read mean what the laws say: `elem`
#     is membership [tiny_elem_finds, tiny_elem_only_members]; `none_up`
#     holds exactly when no model of the list is available
#     [tiny_none_up_misses, tiny_none_up_only_when_none]; `needs` counts
#     the needs [tiny_needs_counts]; `last_tag` is the tag of the last
#     need since the last exit [tiny_last_tag_is_last]. Without A2 a
#     wrong model with its terms redefined to match passes S9's laws.

import Base
import ../../bend/ffi_tiny.bend as FTn
import ../../bend/tiny.bend as Tn
import ../../bend/wire.bend as Wr
import ../base.bend as LawsBase

# Laws: the chain (S9)
# --------------------

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

# Laws: the terms the pick laws read (A2)
# ---------------------------------------

# LAW tiny_elem_finds (A2): the membership test the pick laws read
# (`elem`) finds a model wherever it stands in a list: any models
# before it, any after it
# EXCLUDES: an `elem` that misses a model past the head or at the head
#   (tiny_pick_first would then claim a pick no chain gets)
law tiny_elem_finds:
  for +pre: List<&2, Nat>
  for +x: Nat
  for +post: List<&2, Nat>
  {Tn.elem(List.append(&2, Nat, pre, x <> post), x) == True{} : Bool}

# LAW tiny_elem_only_members (A2): `elem` answers True only for a model
# the list holds: the list is then some models, that model, and some more
# EXCLUDES: an `elem` that answers True for anything (a mutation probe
#   found it would leave tiny_pick_in_chain saying nothing)
law tiny_elem_only_members:
  for +xs: List<&2, Nat>
  for +x: Nat
  for hit: {Tn.elem(xs, x) == True{} : Bool}
  exs pre: List<&2, Nat>
  exs post: List<&2, Nat>
  {xs == List.append(&2, Nat, pre, x <> post) : List<&2, Nat>}

# LAW tiny_none_up_misses (A2): when `none_up` says that no model of a
# list is available, no model the list holds is available (`elem` of the
# available models answers False for it)
# EXCLUDES: a `none_up` that is True while a model of the list is
#   available (tiny_pick_unavailable would then claim Unavailable for a
#   chain with an available model)
law tiny_none_up_misses:
  for +pre: List<&2, Nat>
  for +x: Nat
  for +post: List<&2, Nat>
  for +up: List<&2, Nat>
  for none: {Tn.none_up(List.append(&2, Nat, pre, x <> post), up) == True{} : Bool}
  {Tn.elem(up, x) == False{} : Bool}

# LAW tiny_none_up_only_when_none (A2): `none_up` says False only when
# some model the list holds is available
# EXCLUDES: a `none_up` that is False for every chain (it would make
#   tiny_pick_unavailable and tiny_pick_first vacuous)
law tiny_none_up_only_when_none:
  for +xs: List<&2, Nat>
  for +up: List<&2, Nat>
  for some: {Tn.none_up(xs, up) == False{} : Bool}
  exs pre: List<&2, Nat>
  exs x: Nat
  exs post: List<&2, Nat>
  {xs == List.append(&2, Nat, pre, x <> post) : List<&2, Nat>} & {Tn.elem(up, x) == True{} : Bool}

# Laws: the worker of one model (S9)
# ----------------------------------

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

# Laws: the terms the worker laws read (A2)
# -----------------------------------------

# LAW tiny_needs_counts (A2): `needs` counts the needs among events: a
# need counts one, an exit none, and two runs of events one after the
# other count the sum of theirs
# EXCLUDES: a `needs` that misses or double-counts needs, or is constant
#   (with it tiny_every_need_served would pass a model that loses a need
#   or answers one twice: a fresh specification-completeness review
#   passed every worker law that way)
law tiny_needs_counts:
  for +a: List<&2, Tn.Ev>
  for +b: List<&2, Tn.Ev>
  for +p: Nat
  for +t: Nat
  {Tn.needs(List.append(&2, Tn.Ev, a, b)) == Nat.add(Tn.needs(a), Tn.needs(b)) : Nat} & {[Tn.needs([Tn.Need{p, t}]), Tn.needs([Tn.Gone{}])] == [1n, 0n] : List<&2, Nat>}

# LAW tiny_last_tag_is_last (A2): `last_tag` from a start value m is the
# tag of the last event when that event is a need of any process p, none
# when it is an exit, and m with no events
# EXCLUDES: a `last_tag` that reads the first need, keeps a tag past an
#   exit, or is constant (with it tiny_worker_current would pass a model
#   whose stale worker serves)
law tiny_last_tag_is_last:
  for +es: List<&2, Tn.Ev>
  for +m: Maybe<&2, Nat>
  for +p: Nat
  for +t: Nat
  {Tn.last_tag(List.append(&2, Tn.Ev, es, [Tn.Need{p, t}]), m) == Some{t} : Maybe<&2, Nat>} & {Tn.last_tag(List.append(&2, Tn.Ev, es, [Tn.Gone{}]), m) == None{} : Maybe<&2, Nat>} & {Tn.last_tag(Nil{}, m) == m : Maybe<&2, Nat>}

# Laws: the pick's entry (A1)
# ---------------------------

# LAW tiny_ffi_request_round_trip (A1, compiled core): the tiny pick entry (bend/ffi_tiny.bend)
# reads back a chain and the available models as its own encoder put_req writes them (every
# count and model within the wire), and leaves what follows untouched (the spelling Rust
# writes is tiny_ffi_answers_spelled's)
# EXCLUDES: a request field misread, dropped, reordered or shifted; a
#   decoder that eats the input after the request
law tiny_ffi_request_round_trip:
  for +chain: List<&2, Nat>
  for +up: List<&2, Nat>
  for +rest: String
  for h: {Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, chain)), LawsBase.wire_nats_fit(chain)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, up)), LawsBase.wire_nats_fit(up))) == True{} : Bool}
  {FTn.get_req(FTn.put_req(FTn.Req{chain, up}, rest)) == Wr.Got{FTn.Req{chain, up}, rest} : Wr.Dec<FTn.Req>}

# LAW tiny_ffi_answers (A1, compiled core): the tiny pick entry answers a whole request with the
# model's pick
# EXCLUDES: an entry that answers another rule, a default, or a reply for
#   a request it misread
law tiny_ffi_answers:
  for +chain: List<&2, Nat>
  for +up: List<&2, Nat>
  for h: {Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, chain)), LawsBase.wire_nats_fit(chain)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, up)), LawsBase.wire_nats_fit(up))) == True{} : Bool}
  {FTn.ffi(FTn.put_req(FTn.Req{chain, up}, "")) == FTn.put_pick(Tn.pick(chain, up), "") : String}

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
# tiny_pick_unavailable and the A2 laws on `elem` and `none_up` pin it)
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
