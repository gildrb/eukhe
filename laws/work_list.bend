# eukhe: the laws of area work_list

import Base
import ../bend/work_list.bend as Wl
import ../bend/ffi_work_list.bend as FWl
import ../bend/wire.bend as Wr
import ../spec/agents/work_list.bend as S
import ./base.bend as LawsBase

# (T15) A child finishes its items or hands back stopped
# ------------------------------------------------------
# spec/README.md T15. bend/work_list.bend: the parent names a child's
# items (`items` of an `rlm.split` half, an `rlm.spawn` help leaf or a
# worker's task, `worker_assign`; a new task replaces the list); the child
# accounts for each,
# done or left with a reason (`rlm.items`). Its hand-back is Finished only
# when every item is accounted done, else Stopped naming the items left:
# the parent's notice and the child's status say `stopped`, never a
# success. It runs as the compiled core by bend/ffi_work_list.bend
# (eukhe-bend rules/work_list.rs), asked by the watch of every child given
# items (eukhe-core durable/children/task.rs). spec/agents/
# work_list.bend restates the rule (S1-S3). Every input is free: any
# number of items, each done or not.
#
# R1: the hand-back is Finished exactly when every item is done (S2).
# R2: a hand-back names an item left exactly when that item is open: left
#     with a reason or never accounted for (S1, S3).
# R3: the items left come in the parent's order, each once (S3).
# R4: the entry answers each request Rust writes (the count within the
#     wire) with the model's hand-back, reads exactly the request and
#     nothing after it, and answers any other input with the exact error
#     form `E work_list: malformed request`.
#
# Not pinned here: that Rust asks with one Bool per item the parent named,
# in its order, true only for an item the child accounted done, and that
# the parent's notice and the child's status show the items left: the
# Rust tests (durable/children/tests/work_list.rs) cover it.

# Spec helpers
# ------------

# R4: the items of a list of Bools, each spelled, then rest
def sp_w_bools(xs: List<&2, Bool>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      Wr.put_bool(x, sp_w_bools(t, rest))

# R4: the spelling of a request: the count of items, then one Bool per
# item (T done)
def sp_w_req(+done: List<&2, Bool>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Bool, done), sp_w_bools(done, rest))

# the count of items fits the wire
def sp_fit_req(done: List<&2, Bool>) -> Bool:
  LawsBase.wire_fits(List.length(&2, Bool, done))

# R4: the spelling of a reply: 0 finished; 1, then the items left
def sp_w_reply(o: Wl.Outcome) -> String:
  match o:
    case Wl.Finished{}:
      Wr.put_nat(0n, "")
    case Wl.Stopped{xs}:
      Wr.put_nat(1n, Wr.put_list(~Nat, ~Wr.put_nat, xs, ""))

# Laws: the hand-back (R1-R3)
# ---------------------------

# LAW work_list_finished_exactly_all_done (R1): the hand-back is Finished
# exactly when every item is done
# EXCLUDES: a child with open items handed back as finished (4 of 11 done,
#   reported a success), a finished list handed back as stopped, an
#   outcome read from the last item or the first only
law work_list_finished_exactly_all_done:
  for +done: List<&2, Bool>
  {S.finished(Wl.outcome(done)) == S.all_done(done) : Bool}

# LAW work_list_left_exactly_open (R2): position k is among the items a
# hand-back names left exactly when the item at k is open
# EXCLUDES: an open item missing from the list, a done item listed, a
#   position past the items listed, positions off by one
law work_list_left_exactly_open:
  for +done: List<&2, Bool>
  for +k: Nat
  {S.member(k, S.left(Wl.outcome(done))) == S.open_at(done, k) : Bool}

# LAW work_list_left_in_order (R3): the items left come in the parent's
# order, each once
# EXCLUDES: the items left reversed, repeated or out of order
law work_list_left_in_order:
  for +done: List<&2, Bool>
  {S.ascending(S.left(Wl.outcome(done))) == True{} : Bool}

# LAW work_list_example (R1-R3): anchor: no items, all done, two open
# items of four
# EXCLUDES: an empty list handed back as stopped, positions counted from 1
law work_list_example:
  {[Wl.outcome([]), Wl.outcome([True{}, True{}]), Wl.outcome([True{}, False{}, True{}, False{}])] == [Wl.Finished{}, Wl.Finished{}, Wl.Stopped{[1n, 3n]}] : List<&2, Wl.Outcome>}

# Laws: the entry (R4)
# --------------------

# LAW work_list_entry_is_model (R4): the entry answers every request Rust
# spells, the count within the wire, with the model's hand-back, spelled
# EXCLUDES: an item misread, a default, another reply spelling
law work_list_entry_is_model:
  for +done: List<&2, Bool>
  for h: {sp_fit_req(done) == True{} : Bool}
  {FWl.ffi(sp_w_req(done, "")) == sp_w_reply(Wl.outcome(done)) : String}

# LAW work_list_entry_reads (R4): the entry's decoder reads a spelled
# request back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law work_list_entry_reads:
  for +done: List<&2, Bool>
  for +rest: String
  for h: {sp_fit_req(done) == True{} : Bool}
  {FWl.get_req(sp_w_req(done, rest)) == Wr.Got{done, rest} : Wr.Dec<List<&2, Bool>>}

# LAW work_list_entry_exact (R4): every input the entry does not answer
# with the error form is a spelled request that fits the wire
# EXCLUDES: an answer for input that is no request (a malformed count or
#   item, input left over)
law work_list_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FWl.ffi(s)) == False{} : Bool}
  exs done: List<&2, Bool>
  {s == sp_w_req(done, "") : String} & {sp_fit_req(done) == True{} : Bool}

# LAW work_list_entry_refuses (R4): every error the entry answers is
# exactly `E work_list: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law work_list_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FWl.ffi(s)) == True{} : Bool}
  {FWl.ffi(s) == Wr.err("work_list: malformed request") : String}

# LAW work_list_entry_example (R4): anchor: the wire strings Rust sends and
# the replies it reads (no items, two done, two open of four); a malformed
# item, input left over
# EXCLUDES: another request or reply spelling
law work_list_entry_example:
  {[FWl.ffi("0,"), FWl.ffi("2,TT"), FWl.ffi("4,TFTF"), FWl.ffi("1,X"), FWl.ffi("1,TT")] == ["0,", "0,", "1,2,1,3,", Wr.err("work_list: malformed request"), Wr.err("work_list: malformed request")] : List<&2, String>}
