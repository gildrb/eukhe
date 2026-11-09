# eukhe: the laws of area admission: the stepper's wire
#
# The stepper bend/ffi_admission.bend runs the live controller eukhe
# runs (`Ad.Live.step`, tied to the model of laws/admission.bend by
# admission_live_step); these laws state its bytes (R1-R3 below).

import Base
import ../../bend/admission.bend as Ad
import ../../bend/ffi_admission.bend as FAd
import ../../bend/wire.bend as Wr
import ../base.bend as LawsBase

# ---- admission_wire ----

# The wire codec of bend/ffi_admission.bend (the stepper of the compiled
# Bend core; grammar: that file's header, crates/eukhe-bend/WIRE.md). R1:
# every value the stepper and Rust exchange reads back; R2: a well-formed
# open or step answers the model's new controller, encoded; R3: a
# malformed or overlong input answers the error form and changes nothing.
# Every input is free: any limits, any op, any controller, any text.

# what fits the wire: every Nat (and every list length) at most 14 digits
def adw_lim_fits(l: Ad.Lim) -> Bool:
  match l:
    case Ad.Unl{}:
      True{}
    case Ad.Cap{p}:
      LawsBase.wire_fits(p)

def adw_lv_fits(t: Ad.Lv) -> Bool:
  match t:
    case Ad.Lv{k, c, s}:
      LawsBase.wire_fits(k)

def adw_lvs_fit(ts: List<&2, Ad.Lv>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case Con{t, u}:
      Bool.and(adw_lv_fits(t), adw_lvs_fit(u))

def adw_live_fits(x: Ad.Live) -> Bool:
  match x:
    case Ad.Live{l, q, +ts, n}:
      Bool.and(adw_lim_fits(l), Bool.and(LawsBase.wire_fits(q), Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Ad.Lv, ts)), adw_lvs_fit(ts)), LawsBase.wire_fits(n))))

def adw_op_fits(o: Ad.Op) -> Bool:
  match o:
    case Ad.Admit{c}:
      True{}
    case Ad.Collect{k}:
      LawsBase.wire_fits(k)
    case Ad.Release{k}:
      LawsBase.wire_fits(k)
    case Ad.Leave{k}:
      LawsBase.wire_fits(k)
    case Ad.Limit{l, q}:
      Bool.and(adw_lim_fits(l), LawsBase.wire_fits(q))

# LAW adw_cls_round_trip (R1): a ticket's class reads back, and the rest is untouched
# EXCLUDES: swapped class tags, a class that eats the rest
law adw_cls_round_trip:
  for c: Ad.Cls
  for rest: String
  {FAd.get_cls(FAd.put_cls(c, rest)) == Wr.Got{c, rest} : Wr.Dec<Ad.Cls>}

# LAW adw_sts_round_trip (R1): a ticket's status reads back, and the rest is untouched
# EXCLUDES: two statuses with one tag, a status read as another
law adw_sts_round_trip:
  for s: Ad.Sts
  for rest: String
  {FAd.get_sts(FAd.put_sts(s, rest)) == Wr.Got{s, rest} : Wr.Dec<Ad.Sts>}

# LAW adw_lim_round_trip (R1): a limit that fits reads back, and the rest is untouched
# EXCLUDES: a cap read as unlimited, a misread slot count
law adw_lim_round_trip:
  for +l: Ad.Lim
  for rest: String
  for h: {adw_lim_fits(l) == True{} : Bool}
  {FAd.get_lim(FAd.put_lim(l, rest)) == Wr.Got{l, rest} : Wr.Dec<Ad.Lim>}

# LAW adw_lv_round_trip (R1): a live ticket that fits reads back, and the rest is untouched
# EXCLUDES: a ticket's number, class or status lost or misread
law adw_lv_round_trip:
  for +t: Ad.Lv
  for rest: String
  for h: {adw_lv_fits(t) == True{} : Bool}
  {FAd.get_lv(FAd.put_lv(t, rest)) == Wr.Got{t, rest} : Wr.Dec<Ad.Lv>}

# LAW adw_lvs_round_trip (R1): a list of live tickets that fit, of a length that fits, reads back
# EXCLUDES: tickets lost, added, reordered or misread, a wrong count
law adw_lvs_round_trip:
  for +ts: List<&2, Ad.Lv>
  for rest: String
  for h: {Bool.and(LawsBase.wire_fits(List.length(&2, Ad.Lv, ts)), adw_lvs_fit(ts)) == True{} : Bool}
  {Wr.get_list(~Ad.Lv, ~FAd.get_lv, Wr.put_list(~Ad.Lv, ~FAd.put_lv, ts, rest)) == Wr.Got{ts, rest} : Wr.Dec<List<&2, Ad.Lv>>}

# LAW adw_live_round_trip (R1): the reply, a controller that fits, reads back
# EXCLUDES: a reply that drops or misreads the limits, a ticket or the
#   next ticket's number
law adw_live_round_trip:
  for +x: Ad.Live
  for rest: String
  for h: {adw_live_fits(x) == True{} : Bool}
  {FAd.get_live(FAd.put_live(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Ad.Live>}

# LAW adw_op_round_trip (R1): the request of a step, an op that fits, reads back
# EXCLUDES: one op read as another, a misread ticket number or limit
law adw_op_round_trip:
  for +o: Ad.Op
  for rest: String
  for h: {adw_op_fits(o) == True{} : Bool}
  {FAd.get_op(FAd.put_op(o, rest)) == Wr.Got{o, rest} : Wr.Dec<Ad.Op>}

# LAW adw_open_round_trip (R1): the request of an open, limits that fit, reads back
# EXCLUDES: the limit and providerMaxQueued swapped or misread
law adw_open_round_trip:
  for +l: Ad.Lim
  for +q: Nat
  for rest: String
  for h: {Bool.and(adw_lim_fits(l), LawsBase.wire_fits(q)) == True{} : Bool}
  {FAd.get_open(FAd.put_lim(l, Wr.put_nat(q, rest))) == Wr.Got{(l, q), rest} : Wr.Dec<+Sigma<Ad.Lim, x => Nat>>}

# LAW adw_open_malformed (R3): a malformed open opens the refused state, with the error form
# EXCLUDES: a default controller for malformed limits
law adw_open_malformed:
  for +s: String
  for h: {FAd.get_open(s) == Wr.Bad{} : Wr.Dec<+Sigma<Ad.Lim, x => Nat>>}
  {FAd.open(s) == (FAd.Shut{}, Wr.err("admission: malformed open")) : FAd.St & String}

# LAW adw_step_malformed (R3): a malformed op answers the error form and keeps the controller
# EXCLUDES: a guessed op, a controller lost or changed by a bad input
law adw_step_malformed:
  for x: Ad.Live
  for +s: String
  for h: {FAd.get_op(s) == Wr.Bad{} : Wr.Dec<Ad.Op>}
  {FAd.step(FAd.Running{x}, s) == (FAd.Running{x}, Wr.err("admission: malformed op")) : FAd.St & String}

# LAW adw_shut_refuses (R3): the refused state answers every step with the error form
# EXCLUDES: a refused open that later runs ops on a made-up controller
law adw_shut_refuses:
  for s: String
  {FAd.step(FAd.Shut{}, s) == (FAd.Shut{}, Wr.err("admission: the open was refused")) : FAd.St & String}

# LAW adw_tags_example (R1): anchor: the tags of the header (Cls 0 interactive | 1 background;
# Sts 0 queued | 1 granted | 2 held | 3 preempted | 4 ended)
# EXCLUDES: tags in another order than the grammar's
law adw_tags_example:
  {FAd.put_cls(Ad.Ia{}, FAd.put_cls(Ad.Bg{}, "")) == "0,1," : String} & {FAd.put_sts(Ad.Queued{}, FAd.put_sts(Ad.Granted{}, FAd.put_sts(Ad.Held{}, FAd.put_sts(Ad.Preempted{}, FAd.put_sts(Ad.Ended{}, ""))))) == "0,1,2,3,4," : String}

# LAW adw_lim_example (R1): anchor and witness: a cap of 1 + 2 slots is 1, 2
# EXCLUDES: a vacuous adw_lim_round_trip, a cap spelled otherwise
law adw_lim_example:
  {adw_lim_fits(Ad.Cap{2n}) == True{} : Bool} & {FAd.put_lim(Ad.Cap{2n}, FAd.put_lim(Ad.Unl{}, "")) == "1,2,0," : String}

# LAW adw_lv_example (R1): anchor and witness: a live ticket is its number, class, status
# EXCLUDES: a vacuous adw_lv_round_trip, fields in another order
law adw_lv_example:
  {adw_lv_fits(Ad.Lv{3n, Ad.Bg{}, Ad.Preempted{}}) == True{} : Bool} & {FAd.put_lv(Ad.Lv{3n, Ad.Bg{}, Ad.Preempted{}}, "") == "3,1,3," : String}

# LAW adw_lvs_example (R1): anchor and witness: a list of tickets is its count, then them
# EXCLUDES: a vacuous adw_lvs_round_trip
law adw_lvs_example:
  {Bool.and(LawsBase.wire_fits(List.length(&2, Ad.Lv, [Ad.Lv{0n, Ad.Ia{}, Ad.Queued{}}, Ad.Lv{1n, Ad.Bg{}, Ad.Ended{}}])), adw_lvs_fit([Ad.Lv{0n, Ad.Ia{}, Ad.Queued{}}, Ad.Lv{1n, Ad.Bg{}, Ad.Ended{}}])) == True{} : Bool} & {Wr.put_list(~Ad.Lv, ~FAd.put_lv, [Ad.Lv{0n, Ad.Ia{}, Ad.Queued{}}, Ad.Lv{1n, Ad.Bg{}, Ad.Ended{}}], "") == "2,0,0,0,1,1,4," : String}

# LAW adw_live_example (R1): anchor and witness: a controller is its limit, providerMaxQueued,
# live tickets and next ticket's number
# EXCLUDES: a vacuous adw_live_round_trip, fields in another order
law adw_live_example:
  {adw_live_fits(Ad.Live{Ad.Cap{0n}, 1n, [Ad.Lv{1n, Ad.Ia{}, Ad.Granted{}}], 2n}) == True{} : Bool} & {FAd.put_live(Ad.Live{Ad.Cap{0n}, 1n, [Ad.Lv{1n, Ad.Ia{}, Ad.Granted{}}], 2n}, "") == "1,0,1,1,1,0,1,2," : String}

# LAW adw_op_example (R1): anchor and witness: every op's tag and fields
# EXCLUDES: a vacuous adw_op_round_trip, op tags in another order
law adw_op_example:
  {adw_op_fits(Ad.Limit{Ad.Cap{2n}, 3n}) == True{} : Bool} & {FAd.put_op(Ad.Admit{Ad.Bg{}}, FAd.put_op(Ad.Collect{5n}, FAd.put_op(Ad.Release{6n}, FAd.put_op(Ad.Leave{7n}, FAd.put_op(Ad.Limit{Ad.Cap{2n}, 3n}, ""))))) == "0,1,1,5,2,6,3,7,4,1,2,3," : String}

# LAW adw_open_example (R2): anchor and witness: open on 0, 3 (unlimited, 3 queued) answers
# the controller with no ticket
# EXCLUDES: a vacuous adw_open_answers_spelled, an open that grants or numbers
#   tickets before any op
law adw_open_example:
  {Bool.and(adw_lim_fits(Ad.Unl{}), LawsBase.wire_fits(3n)) == True{} : Bool} & {FAd.open("0,3,") == (FAd.Running{Ad.Live{Ad.Unl{}, 3n, Nil{}, 0n}}, "0,3,0,0,") : FAd.St & String}

# LAW adw_malformed_example (R3): witness: malformed inputs exist (an unknown limit tag, an
# unknown op tag)
# EXCLUDES: a vacuous adw_open_malformed or adw_step_malformed
law adw_malformed_example:
  {FAd.get_open("2,0,") == Wr.Bad{} : Wr.Dec<+Sigma<Ad.Lim, x => Nat>>} & {FAd.get_op("5,") == Wr.Bad{} : Wr.Dec<Ad.Op>}

# ---- admission_stepper ----

# The stepper's bytes, spelled from the wire primitives alone (never the
# entry's put_* / get_*), as crates/eukhe-core/src/admission/live.rs
# writes the requests and reads the replies: a constructor is its tag
# (declaration order), then its fields. An open answers the new
# controller, spelled, or the error form with the refused state; a step
# on a running controller answers the model's next controller, spelled,
# or the error form with the controller kept (adw_shut_refuses pins the
# refused state). Every input is free: any limits, any op, any
# controller, any text.

# a class: interactive 0, background 1
def adw_spell_cls(c: Ad.Cls, rest: String) -> String:
  match c:
    case Ad.Ia{}:
      Wr.put_nat(0n, rest)
    case Ad.Bg{}:
      Wr.put_nat(1n, rest)

# a ticket's status: queued 0, granted 1, held 2, preempted 3, ended 4
def adw_spell_sts(s: Ad.Sts, rest: String) -> String:
  match s:
    case Ad.Queued{}:
      Wr.put_nat(0n, rest)
    case Ad.Granted{}:
      Wr.put_nat(1n, rest)
    case Ad.Held{}:
      Wr.put_nat(2n, rest)
    case Ad.Preempted{}:
      Wr.put_nat(3n, rest)
    case Ad.Ended{}:
      Wr.put_nat(4n, rest)

# a limit: unlimited 0, or 1 then p (1 + p slots)
def adw_spell_lim(l: Ad.Lim, rest: String) -> String:
  match l:
    case Ad.Unl{}:
      Wr.put_nat(0n, rest)
    case Ad.Cap{p}:
      Wr.put_nat(1n, Wr.put_nat(p, rest))

# a live ticket: its number, class and status
def adw_spell_lv(t: Ad.Lv, rest: String) -> String:
  match t:
    case Ad.Lv{k, c, s}:
      Wr.put_nat(k, adw_spell_cls(c, adw_spell_sts(s, rest)))

# the live tickets of ts, each spelled, then rest
def adw_spell_lvs.items(ts: List<&2, Ad.Lv>, rest: String) -> String:
  match ts:
    case Nil{}:
      rest
    case Con{t, u}:
      adw_spell_lv(t, adw_spell_lvs.items(u, rest))

# a list of live tickets: its count, then each ticket
def adw_spell_lvs(+ts: List<&2, Ad.Lv>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Ad.Lv, ts), adw_spell_lvs.items(ts, rest))

# a controller (every reply but the error form): its limit,
# providerMaxQueued, live tickets and next ticket's number
def adw_spell_live(x: Ad.Live, rest: String) -> String:
  match x:
    case Ad.Live{l, q, ts, n}:
      adw_spell_lim(l, Wr.put_nat(q, adw_spell_lvs(ts, Wr.put_nat(n, rest))))

# an op (the request of a step): admit 0 then the class; collect 1,
# release 2, leave 3, each then the ticket's number; limits 4 then the
# limit and providerMaxQueued
def adw_spell_op(o: Ad.Op, rest: String) -> String:
  match o:
    case Ad.Admit{c}:
      Wr.put_nat(0n, adw_spell_cls(c, rest))
    case Ad.Collect{k}:
      Wr.put_nat(1n, Wr.put_nat(k, rest))
    case Ad.Release{k}:
      Wr.put_nat(2n, Wr.put_nat(k, rest))
    case Ad.Leave{k}:
      Wr.put_nat(3n, Wr.put_nat(k, rest))
    case Ad.Limit{l, q}:
      Wr.put_nat(4n, adw_spell_lim(l, Wr.put_nat(q, rest)))

# the request of an open: the limit, then providerMaxQueued
def adw_spell_open(l: Ad.Lim, q: Nat, rest: String) -> String:
  adw_spell_lim(l, Wr.put_nat(q, rest))

# the reply of an answer of the stepper (the bytes Rust reads)
def adw_reply(a: FAd.St & String) -> String:
  match a:
    case (st, r):
      r

# the state an answer of the stepper keeps (the next step's state)
def adw_state(a: FAd.St & String) -> FAd.St:
  match a:
    case (st, r):
      st

# the replies of the steps ins, in order, from state st, each step on the
# state the one before kept
def adw_feed(ins: List<&2, String>, +st: FAd.St) -> List<&2, String>:
  match ins:
    case Nil{}:
      Nil{}
    case Con{+i, rest}:
      adw_reply(FAd.step(st, i)) <> adw_feed(rest, adw_state(FAd.step(st, i)))

# LAW adw_open_answers_spelled (R2): an open spelled by the grammar (the limit, then
# providerMaxQueued), every number within the wire, answers the controller
# with those limits, no ticket and next ticket 0, spelled by the grammar,
# and keeps it
# EXCLUDES: a limit tag that drifts from the grammar Rust writes and reads
#   (on the entry's encoder and decoder alike), the limits swapped,
#   misread or defaulted, a ticket or next number made up, a reply spelled
#   another way, a state that is not the reply's
law adw_open_answers_spelled:
  for +l: Ad.Lim
  for +q: Nat
  for fits: {Bool.and(adw_lim_fits(l), LawsBase.wire_fits(q)) == True{} : Bool}
  {FAd.open(adw_spell_open(l, q, "")) == (FAd.Running{Ad.Live{l, q, Nil{}, 0n}}, adw_spell_live(Ad.Live{l, q, Nil{}, 0n}, "")) : FAd.St & String}

# LAW adw_open_left_over_spelled (R3): a spelled open that fits, followed by any more input,
# opens the refused state with the error form "admission: input left over"
# EXCLUDES: trailing input ignored, or read as part of the open, a
#   controller opened on it, the error spelled with another text
law adw_open_left_over_spelled:
  for +l: Ad.Lim
  for +q: Nat
  for fits: {Bool.and(adw_lim_fits(l), LawsBase.wire_fits(q)) == True{} : Bool}
  for +c: Char
  for +t: String
  {FAd.open(adw_spell_open(l, q, SCon{c, t})) == (FAd.Shut{}, Wr.err("admission: input left over")) : FAd.St & String}

# LAW adw_open_unknown_lim (R3): a limit tag of 2 or more (of any length) opens the refused
# state with the error form "admission: malformed open", whatever follows
# EXCLUDES: an unknown limit tag read as unlimited or a cap, or answered
#   with another error
law adw_open_unknown_lim:
  for +n: Nat
  for +rest: String
  {FAd.open(Wr.put_nat(2n+n, rest)) == (FAd.Shut{}, Wr.err("admission: malformed open")) : FAd.St & String}

# LAW adw_open_malformed_unless_request (R3): every open answered other than with the error form
# "admission: malformed open" begins with a spelled open that fits
# EXCLUDES: a decoder that accepts an unknown tag, a missing field or a
#   number past the wire; the left-over error (or any answer) for input
#   that does not begin with an open; the malformed error spelled with
#   another text
law adw_open_malformed_unless_request:
  for +s: String
  for other: {String.eq(adw_reply(FAd.open(s)), Wr.err("admission: malformed open")) == False{} : Bool}
  exs l: Ad.Lim
  exs q: Nat
  exs rest: String
  {(s, Bool.and(adw_lim_fits(l), LawsBase.wire_fits(q))) == (adw_spell_open(l, q, rest), True{}) : String & Bool}

# LAW adw_open_refused_shut (R3): every open answered with the error form opens the refused state
# EXCLUDES: a controller (made up or half read) kept after a refused open
law adw_open_refused_shut:
  for +s: String
  for err: {LawsBase.wire_opens_err(adw_reply(FAd.open(s))) == True{} : Bool}
  {adw_state(FAd.open(s)) == FAd.Shut{} : FAd.St}

# LAW adw_open_reads_only_requests (R2): an open answered other than with the error form is a
# request: the input is exactly a spelled open that fits, and the answer
# is its controller, kept and spelled
# EXCLUDES: a decoder that accepts an unknown tag, a missing or extra
#   field or input left over, and opens a controller anyway (a default
#   instead of the error form)
law adw_open_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(adw_reply(FAd.open(s))) == False{} : Bool}
  exs l: Ad.Lim
  exs q: Nat
  {(s, (Bool.and(adw_lim_fits(l), LawsBase.wire_fits(q)), FAd.open(s))) == (adw_spell_open(l, q, ""), (True{}, (FAd.Running{Ad.Live{l, q, Nil{}, 0n}}, adw_spell_live(Ad.Live{l, q, Nil{}, 0n}, "")))) : String & (Bool & (FAd.St & String))}

# LAW adw_step_answers_spelled (R2): on any controller, an op spelled by the grammar, every
# number within the wire, answers the model's next controller (Live.step),
# spelled by the grammar, and keeps it
# EXCLUDES: an op, class, limit or status tag that drifts from the grammar
#   Rust writes and reads (on the entry's encoder and decoder alike), an
#   op's field lost, swapped or defaulted, a ticket's fields in another
#   order, a wrong count, a reply spelled another way, a state that is not
#   the reply's
law adw_step_answers_spelled:
  for +x: Ad.Live
  for +o: Ad.Op
  for fits: {adw_op_fits(o) == True{} : Bool}
  {FAd.step(FAd.Running{x}, adw_spell_op(o, "")) == (FAd.Running{Ad.Live.step(x, o)}, adw_spell_live(Ad.Live.step(x, o), "")) : FAd.St & String}

# LAW adw_step_left_over_spelled (R3): a spelled op that fits, followed by any more input,
# answers the error form "admission: input left over" and keeps the
# controller
# EXCLUDES: trailing input ignored, or read as part of the op, an op run
#   on it, the error spelled with another text
law adw_step_left_over_spelled:
  for +x: Ad.Live
  for +o: Ad.Op
  for fits: {adw_op_fits(o) == True{} : Bool}
  for +c: Char
  for +t: String
  {FAd.step(FAd.Running{x}, adw_spell_op(o, SCon{c, t})) == (FAd.Running{x}, Wr.err("admission: input left over")) : FAd.St & String}

# LAW adw_step_unknown_op (R3): an op tag of 5 or more (of any length) answers the error form
# "admission: malformed op" and keeps the controller, whatever follows
# EXCLUDES: an unknown op read as a known one, or answered with another
#   error
law adw_step_unknown_op:
  for +x: Ad.Live
  for +n: Nat
  for +rest: String
  {FAd.step(FAd.Running{x}, Wr.put_nat(5n+n, rest)) == (FAd.Running{x}, Wr.err("admission: malformed op")) : FAd.St & String}

# LAW adw_step_malformed_unless_op (R3): every step answered other than with the error form
# "admission: malformed op" begins with a spelled op that fits
# EXCLUDES: a decoder that accepts an unknown tag (op, class, limit), a
#   missing field or a number past the wire; the left-over error (or any
#   answer) for input that does not begin with an op; the malformed error
#   spelled with another text
law adw_step_malformed_unless_op:
  for +x: Ad.Live
  for +s: String
  for other: {String.eq(adw_reply(FAd.step(FAd.Running{x}, s)), Wr.err("admission: malformed op")) == False{} : Bool}
  exs o: Ad.Op
  exs rest: String
  {(s, adw_op_fits(o)) == (adw_spell_op(o, rest), True{}) : String & Bool}

# LAW adw_step_refused_keeps (R3): every step answered with the error form keeps the controller
# EXCLUDES: a controller lost, changed or refused by a bad input
law adw_step_refused_keeps:
  for +x: Ad.Live
  for +s: String
  for err: {LawsBase.wire_opens_err(adw_reply(FAd.step(FAd.Running{x}, s))) == True{} : Bool}
  {adw_state(FAd.step(FAd.Running{x}, s)) == FAd.Running{x} : FAd.St}

# LAW adw_step_reads_only_ops (R2): a step answered other than with the error form is an op:
# the input is exactly a spelled op that fits, and the answer is the
# model's next controller, kept and spelled
# EXCLUDES: a decoder that accepts an unknown tag, a missing or extra
#   field or input left over, and runs an op anyway (a default instead of
#   the error form)
law adw_step_reads_only_ops:
  for +x: Ad.Live
  for +s: String
  for ok: {LawsBase.wire_opens_err(adw_reply(FAd.step(FAd.Running{x}, s))) == False{} : Bool}
  exs o: Ad.Op
  {(s, (adw_op_fits(o), FAd.step(FAd.Running{x}, s))) == (adw_spell_op(o, ""), (True{}, (FAd.Running{Ad.Live.step(x, o)}, adw_spell_live(Ad.Live.step(x, o), "")))) : String & (Bool & (FAd.St & String))}

# LAW adw_stepper_example (R1): anchor: the bytes Rust sends and reads. Open one slot, one
# queued (1,0,1,): no ticket, next 0. Then a background admit is held
# (ticket 0: 0,1,2); an interactive admit preempts it (0,1,3) and holds
# (1,0,2); a second waits (2,0,0); an op tag 5, a collect with input left
# over, a limit tag 2 and a class tag 2 are refused, the controller kept;
# a release of 1 leaves and grants 2 (2,0,1), whose collect holds it
# (2,0,2); limits unlimited, 0 queued. An open with limit tag 2, with
# input left over, or cut short is refused, and the refused state
# refuses every step
# EXCLUDES: request or reply tags in another order than the grammar's,
#   fields in another order, an error kept as state, error texts swapped
law adw_stepper_example:
  {(adw_reply(FAd.open("1,0,1,")), adw_feed(["0,1,", "0,0,", "0,0,", "5,", "1,2,x", "4,2,0,", "0,2,", "2,1,", "1,2,", "4,0,0,"], adw_state(FAd.open("1,0,1,")))) == ("1,0,1,0,0,", ["1,0,1,1,0,1,2,1,", "1,0,1,2,0,1,3,1,0,2,2,", "1,0,1,3,0,1,3,1,0,2,2,0,0,3,", Wr.err("admission: malformed op"), Wr.err("admission: input left over"), Wr.err("admission: malformed op"), Wr.err("admission: malformed op"), "1,0,1,2,0,1,3,2,0,1,3,", "1,0,1,2,0,1,3,2,0,2,3,", "0,0,2,0,1,3,2,0,2,3,"]) : String & List<&2, String>} & {[adw_reply(FAd.open("2,0,")), adw_reply(FAd.open("0,3,x")), adw_reply(FAd.open("1,")), adw_reply(FAd.step(adw_state(FAd.open("0,3,x")), "0,0,"))] == [Wr.err("admission: malformed open"), Wr.err("admission: input left over"), Wr.err("admission: malformed open"), Wr.err("admission: the open was refused")] : List<&2, String>}
