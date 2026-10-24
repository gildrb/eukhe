# eukhe: the laws of area notice

import Base
import ../bend/notice.bend as No
import ../bend/ffi_notice.bend as FNo
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# The rank of a version, read by semver.bend's reader (the spec): the text
# before the first '-' read as a version X.Y.Z (Sv.Ver.parse: decimal
# numbers without leading zeros, three of them, nothing else) whose
# numbers have at most 14 digits; [X, Y, 0, Z] with a '-' (a prerelease),
# [X, Y, 1, Z] without; [] for any other text. A number of 15 digits or
# more is past the range of the compiled core's numbers (2^48 - 1): its
# version has no rank, as text that is no version. A text of more than 64
# chars has no rank either (no version is that long): the first 65 chars
# of any text decide its rank, so Rust sends only those.

# LAW notice_shown_once: an attach never shows a kernel restore notice again. After any
# restores, live notices and attaches (reconnects, worker restarts), in
# any order, each stored notice showed at most once (bend/notice.bend;
# the bridge is crates/eukhe-tui/src/restore_notices.rs)
law notice_shown_once:
  for +evs: List<&2, No.Ev>
  {No.once(No.run(evs)) == True{} : Bool}

# LAW notice_per_restore: restore notices do not accumulate. After any events and one more
# attach, the restore rows the view showed equal the restores
law notice_per_restore:
  for +evs: List<&2, No.Ev>
  {No.total(No.run(List.append(&2, No.Ev, evs, [No.Reconnect{}]))) == No.restores(evs) : Nat}

# ---- the rule (bend/notice.bend, run by bend/ffi_notice.bend) ----
#
# LAWS: the kernel restore notices a TUI view shows
# (crates/eukhe-tui/src/restore_notices.rs `RestoreNotices` keeps the
# compiled stepper of bend/ffi_notice.bend; docs/daemon.md D1). A message
# is another role or a custom message (its kind and its stamp, as text);
# the view asks whether a message of a session shows, and records the
# messages of a session it shows. Every input is free: any session ids,
# kinds, stamps, messages and asks, in any order.
#
# R1: a restore notice (a custom message of kind ipython_state_restored)
#     that the view recorded for a session never shows again for that
#     session, whatever it records after.
# R2: a restore notice shows while no record of its session holds its
#     stamp.
# R3: every other message (another role, a custom message of another
#     kind) shows.
# R4: sessions are kept apart: what the view records for one session
#     never changes what shows for another.
# R5: asking whether a message shows changes nothing; only a record does.
# R6: after any restores, live notices and attaches, run as eukhe runs
#     them (an attach shows the stored messages that show, then records
#     them), each stored notice showed at most once, and after one more
#     attach exactly once: the counts of the model of the scenario.
# R7: the entry reads exactly the asks Rust spells (WIRE.md) and answers
#     the rule's answer; any other input answers the error form and keeps
#     the record; an open with input is refused, and a refused open
#     answers every step with the error form.

# Spec helpers
# ------------

# a and b hold the same chars, in the same order
def nt_eq(a: String, b: String) -> Bool:
  match a b:
    case SNil{} SNil{}:
      True{}
    case SNil{} SCon{d, u}:
      False{}
    case SCon{c, t} SNil{}:
      False{}
    case SCon{c, t} SCon{d, u}:
      Bool.and(Char.is_eq(c, d), nt_eq(t, u))

# the kind of a restore notice (eukhe-types `CustomType::IpythonStateRestored`)
def nt_kind() -> String:
  "ipython_state_restored"

# m is a restore notice stamped s
def nt_is(m: No.Msg, +s: String) -> Bool:
  match m:
    case No.Other{}:
      False{}
    case No.Custom{k, t}:
      Bool.and(nt_eq(k, nt_kind()), nt_eq(t, s))

# ms holds a restore notice stamped s
def nt_has(ms: List<&2, No.Msg>, +s: String) -> Bool:
  match ms:
    case Nil{}:
      False{}
    case m <> t:
      Bool.or(nt_is(m, s), nt_has(t, s))

# a record among the asks qs is of session sid and holds a restore notice
# stamped s (the order of the asks does not matter)
def nt_noted(qs: List<&2, No.Ask>, +sid: String, +s: String) -> Bool:
  match qs:
    case Nil{}:
      False{}
    case q <> t:
      match q:
        case No.Shows{a, m}:
          nt_noted(t, sid, s)
        case No.Notes{a, ms}:
          Bool.or(Bool.and(nt_eq(a, sid), nt_has(ms, s)), nt_noted(t, sid, s))

# after the asks qs, m of session sid shows: it is no restore notice, or
# no record of sid among qs holds its stamp
def nt_shows(qs: List<&2, No.Ask>, +sid: String, m: No.Msg) -> Bool:
  match m:
    case No.Other{}:
      True{}
    case No.Custom{k, s}:
      Bool.not(Bool.and(nt_eq(k, nt_kind()), nt_noted(qs, sid, s)))

# the record after the asks qs (the newest first), each run by No.answer
def nt_book.after(r: List<&2, No.Seen> & No.Ans) -> List<&2, No.Seen>:
  (rs, a) = r
  rs

def nt_book(qs: List<&2, No.Ask>) -> List<&2, No.Seen>:
  match qs:
    case Nil{}:
      Nil{}
    case q <> t:
      nt_book.after(No.answer(nt_book(t), q))

# The wire (spec spellers over the primitives of bend/wire.bend)
# --------

# a message as Rust writes it
def nt_spell_msg(m: No.Msg, rest: String) -> String:
  match m:
    case No.Other{}:
      Wr.put_nat(0n, rest)
    case No.Custom{k, s}:
      Wr.put_nat(1n, Wr.put_str(k, Wr.put_str(s, rest)))

# an ask as Rust writes it
def nt_spell_ask(q: No.Ask, rest: String) -> String:
  match q:
    case No.Shows{sid, m}:
      Wr.put_nat(0n, Wr.put_str(sid, nt_spell_msg(m, rest)))
    case No.Notes{sid, ms}:
      Wr.put_nat(1n, Wr.put_str(sid, Wr.put_list(~No.Msg, ~nt_spell_msg, ms, rest)))

# an answer as Rust reads it
def nt_spell_ans(a: No.Ans) -> String:
  match a:
    case No.Shown{b}:
      Wr.put_bool(b, "")
    case No.Noted{}:
      ""

# the stepper's state and reply after an answer of the rule
def nt_spell_step(r: List<&2, No.Seen> & No.Ans) -> FNo.St & String:
  (rs, a) = r
  (FNo.Live{rs}, nt_spell_ans(a))

# the reply of a step
def nt_out(r: FNo.St & String) -> String:
  (st, out) = r
  out

# s has a length that fits the wire
def nt_str_fits(s: String) -> Bool:
  LawsBase.wire_fits(String.length(s))

def nt_msg_fits(m: No.Msg) -> Bool:
  match m:
    case No.Other{}:
      True{}
    case No.Custom{k, s}:
      Bool.and(nt_str_fits(k), nt_str_fits(s))

def nt_msgs_fit(ms: List<&2, No.Msg>) -> Bool:
  match ms:
    case Nil{}:
      True{}
    case m <> t:
      Bool.and(nt_msg_fits(m), nt_msgs_fit(t))

# every count and every length of an ask fits the wire
def nt_ask_fits(q: No.Ask) -> Bool:
  match q:
    case No.Shows{sid, m}:
      Bool.and(nt_str_fits(sid), nt_msg_fits(m))
    case No.Notes{sid, +ms}:
      Bool.and(nt_str_fits(sid), Bool.and(LawsBase.wire_fits(List.length(&2, No.Msg, ms)), nt_msgs_fit(ms)))

def nt_asks_fit(qs: List<&2, No.Ask>) -> Bool:
  match qs:
    case Nil{}:
      True{}
    case q <> t:
      Bool.and(nt_ask_fits(q), nt_asks_fit(t))

# the reply the rule gives to q after the asks past
def nt_reply(past: List<&2, No.Ask>, q: No.Ask) -> String:
  match q:
    case No.Shows{sid, m}:
      Wr.put_bool(nt_shows(past, sid, m), "")
    case No.Notes{sid, ms}:
      ""

# the replies to the asks qs after the asks past (the newest first)
def nt_replies(qs: List<&2, No.Ask>, +past: List<&2, No.Ask>) -> List<&2, String>:
  match qs:
    case Nil{}:
      Nil{}
    case +q <> t:
      nt_reply(past, q) <> nt_replies(t, q <> past)

# the reply r, then the replies of the shipped stepper to the asks qs
# spelled on the wire, one step each from the state of r
def nt_run(qs: List<&2, No.Ask>, r: FNo.St & String) -> List<&2, String>:
  match qs:
    case Nil{}:
      (st, out) = r
      [out]
    case q <> t:
      (st, out) = r
      out <> nt_run(t, FNo.step(st, nt_spell_ask(q, "")))

# the same over raw inputs
def nt_feed(ins: List<&2, String>, r: FNo.St & String) -> List<&2, String>:
  match ins:
    case Nil{}:
      (st, out) = r
      [out]
    case i <> t:
      (st, out) = r
      out <> nt_feed(t, FNo.step(st, i))

# The scenario (R6): the model's events run on the rule as eukhe runs them
# --------

# the session of a scenario
def nt_sid() -> String:
  "s"

# the stamp of the stored notice at position i: i chars (distinct
# positions, distinct stamps)
def nt_stamp(i: Nat) -> String:
  match i:
    case 0n:
      SNil{}
    case 1n+p:
      SCon{'1', nt_stamp(p)}

# the stored notice at position i
def nt_note(i: Nat) -> No.Msg:
  No.Custom{nt_kind(), nt_stamp(i)}

# c, plus one when b
def nt_bump(b: Bool, c: Nat) -> Nat:
  match b:
    case True{}:
      1n+c
    case False{}:
      c

# the newest notice, at position i, arrives live: when it shows, the view
# records it
def nt_live.last(b: Bool, rs: List<&2, No.Seen>, c: Nat, +i: Nat) -> List<&2, No.Seen> & List<&2, Nat>:
  match b:
    case True{}:
      (No.record(rs, nt_sid(), [nt_note(i)]), [1n+c])
    case False{}:
      (rs, [c])

def nt_live.cons(c: Nat, r: List<&2, No.Seen> & List<&2, Nat>) -> List<&2, No.Seen> & List<&2, Nat>:
  (rs, cs) = r
  (rs, c <> cs)

# the counts c <> t from position i on, the last one the newest
def nt_live.at(t: List<&2, Nat>, c: Nat, +i: Nat, +rs: List<&2, No.Seen>) -> List<&2, No.Seen> & List<&2, Nat>:
  match t:
    case Nil{}:
      nt_live.last(No.visible(rs, nt_sid(), nt_note(i)), rs, c, i)
    case d <> u:
      nt_live.cons(c, nt_live.at(u, d, 1n+i, rs))

def nt_live(cs: List<&2, Nat>, rs: List<&2, No.Seen>) -> List<&2, No.Seen> & List<&2, Nat>:
  match cs:
    case Nil{}:
      (rs, Nil{})
    case c <> t:
      nt_live.at(t, c, 0n, rs)

# x <> xs when b, else xs
def nt_keep.if(b: Bool, x: No.Msg, xs: List<&2, No.Msg>) -> List<&2, No.Msg>:
  match b:
    case True{}:
      x <> xs
    case False{}:
      xs

def nt_scan.cons(vo: Bool, +vn: Bool, +i: Nat, c: Nat, r: List<&2, No.Msg> & List<&2, Nat>) -> List<&2, No.Msg> & List<&2, Nat>:
  (ks, cs) = r
  (nt_keep.if(vo, No.Other{}, nt_keep.if(vn, nt_note(i), ks)), nt_bump(vn, c) <> cs)

# an attach: the stored transcript from position i on (each notice after
# a message of another role) filtered by the record rs, and each count
# plus one when its notice shows
def nt_scan(cs: List<&2, Nat>, +i: Nat, +rs: List<&2, No.Seen>) -> List<&2, No.Msg> & List<&2, Nat>:
  match cs:
    case Nil{}:
      (Nil{}, Nil{})
    case c <> t:
      nt_scan.cons(No.visible(rs, nt_sid(), No.Other{}), No.visible(rs, nt_sid(), nt_note(i)), i, c, nt_scan(t, 1n+i, rs))

# ... then the view records what it showed
def nt_attach(+rs: List<&2, No.Seen>, r: List<&2, No.Msg> & List<&2, Nat>) -> List<&2, No.Seen> & List<&2, Nat>:
  (ks, cs) = r
  (No.record(rs, nt_sid(), ks), cs)

# an attach from the record rs and the counts cs
def nt_reattach(+rs: List<&2, No.Seen>, cs: List<&2, Nat>) -> List<&2, No.Seen> & List<&2, Nat>:
  nt_attach(rs, nt_scan(cs, 0n, rs))

def nt_step(e: No.Ev, r: List<&2, No.Seen> & List<&2, Nat>) -> List<&2, No.Seen> & List<&2, Nat>:
  match e:
    case No.Restore{}:
      (rs, cs) = r
      (rs, List.append(&2, Nat, cs, [0n]))
    case No.Live{}:
      (rs, cs) = r
      nt_live(cs, rs)
    case No.Reconnect{}:
      (rs, cs) = r
      nt_reattach(rs, cs)

def nt_go(evs: List<&2, No.Ev>, r: List<&2, No.Seen> & List<&2, Nat>) -> List<&2, No.Seen> & List<&2, Nat>:
  match evs:
    case Nil{}:
      r
    case e <> rest:
      nt_go(rest, nt_step(e, r))

# the record and, for each stored notice, how many times it showed, after
# the events evs from a view that showed nothing
def nt_scene(evs: List<&2, No.Ev>) -> List<&2, No.Seen> & List<&2, Nat>:
  nt_go(evs, (Nil{}, Nil{}))

def nt_counts(r: List<&2, No.Seen> & List<&2, Nat>) -> List<&2, Nat>:
  (rs, cs) = r
  cs

# how many times each notice of the model showed
def nt_shown(ns: List<&2, No.N>) -> List<&2, Nat>:
  match ns:
    case Nil{}:
      Nil{}
    case n <> t:
      match n:
        case No.N{s, c}:
          c <> nt_shown(t)

# every count is at most one
def nt_once(cs: List<&2, Nat>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case c <> t:
      Bool.and(Nat.is_le(c, 1n), nt_once(t))

def nt_sum(cs: List<&2, Nat>) -> Nat:
  match cs:
    case Nil{}:
      0n
    case c <> t:
      Nat.add(c, nt_sum(t))

# the restores among the events
def nt_restores(evs: List<&2, No.Ev>) -> Nat:
  match evs:
    case Nil{}:
      0n
    case e <> rest:
      match e:
        case No.Restore{}:
          1n+nt_restores(rest)
        case No.Live{}:
          nt_restores(rest)
        case No.Reconnect{}:
          nt_restores(rest)

# Laws: the rule
# --------------

# LAW notice_rule_history (R1, R2, R3, R4, R5): after any asks, a message of a session shows
# exactly when it is no restore notice or no record of that session among
# the asks holds its stamp
# EXCLUDES: a notice hidden that was never recorded, or recorded under
#   another session or stamp; a recorded notice shown again; another
#   message hidden; an ask that changes the record; a record forgotten
law notice_rule_history:
  for +qs: List<&2, No.Ask>
  for +sid: String
  for +m: No.Msg
  {No.visible(nt_book(qs), sid, m) == nt_shows(qs, sid, m) : Bool}

# LAW notice_real_shown_once (R1): once the view records a restore notice of a session, it
# never shows that notice for that session again
# EXCLUDES: a recorded notice shown again (a rebuilt transcript
#   accumulating restore rows)
law notice_real_shown_once:
  for +rs: List<&2, No.Seen>
  for +sid: String
  for +s: String
  for +ms: List<&2, No.Msg>
  for h: {nt_has(ms, s) == True{} : Bool}
  {No.visible(No.record(rs, sid, ms), sid, No.Custom{"ipython_state_restored", s}) == False{} : Bool}

# LAW notice_real_record_keeps (R1): a record never shows again a message that did not show
# EXCLUDES: a record that forgets earlier notices
law notice_real_record_keeps:
  for +rs: List<&2, No.Seen>
  for +sid: String
  for +q: String
  for +ms: List<&2, No.Msg>
  for +m: No.Msg
  for h: {No.visible(rs, q, m) == False{} : Bool}
  {No.visible(No.record(rs, sid, ms), q, m) == False{} : Bool}

# LAW notice_real_apart (R4): what the view records for one session changes nothing for another
# EXCLUDES: a notice of one session hiding the notice of the same stamp in
#   another session (one record for every session)
law notice_real_apart:
  for +rs: List<&2, No.Seen>
  for +sid: String
  for +q: String
  for +ms: List<&2, No.Msg>
  for +m: No.Msg
  for h: {nt_eq(sid, q) == False{} : Bool}
  {No.visible(No.record(rs, sid, ms), q, m) == No.visible(rs, q, m) : Bool}

# LAW notice_real_other_shows (R3): a message of another role always shows
# EXCLUDES: user, assistant or tool messages hidden by the record
law notice_real_other_shows:
  for +rs: List<&2, No.Seen>
  for +sid: String
  {No.visible(rs, sid, No.Other{}) == True{} : Bool}

# LAW notice_real_custom_shows (R3): a custom message of another kind always shows
# EXCLUDES: custom messages of other kinds hidden because their stamp was
#   recorded
law notice_real_custom_shows:
  for +rs: List<&2, No.Seen>
  for +sid: String
  for +k: String
  for +s: String
  for h: {nt_eq(k, nt_kind()) == False{} : Bool}
  {No.visible(rs, sid, No.Custom{k, s}) == True{} : Bool}

# LAW notice_real_refines (R6): the model's events run on the rule as eukhe runs them (a
# restore stores a notice after a message of another role; a live notice
# shows the newest notice when it shows and records it; an attach shows
# the stored messages that show, then records them) show each notice as
# many times as the model of the scenario (No.run) shows it
# EXCLUDES: a rule whose attach, live event or record differs from the
#   model the laws notice_shown_once and notice_per_restore pin
law notice_real_refines:
  for +evs: List<&2, No.Ev>
  {nt_counts(nt_scene(evs)) == nt_shown(No.run(evs)) : List<&2, Nat>}

# LAW notice_real_once (R6): run on the rule, each stored notice shows at most once
# EXCLUDES: an attach that shows a restore notice again
law notice_real_once:
  for +evs: List<&2, No.Ev>
  {nt_once(nt_counts(nt_scene(evs))) == True{} : Bool}

# LAW notice_real_per_restore (R6): run on the rule, after one more attach the restore rows
# shown equal the restores
# EXCLUDES: notices accumulating or lost across attaches
law notice_real_per_restore:
  for +evs: List<&2, No.Ev>
  {nt_sum(nt_counts(nt_scene(List.append(&2, No.Ev, evs, [No.Reconnect{}])))) == nt_restores(evs) : Nat}

# LAW notice_once_exact (R6): the model's `once` holds exactly when every stored notice showed
# at most once
# EXCLUDES: a constant or input-ignoring No.once (notice_shown_once would
#   then say nothing about the model)
law notice_once_exact:
  for +ns: List<&2, No.N>
  {No.once(ns) == nt_once(nt_shown(ns)) : Bool}

# Laws: the entry
# ---------------

# LAW notice_ffi_open (R7): the open with no input is the empty record, and replies nothing
# EXCLUDES: a record that starts with notices hidden
law notice_ffi_open:
  {FNo.open("") == (FNo.Live{Nil{}}, "") : FNo.St & String}

# LAW notice_ffi_open_refused (R7): an open with input is refused, with the error form
# EXCLUDES: a default record for an open Rust never sends
law notice_ffi_open_refused:
  for +s: String
  for h: {String.is_empty(s) == False{} : Bool}
  {FNo.open(s) == (FNo.Shut{}, Wr.err("notice: the open takes no input")) : FNo.St & String}

# LAW notice_ffi_shut (R7): a refused open answers every step with the error form
# EXCLUDES: a refused stepper that answers a decision
law notice_ffi_shut:
  for +s: String
  {FNo.step(FNo.Shut{}, s) == (FNo.Shut{}, Wr.err("notice: the open was refused")) : FNo.St & String}

# LAW notice_ffi_step (R7): an ask Rust spells answers the rule's answer, spelled, and the
# record moves as the rule moves it
# EXCLUDES: a field misread (session, kind, stamp, the messages of a
#   record), a decision other than the rule's, a reply in another
#   spelling, a record kept that the rule changed or changed that it kept
law notice_ffi_step:
  for +rs: List<&2, No.Seen>
  for +q: No.Ask
  for h: {nt_ask_fits(q) == True{} : Bool}
  {FNo.step(FNo.Live{rs}, nt_spell_ask(q, "")) == nt_spell_step(No.answer(rs, q)) : FNo.St & String}

# LAW notice_ffi_history (R1-R7): the shipped stepper, opened with no input and fed any asks
# Rust spells, replies to each what the history spec answers
# EXCLUDES: any reply of the shipped entry that differs from the spec
law notice_ffi_history:
  for +qs: List<&2, No.Ask>
  for h: {nt_asks_fit(qs) == True{} : Bool}
  {nt_run(qs, FNo.open("")) == "" <> nt_replies(qs, Nil{}) : List<&2, String>}

# LAW notice_ffi_exact (R7): a step that does not answer the error form read an ask Rust
# spells, whole
# EXCLUDES: a decoder that accepts input Rust never writes (a guessed
#   field, an unknown tag, trailing input)
law notice_ffi_exact:
  for +rs: List<&2, No.Seen>
  for +s: String
  for h: {LawsBase.wire_opens_err(nt_out(FNo.step(FNo.Live{rs}, s))) == False{} : Bool}
  exs q: No.Ask
  {nt_ask_fits(q) == True{} : Bool} & {s == nt_spell_ask(q, "") : String}

# LAW notice_ffi_malformed (R7): a step that answers the error form keeps the record and
# answers exactly the malformed-ask error
# EXCLUDES: a record changed or lost by a malformed ask, another error text
law notice_ffi_malformed:
  for +rs: List<&2, No.Seen>
  for +s: String
  for h: {LawsBase.wire_opens_err(nt_out(FNo.step(FNo.Live{rs}, s))) == True{} : Bool}
  {FNo.step(FNo.Live{rs}, s) == (FNo.Live{rs}, Wr.err("notice: malformed ask")) : FNo.St & String}

# LAW notice_ffi_fits_witness: witness: asks that fit the wire exist
# EXCLUDES: a vacuous nt_ask_fits
law notice_ffi_fits_witness:
  exs q: No.Ask
  {nt_ask_fits(q) == True{} : Bool}

# LAW notice_ffi_spell_example (R7): anchor: the asks of eukhe-tui restore_notices.rs, spelled
# EXCLUDES: a speller other than the one Rust writes (field order, tags,
#   lengths in chars)
law notice_ffi_spell_example:
  {[nt_spell_ask(No.Shows{"session-1", No.Custom{"ipython_state_restored", "1700000000001"}}, ""), nt_spell_ask(No.Shows{"session-1", No.Other{}}, ""), nt_spell_ask(No.Notes{"session-1", [No.Other{}, No.Custom{"ipython_state_restored", "1700000000001"}]}, "")] == ["0,9,session-11,22,ipython_state_restored13,1700000000001", "0,9,session-10,", "1,9,session-12,0,1,22,ipython_state_restored13,1700000000001"] : List<&2, String>}

# LAW notice_ffi_wire_example (R1-R7): anchor: the bytes eukhe sends and the replies: a
# notice shows, another message shows, the record, the notice hidden, the
# other session, another stamp, another kind, an unknown tag, trailing
# input, an empty record
# EXCLUDES: an entry that answers other bytes than the grammar's
law notice_ffi_wire_example:
  {nt_feed(["0,9,session-11,22,ipython_state_restored13,1700000000001", "0,9,session-10,", "1,9,session-12,0,1,22,ipython_state_restored13,1700000000001", "0,9,session-11,22,ipython_state_restored13,1700000000001", "0,9,session-21,22,ipython_state_restored13,1700000000001", "0,9,session-11,22,ipython_state_restored13,1700000000002", "0,9,session-11,5,other13,1700000000001", "2,", "0,9,session-10,x", "1,9,session-10,"], FNo.open("")) == ["", "T", "T", "", "F", "T", "T", "T", Wr.err("notice: malformed ask"), Wr.err("notice: malformed ask"), ""] : List<&2, String>}

# LAW notice_ffi_malformed_witness: witness: a step that answers the error form exists
# EXCLUDES: a vacuous notice_ffi_malformed
law notice_ffi_malformed_witness:
  exs s: String
  {LawsBase.wire_opens_err(nt_out(FNo.step(FNo.Live{Nil{}}, s))) == True{} : Bool}
