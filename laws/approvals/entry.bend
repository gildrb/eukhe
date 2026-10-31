# eukhe: the laws of area approvals, section entry: the entry of the
# compiled core for the approval gate (bend/ffi_approvals.bend): the call
# (the default auto set) and the stepper of one session's desk

import Base
import ../../bend/approvals.bend as Am
import ../../bend/ffi_approvals.bend as FAm
import ../../bend/wire.bend as Wr
import ../base.bend as LawsBase

# LAWS (G5, compiled core): the approval gate runs as the compiled model
# (bend/ffi_approvals.bend over bend/approvals.bend; Rust: crates/
# eukhe-bend/src/rules/approvals.rs, driven by crates/eukhe-daemon/src/
# shell_approval.rs). Each law is an open claim about the functions the
# core runs (FAm.ffi, FAm.open, FAm.step), stated with spec spellers and a
# reader built only from the wire primitives of bend/wire.bend:
#
# R1: the call with no input answers the default auto set
#     (`Am.default_auto`); any other input answers exactly the error form
#     "approvals: malformed request".
# R2: the desk opens empty (the first key next) on no input; an open with
#     input opens the refused state, which answers every step "approvals:
#     the open was refused".
# R3: a live desk answers every input that is exactly one event (the
#     grammar of bend/ffi_approvals.bend, restated by `read_ev`) with the
#     model desk's step (`Am.dstep`, laws/approvals/desk.bend), spelled: an
#     ask's key, then the acts; any other input answers exactly the error
#     form "approvals: malformed event" and keeps the desk.
# Every input is free: any request ids, effects, sessions, answers,
# detaches, keys, fates, any text, from any desk.

# Spec spellers
# -------------

def spell_ns(xs: List<&2, Nat>, rest: String) -> String:
  Wr.put_list(~Nat, ~Wr.put_nat, xs, rest)

def spell_here(h: Am.Here) -> Nat:
  match h:
    case Am.Nobody{}:
      0n
    case Am.GatewayOnly{}:
      1n
    case Am.Clients{}:
      2n

# a list of Nats fits the wire: its length and each item
def ns_fit(+xs: List<&2, Nat>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs))

# a fate: runs 0, denied 1, unanswered 2, refused by the gateway rule 3
def spell_fate(f: Am.Fate, rest: String) -> String:
  match f:
    case Am.Runs{}:
      Wr.put_nat(0n, rest)
    case Am.Denied{}:
      Wr.put_nat(1n, rest)
    case Am.Unheard{}:
      Wr.put_nat(2n, rest)
    case Am.GatewayRefused{}:
      Wr.put_nat(3n, rest)

# the error form of a call with input
def malformed() -> String:
  SCon{'E', SCon{' ', "approvals: malformed request"}}

# the error form of an input that is not exactly one event
def malformed_event() -> String:
  SCon{'E', SCon{' ', "approvals: malformed event"}}

# an event as Rust writes it, then rest
def spell_ev(e: Am.Ev, rest: String) -> String:
  match e:
    case Am.EAsk{id, es, h, p}:
      Wr.put_nat(0n, Wr.put_str(id, spell_ns(es, Wr.put_nat(spell_here(h), Wr.put_bool(p, rest)))))
    case Am.EAnswer{id, y}:
      Wr.put_nat(1n, Wr.put_str(id, Wr.put_bool(y, rest)))
    case Am.EDetach{h, p}:
      Wr.put_nat(2n, Wr.put_nat(spell_here(h), Wr.put_bool(p, rest)))
    case Am.ECancel{k}:
      Wr.put_nat(3n, Wr.put_nat(k, rest))
    case Am.EBack{k, f}:
      Wr.put_nat(4n, Wr.put_nat(k, spell_fate(f, rest)))

# every length and number of the event fits the wire
def ev_fits(e: Am.Ev) -> Bool:
  match e:
    case Am.EAsk{id, es, h, p}:
      Bool.and(LawsBase.wire_fits(String.length(id)), ns_fit(es))
    case Am.EAnswer{id, y}:
      LawsBase.wire_fits(String.length(id))
    case Am.EDetach{h, p}:
      True{}
    case Am.ECancel{k}:
      LawsBase.wire_fits(k)
    case Am.EBack{k, f}:
      LawsBase.wire_fits(k)

def evs_fit(es: List<&2, Am.Ev>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case e <> t:
      Bool.and(ev_fits(e), evs_fit(t))

def spell_act(a: Am.Act, rest: String) -> String:
  match a:
    case Am.AShow{k}:
      Wr.put_nat(0n, Wr.put_nat(k, rest))
    case Am.ASettle{k}:
      Wr.put_nat(1n, Wr.put_nat(k, rest))
    case Am.ARelay{k}:
      Wr.put_nat(2n, Wr.put_nat(k, rest))
    case Am.AWake{k, f}:
      Wr.put_nat(3n, Wr.put_nat(k, spell_fate(f, rest)))
    case Am.ATook{}:
      Wr.put_nat(4n, rest)
    case Am.AGone{}:
      Wr.put_nat(5n, rest)

def spell_acts.items(as: List<&2, Am.Act>) -> String:
  match as:
    case Nil{}:
      ""
    case a <> t:
      spell_act(a, spell_acts.items(t))

# the acts: their count, then each
def spell_acts(+as: List<&2, Am.Act>) -> String:
  Wr.put_nat(List.length(&2, Am.Act, as), spell_acts.items(as))

# the reply to e: an ask's leads with its key n
def spell_reply(e: Am.Ev, +n: Nat, +as: List<&2, Am.Act>) -> String:
  match e:
    case Am.EAsk{id, es, h, p}:
      Wr.put_nat(n, spell_acts(as))
    case Am.EAnswer{id, y}:
      spell_acts(as)
    case Am.EDetach{h, p}:
      spell_acts(as)
    case Am.ECancel{k}:
      spell_acts(as)
    case Am.EBack{k, f}:
      spell_acts(as)

def dk_next(d: Am.D) -> Nat:
  match d:
    case Am.D{n, qs}:
      n

# the entry's state and reply after the model desk's step r on e from a
# desk whose next key is n
def dk_reply(e: Am.Ev, +n: Nat, r: Am.D & List<&2, Am.Act>) -> FAm.St & String:
  (d2, as) = r
  (FAm.Live{d2}, spell_reply(e, n, as))

# Reader: the events, read with the wire primitives
# -------------------------------------------------

def read_here(r: Wr.Dec<Nat>) -> Wr.Dec<Am.Here>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{Am.Nobody{}, s}
        case 1n:
          Wr.Got{Am.GatewayOnly{}, s}
        case 2n:
          Wr.Got{Am.Clients{}, s}
        case 3n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def read_fate(r: Wr.Dec<Nat>) -> Wr.Dec<Am.Fate>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{Am.Runs{}, s}
        case 1n:
          Wr.Got{Am.Denied{}, s}
        case 2n:
          Wr.Got{Am.Unheard{}, s}
        case 3n:
          Wr.Got{Am.GatewayRefused{}, s}
        case 4n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.parent(id: String, es: List<&2, Nat>, h: Am.Here, r: Wr.Dec<Bool>) -> Wr.Dec<Am.Ev>:
  match r:
    case Wr.Got{p, s}:
      Wr.Got{Am.EAsk{id, es, h, p}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.here(id: String, es: List<&2, Nat>, r: Wr.Dec<Am.Here>) -> Wr.Dec<Am.Ev>:
  match r:
    case Wr.Got{h, s}:
      read_ask.parent(id, es, h, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.effs(id: String, r: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<Am.Ev>:
  match r:
    case Wr.Got{es, s}:
      read_ask.here(id, es, read_here(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.id(r: Wr.Dec<String>) -> Wr.Dec<Am.Ev>:
  match r:
    case Wr.Got{id, s}:
      read_ask.effs(id, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_answer.yes(id: String, r: Wr.Dec<Bool>) -> Wr.Dec<Am.Ev>:
  match r:
    case Wr.Got{y, s}:
      Wr.Got{Am.EAnswer{id, y}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_answer.id(r: Wr.Dec<String>) -> Wr.Dec<Am.Ev>:
  match r:
    case Wr.Got{id, s}:
      read_answer.yes(id, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_detach.parent(h: Am.Here, r: Wr.Dec<Bool>) -> Wr.Dec<Am.Ev>:
  match r:
    case Wr.Got{p, s}:
      Wr.Got{Am.EDetach{h, p}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_detach.here(r: Wr.Dec<Am.Here>) -> Wr.Dec<Am.Ev>:
  match r:
    case Wr.Got{h, s}:
      read_detach.parent(h, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_cancel.key(r: Wr.Dec<Nat>) -> Wr.Dec<Am.Ev>:
  match r:
    case Wr.Got{k, s}:
      Wr.Got{Am.ECancel{k}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_back.fate(k: Nat, r: Wr.Dec<Am.Fate>) -> Wr.Dec<Am.Ev>:
  match r:
    case Wr.Got{f, s}:
      Wr.Got{Am.EBack{k, f}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_back.key(r: Wr.Dec<Nat>) -> Wr.Dec<Am.Ev>:
  match r:
    case Wr.Got{k, s}:
      read_back.fate(k, read_fate(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read_ev.tag(t: Nat, s: String) -> Wr.Dec<Am.Ev>:
  match t:
    case 0n:
      read_ask.id(Wr.get_str(s))
    case 1n:
      read_answer.id(Wr.get_str(s))
    case 2n:
      read_detach.here(read_here(Wr.get_nat(s)))
    case 3n:
      read_cancel.key(Wr.get_nat(s))
    case 4n:
      read_back.key(Wr.get_nat(s))
    case 5n+u:
      Wr.Bad{}

def read_ev.go(r: Wr.Dec<Nat>) -> Wr.Dec<Am.Ev>:
  match r:
    case Wr.Got{t, s}:
      read_ev.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

# the event s starts with, and what follows it
def read_ev(s: String) -> Wr.Dec<Am.Ev>:
  read_ev.go(Wr.get_nat(s))

def dspec.end(whole: Bool, +d: Am.D, +e: Am.Ev) -> FAm.St & String:
  match whole:
    case True{}:
      dk_reply(e, dk_next(d), Am.dstep(d, e))
    case False{}:
      (FAm.Live{d}, malformed_event())

def dspec.run(+d: Am.D, r: Wr.Dec<Am.Ev>) -> FAm.St & String:
  match r:
    case Wr.Got{e, s}:
      dspec.end(Wr.end(s), d, e)
    case Wr.Bad{}:
      (FAm.Live{d}, malformed_event())

# the step of a live desk d on s: the model desk's step on the event s is
# exactly, spelled; else the error form, the desk kept
def dspec(+d: Am.D, s: String) -> FAm.St & String:
  dspec.run(d, read_ev(s))

# the reply of r, then the shipped stepper's replies to es spelled, from
# the state of r
def dk_feed(es: List<&2, Am.Ev>, r: FAm.St & String) -> List<&2, String>:
  match es:
    case Nil{}:
      (st, out) = r
      [out]
    case e <> t:
      (st, out) = r
      out <> dk_feed(t, FAm.step(st, spell_ev(e, "")))

# the replies of the shipped stepper to raw inputs, from the state of r
def dk_raw(ins: List<&2, String>, r: FAm.St & String) -> List<&2, String>:
  match ins:
    case Nil{}:
      (st, out) = r
      [out]
    case i <> t:
      (st, out) = r
      out <> dk_raw(t, FAm.step(st, i))

def dk_desk(r: Am.D & List<&2, Am.Act>) -> Am.D:
  (d, as) = r
  d

def dk_acts(r: Am.D & List<&2, Am.Act>) -> List<&2, Am.Act>:
  (d, as) = r
  as

# the model desk's replies to es from d, spelled
def dk_replies(es: List<&2, Am.Ev>, +d: Am.D) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> t:
      spell_reply(e, dk_next(d), dk_acts(Am.dstep(d, e))) <> dk_replies(t, dk_desk(Am.dstep(d, e)))

# The call
# --------

def spec.end(whole: Bool) -> String:
  match whole:
    case True{}:
      spell_ns(Am.default_auto(), "")
    case False{}:
      malformed()

# LAW approvals_ffi_exact: on every input the call answers the default auto set when the input is empty (nothing but the call), and exactly the error form "approvals: malformed request" on any other input
# EXCLUDES: another default auto set, a default for malformed input,
#   input ignored
law approvals_ffi_exact:
  for +s: String
  {FAm.ffi(s) == spec.end(Wr.end(s)) : String}

# LAW approvals_ffi_answers: the call Rust makes (no input) answers the default auto set
# EXCLUDES: the call Rust makes refused or answered otherwise
law approvals_ffi_answers:
  {FAm.ffi("") == spell_ns(Am.default_auto(), "") : String}

# LAW approvals_ffi_left_over: a call with input gets exactly the error form
# EXCLUDES: input read past or ignored
law approvals_ffi_left_over:
  for +more: String
  for some: {String.is_empty(more) == False{} : Bool}
  {FAm.ffi(more) == malformed() : String}

# LAW approvals_ffi_example (changed 2026-10-27 by the user: secrets never
# ask again; the default auto set holds every effect): anchor: the bytes
# of the call and its reply; a call with input is refused
# EXCLUDES: another spelling of the reply
law approvals_ffi_example:
  {FAm.ffi("") == "7,0,1,2,3,4,5,6," : String} & {FAm.ffi("2,") == malformed() : String}

# The desk
# --------

# LAW approvals_desk_entry_open (R2): the open with no input is an empty
# desk with the first key next, and replies nothing
# EXCLUDES: a desk that starts with questions or keys used
law approvals_desk_entry_open:
  {FAm.open("") == (FAm.Live{Am.D{0n, Nil{}}}, "") : FAm.St & String}

# LAW approvals_desk_entry_open_refused (R2): an open with input is
# refused with its error form
# EXCLUDES: a default desk for an open Rust never sends
law approvals_desk_entry_open_refused:
  for +s: String
  for h: {String.is_empty(s) == False{} : Bool}
  {FAm.open(s) == (FAm.Refused{}, SCon{'E', SCon{' ', "approvals: the open takes no input"}}) : FAm.St & String}

# LAW approvals_desk_entry_shut (R2): a refused open answers every step
# with its error form
# EXCLUDES: a refused desk that shows, relays or wakes
law approvals_desk_entry_shut:
  for +s: String
  {FAm.step(FAm.Refused{}, s) == (FAm.Refused{}, SCon{'E', SCon{' ', "approvals: the open was refused"}}) : FAm.St & String}

# LAW approvals_desk_entry_exact (R3): on every input, from every desk,
# the entry answers the model desk's step on the event the input is
# exactly (as the wire's reader reads it), spelled; on any other input
# exactly the error form "approvals: malformed event", the desk kept
# EXCLUDES: a field misread, a tag read as another, an act or a key in
#   another spelling, a desk changed by a malformed event, input left over
#   ignored, another error text
law approvals_desk_entry_exact:
  for +d: Am.D
  for +s: String
  {FAm.step(FAm.Live{d}, s) == dspec(d, s) : FAm.St & String}

# LAW approvals_desk_entry_reads (R3): the reader reads back every event
# Rust spells (every length and number within the wire), leaving the rest
# untouched
# EXCLUDES: a reader that refuses or misreads an event Rust sends, which
#   would make approvals_desk_entry_exact answer the error form for it
law approvals_desk_entry_reads:
  for +e: Am.Ev
  for +rest: String
  for h: {ev_fits(e) == True{} : Bool}
  {read_ev(spell_ev(e, rest)) == Wr.Got{e, rest} : Wr.Dec<Am.Ev>}

# LAW approvals_desk_entry_answers (R3): from every desk, every event Rust
# spells moves the desk as the model's step does and answers its spelled
# reply
# EXCLUDES: an event Rust sends refused or answered otherwise
law approvals_desk_entry_answers:
  for +d: Am.D
  for +e: Am.Ev
  for h: {ev_fits(e) == True{} : Bool}
  {FAm.step(FAm.Live{d}, spell_ev(e, "")) == dk_reply(e, dk_next(d), Am.dstep(d, e)) : FAm.St & String}

# LAW approvals_desk_entry_history (R2, R3): the shipped stepper, opened as
# Rust opens it and fed any events Rust spells, replies to each what the
# model desk decides after the events before it: every desk law holds for
# the desk Rust drives
# EXCLUDES: a stepper that forgets, reorders or replays an event
law approvals_desk_entry_history:
  for +es: List<&2, Am.Ev>
  for fits: {evs_fit(es) == True{} : Bool}
  {dk_feed(es, FAm.open("")) == "" <> dk_replies(es, Am.D{0n, Nil{}}) : List<&2, String>}

# LAW approvals_desk_entry_example (R3): anchor: the bytes Rust sends and
# the replies: a question shown (key 0), a relayed one (key 1), the
# answer of the first (settle, wake: runs, took), a second answer to it
# (gone), the parent's answer to the relay (wake: denied), a gateway-only
# protected-path write (wake at once: refused), a gateway-only secret read
# (wake at once: runs), an unknown tag, input left over
# EXCLUDES: another spelling of an event or a reply
law approvals_desk_entry_example:
  {dk_raw(["0,1,a1,1,2,F", "0,1,b1,1,0,T", "1,1,aT", "1,1,aT", "4,1,1,", "0,1,c1,5,1,F", "0,1,d1,6,1,F", "9,", "3,0,x"], FAm.open("")) == ["", "0,1,0,0,", "1,1,2,1,", "3,1,0,3,0,0,4,", "1,5,", "1,3,1,1,", "2,1,3,2,3,", "3,1,3,3,0,", malformed_event(), malformed_event()] : List<&2, String>}

# LAW approvals_desk_fits_example (R3): witness: events of each kind Rust
# sends fit the wire (the desk entry laws are not vacuous)
law approvals_desk_fits_example:
  {evs_fit([Am.EAsk{"call-1:0", [1n, 5n], Am.Clients{}, True{}}, Am.EAnswer{"call-1:0", True{}}, Am.EDetach{Am.Nobody{}, False{}}, Am.ECancel{3n}, Am.EBack{2n, Am.Unheard{}}]) == True{} : Bool}
