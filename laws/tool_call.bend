# eukhe: the laws of area tool_call

import Base
import ../bend/tool_call.bend as Tc
import ../bend/ffi_tool_call.bend as FTc
import ../bend/wire.bend as Wr

# (S2) A tool call journals its start and its settle
# --------------------------------------------------
# Call 1-3. The Harness opens the stepper
# bend/ffi_tool_call.bend where it journals a call's start (a first
# attempt) or clears it (a rerun), sends it every report the tool makes
# (output, a diagnostic, usage, details, a read of its output, a nested
# call) and the end of its execute, in the order they come from any
# thread, and does what each reply says: store a report, refuse it,
# journal the settle (as finished, failed, or cancelled: the abort handler
# settles), or nothing. It keeps the reports' content; it journals only
# what the replies say. Every law holds for every event order: the
# events are free, a report after the end and a second end included.

# Spellers: the bytes the Harness sends and reads, from the wire's
# primitives

# an event as the Harness writes it: 0 a report; 1, then threw and aborted
def tc_spell(e: Tc.Ev) -> String:
  match e:
    case Tc.Report{}:
      Wr.put_nat(0n, "")
    case Tc.End{t, a}:
      Wr.put_nat(1n, Wr.put_bool(t, Wr.put_bool(a, "")))

# an open as the Harness writes it: a first attempt or a rerun
def tc_spell_open(first: Bool) -> String:
  Wr.put_bool(first, "")

def tc_state(r: FTc.St & String) -> FTc.St:
  (s, x) = r
  s

def tc_reply(r: FTc.St & String) -> String:
  (s, x) = r
  x

# the stepper as opened for a first attempt or a rerun, spelled
def tc_opened(first: Bool) -> FTc.St:
  tc_state(FTc.open(tc_spell_open(first)))

# the replies of the stepper st to the events es, spelled, in order
def tc_replies(es: List<&2, Tc.Ev>, +st: FTc.St) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> rest:
      tc_reply(FTc.step(st, tc_spell(e))) <> tc_replies(rest, tc_state(FTc.step(st, tc_spell(e))))

# What S2 asks, written from the requirement

# the record an open journals: 0 the start (the slot goes running), 1 a
# rerun's clear
def tc_open_spec(first: Bool) -> String:
  match first:
    case True{}:
      "0,"
    case False{}:
      "1,"

# how an execute that threw or not, its signal aborted or not, settles:
# 0 finished (it returned), 1 failed (it threw), 2 cancelled (it threw on
# an abort: the abort handler settles)
def tc_how_spec(t: Bool, a: Bool) -> String:
  match t a:
    case False{} False{}:
      "0,"
    case False{} True{}:
      "0,"
    case True{} True{}:
      "2,"
    case True{} False{}:
      "1,"

# the reply S2 asks for each event, spelled; ended: an end came before.
# Before the end: a report is stored (0), the end settles (2, then how).
# After it: a report is refused (1), another end does nothing (3).
def tc_spec(es: List<&2, Tc.Ev>, ended: Bool) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      match e:
        case Tc.Report{}:
          match ended:
            case False{}:
              "0," <> tc_spec(rest, False{})
            case True{}:
              "1," <> tc_spec(rest, True{})
        case Tc.End{t, a}:
          match ended:
            case False{}:
              SCon{'2', SCon{',', tc_how_spec(t, a)}} <> tc_spec(rest, True{})
            case True{}:
              "3," <> tc_spec(rest, True{})

# a reply that journals the call's settle: tag 2
def tc_settles(r: String) -> Bool:
  match r:
    case SNil{}:
      False{}
    case SCon{c, t}:
      match t:
        case SNil{}:
          False{}
        case SCon{d, u}:
          Bool.and(Char.is_eq(c, '2'), Char.is_eq(d, ','))

def tc_journaled.pick(b: Bool, r: String, rest: List<&2, String>) -> List<&2, String>:
  match b:
    case True{}:
      r <> rest
    case False{}:
      rest

# the replies among rs that journal a settle
def tc_journaled(rs: List<&2, String>) -> List<&2, String>:
  match rs:
    case Nil{}:
      Nil{}
    case +r <> rest:
      tc_journaled.pick(tc_settles(r), r, tc_journaled(rest))

# the call's journal: the open's record, then each settle its replies ask
def tc_journal(+first: Bool, es: List<&2, Tc.Ev>) -> List<&2, String>:
  tc_reply(FTc.open(tc_spell_open(first))) <> tc_journaled(tc_replies(es, tc_opened(first)))

# es holds an end of the execute
def tc_ends(es: List<&2, Tc.Ev>) -> Bool:
  match es:
    case Nil{}:
      False{}
    case e <> rest:
      match e:
        case Tc.Report{}:
          tc_ends(rest)
        case Tc.End{t, a}:
          True{}

def tc_once(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# for each report of es, in order: whether its reply stores it (rs: the
# replies, one per event)
def tc_kept(es: List<&2, Tc.Ev>, rs: List<&2, String>) -> List<&2, Bool>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      match e:
        case Tc.Report{}:
          match rs:
            case Nil{}:
              Nil{}
            case r <> more:
              String.eq(r, "0,") <> tc_kept(rest, more)
        case Tc.End{t, a}:
          match rs:
            case Nil{}:
              Nil{}
            case r <> more:
              tc_kept(rest, more)

# for each report of es, in order: whether it came before the end
# (ended: an end came before es)
def tc_before_end(es: List<&2, Tc.Ev>, +ended: Bool) -> List<&2, Bool>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      match e:
        case Tc.Report{}:
          Bool.not(ended) <> tc_before_end(rest, ended)
        case Tc.End{t, a}:
          tc_before_end(rest, True{})

# LAW tool_call_step_is_model: the stepper opened for a first attempt or
# a rerun and sent any events, in any order, answers each as S2 asks:
# before the execute's end every report is stored and the end settles the
# call, finished when it returned, failed when it threw, cancelled when it
# threw on an abort; after the end every report is refused and another
# end does nothing
# EXCLUDES: a report lost or refused while the call runs, a report stored
# after the settle, a second settle, a settle before the end, a settle as
# another ending (an abort settled as a failure, a throw as finished), a
# stepper whose state drifts after some order of events
law tool_call_step_is_model:
  for +first: Bool
  for +es: List<&2, Tc.Ev>
  {tc_replies(es, tc_opened(first)) == tc_spec(es, False{}) : List<&2, String>}

# LAW tool_call_open_exact: an open journals the start of a first attempt
# and the clear of a rerun
# EXCLUDES: a rerun that journals a second start, a first attempt that
# journals no start
law tool_call_open_exact:
  for +first: Bool
  {tc_reply(FTc.open(tc_spell_open(first))) == tc_open_spec(first) : String}

# LAW stream_journals_two: a tool call journals at most two records: its
# start (or a rerun's clear) and one settle; no report is journaled, in
# any order of events
# EXCLUDES: a progress record (a report journaled), a second settle
law stream_journals_two:
  for +first: Bool
  for +es: List<&2, Tc.Ev>
  {Nat.is_le(List.length(&2, String, tc_journal(first, es)), 2n) == True{} : Bool}

# LAW stream_settles_once: a tool call settles exactly once when its
# execute ends (a result, a throw or a cancel), and not before, whatever
# comes after
# EXCLUDES: a call that never settles, settles before its end, or settles
# twice (a late end, a report after the end)
law stream_settles_once:
  for +first: Bool
  for +es: List<&2, Tc.Ev>
  {List.length(&2, String, tc_journaled(tc_replies(es, tc_opened(first)))) == tc_once(tc_ends(es)) : Nat}

# LAW stream_settle_carries_all: the stepper stores exactly the reports
# that came before the execute's end: every one of them (so the settle,
# which reads what was stored after the end, carries every result byte,
# every warning, all usage), and none after it
# EXCLUDES: a report lost before the settle, a report stored after it (a
# settle that misses part of what the call stored, or a store into a
# settled call)
law stream_settle_carries_all:
  for +first: Bool
  for +es: List<&2, Tc.Ev>
  {tc_kept(es, tc_replies(es, tc_opened(first))) == tc_before_end(es, False{}) : List<&2, Bool>}

# The entry: the laws' reader, from the wire's primitives

def tc_read.aborted(t: Bool, r: Wr.Dec<Bool>) -> Wr.Dec<Tc.Ev>:
  match r:
    case Wr.Got{a, s}:
      Wr.Got{Tc.End{t, a}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def tc_read.threw(r: Wr.Dec<Bool>) -> Wr.Dec<Tc.Ev>:
  match r:
    case Wr.Got{t, s}:
      tc_read.aborted(t, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def tc_read.tag(n: Nat, s: String) -> Wr.Dec<Tc.Ev>:
  match n:
    case 0n:
      Wr.Got{Tc.Report{}, s}
    case 1n:
      tc_read.threw(Wr.get_bool(s))
    case 2n+p:
      Wr.Bad{}

def tc_read.go(r: Wr.Dec<Nat>) -> Wr.Dec<Tc.Ev>:
  match r:
    case Wr.Got{n, s}:
      tc_read.tag(n, s)
    case Wr.Bad{}:
      Wr.Bad{}

def tc_read.end(whole: Bool, e: Tc.Ev) -> Maybe<&2, Tc.Ev>:
  match whole:
    case True{}:
      Some{e}
    case False{}:
      None{}

def tc_read.whole(d: Wr.Dec<Tc.Ev>) -> Maybe<&2, Tc.Ev>:
  match d:
    case Wr.Got{e, s}:
      tc_read.end(Wr.end(s), e)
    case Wr.Bad{}:
      None{}

# the event s is, when s is exactly one event
def tc_read(s: String) -> Maybe<&2, Tc.Ev>:
  tc_read.whole(tc_read.go(Wr.get_nat(s)))

def tc_read_open.end(whole: Bool, b: Bool) -> Maybe<&2, Bool>:
  match whole:
    case True{}:
      Some{b}
    case False{}:
      None{}

def tc_read_open.whole(d: Wr.Dec<Bool>) -> Maybe<&2, Bool>:
  match d:
    case Wr.Got{b, s}:
      tc_read_open.end(Wr.end(s), b)
    case Wr.Bad{}:
      None{}

# the open s is, when s is exactly one Bool
def tc_read_open(s: String) -> Maybe<&2, Bool>:
  tc_read_open.whole(Wr.get_bool(s))

# LAW tool_call_entry_reads: in every state, an input the laws' reader
# reads as exactly one event is answered as that event spelled
# EXCLUDES: an input read otherwise by the entry than by the wire's grammar
law tool_call_entry_reads:
  for +c: Tc.C
  for +i: String
  for +e: Tc.Ev
  for got: {tc_read(i) == Some{e} : Maybe<&2, Tc.Ev>}
  {FTc.step(FTc.Call{c}, i) == FTc.step(FTc.Call{c}, tc_spell(e)) : FTc.St & String}

# LAW tool_call_entry_malformed_exact: in every state, an input the laws'
# reader does not read as exactly one event (a bad tag, a short or bad
# Bool, input left over) keeps the call and answers exactly the error form
# 'E ' + "tool_call: malformed event"
# EXCLUDES: a guessed event (a garbage end that settles the call, a
# garbage report stored), a call moved by garbage, another error text
law tool_call_entry_malformed_exact:
  for +c: Tc.C
  for +i: String
  for no: {tc_read(i) == None{} : Maybe<&2, Tc.Ev>}
  {FTc.step(FTc.Call{c}, i) == (FTc.Call{c}, SCon{'E', SCon{' ', "tool_call: malformed event"}}) : FTc.St & String}

# LAW tool_call_entry_open_reads: an open input the laws' reader reads as
# exactly one Bool opens as that Bool spelled
# EXCLUDES: an open read otherwise by the entry than by the wire's grammar
law tool_call_entry_open_reads:
  for +i: String
  for +b: Bool
  for got: {tc_read_open(i) == Some{b} : Maybe<&2, Bool>}
  {FTc.open(i) == FTc.open(tc_spell_open(b)) : FTc.St & String}

# LAW tool_call_entry_open_malformed_exact: an open input the laws' reader
# does not read as exactly one Bool opens the refused state and answers
# exactly the error form 'E ' + "tool_call: malformed open"
# EXCLUDES: a default attempt (a start journaled for garbage)
law tool_call_entry_open_malformed_exact:
  for +i: String
  for no: {tc_read_open(i) == None{} : Maybe<&2, Bool>}
  {FTc.open(i) == (FTc.Refused{}, SCon{'E', SCon{' ', "tool_call: malformed open"}}) : FTc.St & String}

# LAW tool_call_entry_shut: a refused open answers every step with exactly
# the error form 'E ' + "tool_call: the open was refused"
# EXCLUDES: a refused stepper that stores a report or settles a call
law tool_call_entry_shut:
  for +i: String
  {FTc.step(FTc.Refused{}, i) == (FTc.Refused{}, SCon{'E', SCon{' ', "tool_call: the open was refused"}}) : FTc.St & String}

# LAW tool_call_entry_example: anchor: the bytes the Harness sends and the
# replies: opens of a first attempt, a rerun, garbage; on a first attempt
# a report, an end that returned, threw, threw on an abort, a bad tag, a
# short end, input left over; after an end, a report and an end
# EXCLUDES: an entry that answers other bytes than the grammar's
law tool_call_entry_example:
  {[tc_reply(FTc.open("T")), tc_reply(FTc.open("F")), tc_reply(FTc.open("x"))] == ["0,", "1,", SCon{'E', SCon{' ', "tool_call: malformed open"}}] : List<&2, String>} & {[tc_reply(FTc.step(tc_opened(True{}), "0,")), tc_reply(FTc.step(tc_opened(True{}), "1,FF")), tc_reply(FTc.step(tc_opened(True{}), "1,TF")), tc_reply(FTc.step(tc_opened(True{}), "1,TT")), tc_reply(FTc.step(tc_opened(True{}), "2,")), tc_reply(FTc.step(tc_opened(True{}), "1,T")), tc_reply(FTc.step(tc_opened(True{}), "0,0,"))] == ["0,", "2,0,", "2,1,", "2,2,", SCon{'E', SCon{' ', "tool_call: malformed event"}}, SCon{'E', SCon{' ', "tool_call: malformed event"}}, SCon{'E', SCon{' ', "tool_call: malformed event"}}] : List<&2, String>} & {tc_replies([Tc.End{False{}, False{}}, Tc.Report{}, Tc.End{True{}, True{}}], tc_opened(False{})) == ["2,0,", "1,", "3,"] : List<&2, String>}
