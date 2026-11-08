# eukhe: the laws of area tool_call

import Base
import ../bend/tool_call.bend as Tc
import ../bend/ffi_tool_call.bend as FTc
import ../bend/wire.bend as Wr
import ../spec/harness/effect.bend as Sp

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

# (S3) Speculation, then effect
# -----------------------------
# A tool's effects run only once the assistant entry that made the call is
# durable (omp2 PHILOSOPHY: speculation, then effect). The Harness
# appends the assistant entry and creates each call's tool task in one
# commit (harness/generation/round.rs); the streamed reply before it is
# speculation, which runs nothing. Each handler of a tool task
# (harness/tool.rs: the call phase, the execute phase after a restart,
# abort) asks the gate, the call `ffi` of bend/ffi_tool_call.bend, and
# does what it answers. spec/harness/effect.bend restates the gate
# (E1-E4) and the world of one call (E5): the laws below run the shipped
# gate (Tc.gate, the one the entry spells) in every history of that
# world, any order of chunks, commits, runs, crashes, ends and aborts,
# with the tool resolved anew at each run. Not pinned here: what a run
# does (the journal, S2), which calls a round admits (round.rs refuses a
# truncated reply's calls and calls to tools not offered before it
# creates their tasks).

# Spellers: the bytes the Harness sends and reads, from the wire's
# primitives

def tc_spell_replay(p: Tc.Replay, rest: String) -> String:
  match p:
    case Tc.Safe{}:
      Wr.put_nat(0n, rest)
    case Tc.Unsafe{}:
      Wr.put_nat(1n, rest)

def tc_spell_now(t: Tc.Now, rest: String) -> String:
  match t:
    case Tc.Gone{}:
      Wr.put_nat(0n, rest)
    case Tc.Offered{p}:
      Wr.put_nat(1n, tc_spell_replay(p, rest))

# a gate question as the Harness writes it
def tc_spell_gate(q: Tc.Gate) -> String:
  match q:
    case Tc.Enter{f, t}:
      Wr.put_nat(0n, Wr.put_bool(f, tc_spell_now(t, "")))
    case Tc.Recover{f, p, t}:
      Wr.put_nat(1n, Wr.put_bool(f, tc_spell_replay(p, tc_spell_now(t, ""))))
    case Tc.Stop{f, x, i}:
      Wr.put_nat(2n, Wr.put_bool(f, Wr.put_bool(x, Wr.put_bool(i, ""))))

# an answer as the Harness reads it: 0 run, 1 missing, 2 unavailable,
# 3 rerun, 4 interrupted, 5 aborted, 6 abandoned
def tc_spell_go(g: Tc.Go) -> String:
  match g:
    case Tc.Run{}:
      "0,"
    case Tc.Missing{}:
      "1,"
    case Tc.Unavailable{}:
      "2,"
    case Tc.Rerun{}:
      "3,"
    case Tc.Interrupted{}:
      "4,"
    case Tc.Aborted{}:
      "5,"
    case Tc.Abandoned{}:
      "6,"

# The laws' reader of a gate question, from the wire's primitives

def tc_rg_replay.tag(n: Nat, s: String) -> Wr.Dec<Tc.Replay>:
  match n:
    case 0n:
      Wr.Got{Tc.Safe{}, s}
    case 1n:
      Wr.Got{Tc.Unsafe{}, s}
    case 2n+p:
      Wr.Bad{}

def tc_rg_replay.go(r: Wr.Dec<Nat>) -> Wr.Dec<Tc.Replay>:
  match r:
    case Wr.Got{n, s}:
      tc_rg_replay.tag(n, s)
    case Wr.Bad{}:
      Wr.Bad{}

def tc_rg_replay(s: String) -> Wr.Dec<Tc.Replay>:
  tc_rg_replay.go(Wr.get_nat(s))

def tc_rg_now.offered(r: Wr.Dec<Tc.Replay>) -> Wr.Dec<Tc.Now>:
  match r:
    case Wr.Got{p, s}:
      Wr.Got{Tc.Offered{p}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def tc_rg_now.tag(n: Nat, s: String) -> Wr.Dec<Tc.Now>:
  match n:
    case 0n:
      Wr.Got{Tc.Gone{}, s}
    case 1n:
      tc_rg_now.offered(tc_rg_replay(s))
    case 2n+p:
      Wr.Bad{}

def tc_rg_now.go(r: Wr.Dec<Nat>) -> Wr.Dec<Tc.Now>:
  match r:
    case Wr.Got{n, s}:
      tc_rg_now.tag(n, s)
    case Wr.Bad{}:
      Wr.Bad{}

def tc_rg_now(s: String) -> Wr.Dec<Tc.Now>:
  tc_rg_now.go(Wr.get_nat(s))

def tc_rg.enter(f: Bool, r: Wr.Dec<Tc.Now>) -> Wr.Dec<Tc.Gate>:
  match r:
    case Wr.Got{t, s}:
      Wr.Got{Tc.Enter{f, t}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def tc_rg.recover(f: Bool, p: Tc.Replay, r: Wr.Dec<Tc.Now>) -> Wr.Dec<Tc.Gate>:
  match r:
    case Wr.Got{t, s}:
      Wr.Got{Tc.Recover{f, p, t}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def tc_rg.stored(f: Bool, r: Wr.Dec<Tc.Replay>) -> Wr.Dec<Tc.Gate>:
  match r:
    case Wr.Got{p, s}:
      tc_rg.recover(f, p, tc_rg_now(s))
    case Wr.Bad{}:
      Wr.Bad{}

def tc_rg.intent(f: Bool, x: Bool, r: Wr.Dec<Bool>) -> Wr.Dec<Tc.Gate>:
  match r:
    case Wr.Got{i, s}:
      Wr.Got{Tc.Stop{f, x, i}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def tc_rg.restart(f: Bool, r: Wr.Dec<Bool>) -> Wr.Dec<Tc.Gate>:
  match r:
    case Wr.Got{x, s}:
      tc_rg.intent(f, x, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def tc_rg.found(n: Nat, r: Wr.Dec<Bool>) -> Wr.Dec<Tc.Gate>:
  match n:
    case 0n:
      match r:
        case Wr.Got{f, s}:
          tc_rg.enter(f, tc_rg_now(s))
        case Wr.Bad{}:
          Wr.Bad{}
    case 1n:
      match r:
        case Wr.Got{f, s}:
          tc_rg.stored(f, tc_rg_replay(s))
        case Wr.Bad{}:
          Wr.Bad{}
    case 2n:
      match r:
        case Wr.Got{f, s}:
          tc_rg.restart(f, Wr.get_bool(s))
        case Wr.Bad{}:
          Wr.Bad{}
    case 3n+p:
      Wr.Bad{}

def tc_rg.go(r: Wr.Dec<Nat>) -> Wr.Dec<Tc.Gate>:
  match r:
    case Wr.Got{n, s}:
      tc_rg.found(n, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def tc_rg.end(whole: Bool, q: Tc.Gate) -> Maybe<&2, Tc.Gate>:
  match whole:
    case True{}:
      Some{q}
    case False{}:
      None{}

def tc_rg.whole(d: Wr.Dec<Tc.Gate>) -> Maybe<&2, Tc.Gate>:
  match d:
    case Wr.Got{q, s}:
      tc_rg.end(Wr.end(s), q)
    case Wr.Bad{}:
      None{}

# the gate question s is, when s is exactly one
def tc_read_gate(s: String) -> Maybe<&2, Tc.Gate>:
  tc_rg.whole(tc_rg.go(Wr.get_nat(s)))

# The world of one call, run with the shipped gate (E5)

# the world after the gate answers g to the task at phase ph (c: the
# entry committed; r: running; n effects, s settles, x early runs; p: the
# policy a run's intent records)
def ef_answer(g: Tc.Go, +c: Bool, ph: Sp.Phase, r: Bool, n: Nat, s: Nat, x: Nat, p: Tc.Replay) -> Sp.World:
  match g:
    case Tc.Run{}:
      Sp.Wd{c, Sp.AtExecute{p}, True{}, 1n+n, s, Sp.early_add(c, x)}
    case Tc.Missing{}:
      Sp.Wd{c, ph, r, n, s, x}
    case Tc.Unavailable{}:
      Sp.Wd{c, Sp.Settled{Sp.intent_of(ph)}, False{}, n, 1n+s, x}
    case Tc.Rerun{}:
      Sp.Wd{c, ph, True{}, 1n+n, s, Sp.early_add(c, x)}
    case Tc.Interrupted{}:
      Sp.Wd{c, Sp.Settled{Sp.intent_of(ph)}, False{}, n, 1n+s, x}
    case Tc.Aborted{}:
      Sp.Wd{c, Sp.Settled{Sp.intent_of(ph)}, False{}, n, 1n+s, x}
    case Tc.Abandoned{}:
      Sp.Wd{c, Sp.Settled{Sp.intent_of(ph)}, False{}, n, 1n+s, x}

# the scheduler runs the task's current phase, the tool resolved as t
def ef_start(ph: Sp.Phase, +c: Bool, n: Nat, s: Nat, x: Nat, +t: Tc.Now) -> Sp.World:
  match ph:
    case Sp.NoTask{}:
      ef_answer(Tc.gate(Tc.Enter{c, t}), c, Sp.NoTask{}, False{}, n, s, x, Sp.policy(t))
    case Sp.AtCall{}:
      ef_answer(Tc.gate(Tc.Enter{c, t}), c, Sp.AtCall{}, False{}, n, s, x, Sp.policy(t))
    case Sp.AtExecute{+q}:
      ef_answer(Tc.gate(Tc.Recover{c, q, t}), c, Sp.AtExecute{q}, False{}, n, s, x, q)
    case Sp.Settled{q}:
      Sp.Wd{c, Sp.Settled{q}, False{}, n, s, x}

# a run: never of a running task
def ef_go(r: Bool, ph: Sp.Phase, c: Bool, n: Nat, s: Nat, x: Nat, t: Tc.Now) -> Sp.World:
  match r:
    case True{}:
      Sp.Wd{c, ph, True{}, n, s, x}
    case False{}:
      ef_start(ph, c, n, s, x, t)

# the commit of the entry and the task: once
def ef_commit(ph: Sp.Phase, c: Bool, r: Bool, n: Nat, s: Nat, x: Nat) -> Sp.World:
  match ph:
    case Sp.NoTask{}:
      Sp.Wd{True{}, Sp.AtCall{}, r, n, s, x}
    case Sp.AtCall{}:
      Sp.Wd{c, Sp.AtCall{}, r, n, s, x}
    case Sp.AtExecute{q}:
      Sp.Wd{c, Sp.AtExecute{q}, r, n, s, x}
    case Sp.Settled{q}:
      Sp.Wd{c, Sp.Settled{q}, r, n, s, x}

# the end of the execute settles a running call
def ef_finish(r: Bool, c: Bool, ph: Sp.Phase, n: Nat, s: Nat, x: Nat) -> Sp.World:
  match r:
    case True{}:
      Sp.Wd{c, Sp.Settled{Sp.intent_of(ph)}, False{}, n, 1n+s, x}
    case False{}:
      Sp.Wd{c, ph, False{}, n, s, x}

# the abort handler of a task not settled asks the gate
def ef_abort(ph: Sp.Phase, +c: Bool, r: Bool, n: Nat, s: Nat, x: Nat, k: Bool) -> Sp.World:
  match ph:
    case Sp.NoTask{}:
      ef_answer(Tc.gate(Tc.Stop{c, k, False{}}), c, Sp.NoTask{}, r, n, s, x, Tc.Unsafe{})
    case Sp.AtCall{}:
      ef_answer(Tc.gate(Tc.Stop{c, k, False{}}), c, Sp.AtCall{}, r, n, s, x, Tc.Unsafe{})
    case Sp.AtExecute{q}:
      ef_answer(Tc.gate(Tc.Stop{c, k, True{}}), c, Sp.AtExecute{q}, r, n, s, x, Tc.Unsafe{})
    case Sp.Settled{q}:
      Sp.Wd{c, Sp.Settled{q}, r, n, s, x}

# the world after one event
def ef_step(w: Sp.World, e: Sp.Ev) -> Sp.World:
  match w:
    case Sp.Wd{c, ph, r, n, s, x}:
      match e:
        case Sp.Delta{}:
          Sp.Wd{c, ph, r, n, s, x}
        case Sp.Commit{}:
          ef_commit(ph, c, r, n, s, x)
        case Sp.Start{t}:
          ef_go(r, ph, c, n, s, x, t)
        case Sp.Finish{}:
          ef_finish(r, c, ph, n, s, x)
        case Sp.Crash{}:
          Sp.Wd{c, ph, False{}, n, s, x}
        case Sp.Abort{k}:
          ef_abort(ph, c, r, n, s, x, k)

# the world after the events es, in order, from w
def ef_run(es: List<&2, Sp.Ev>, w: Sp.World) -> Sp.World:
  match es:
    case Nil{}:
      w
    case e <> rest:
      ef_run(rest, ef_step(w, e))

# LAW tool_call_gate_is_spec (E1-E4): the entry answers every gate
# question the Harness spells with the spec's answer, spelled as Rust
# reads it
# EXCLUDES: a run without a committed entry or without an offered tool, a
# rerun of an unsafe call (stored or current policy unsafe, the tool gone),
# a safe call not rerun, a settle for a call no entry holds, an abort
# answered with another code, a field misread, a reply spelled otherwise
law tool_call_gate_is_spec:
  for +q: Tc.Gate
  {FTc.ffi(tc_spell_gate(q)) == tc_spell_go(Sp.gate_spec(q)) : String}

# LAW tool_call_gate_spelled_reads: the laws' reader reads every spelled
# gate question back whole, so tool_call_gate_malformed_exact refuses only
# what Rust never writes
# EXCLUDES: a reader (and so an entry) that refuses a question Rust writes
law tool_call_gate_spelled_reads:
  for +q: Tc.Gate
  {tc_read_gate(tc_spell_gate(q)) == Some{q} : Maybe<&2, Tc.Gate>}

# LAW tool_call_gate_reads: an input the laws' reader reads as exactly one
# gate question is answered as that question spelled
# EXCLUDES: an input read otherwise by the entry than by the wire's grammar
law tool_call_gate_reads:
  for +i: String
  for +q: Tc.Gate
  for got: {tc_read_gate(i) == Some{q} : Maybe<&2, Tc.Gate>}
  {FTc.ffi(i) == FTc.ffi(tc_spell_gate(q)) : String}

# LAW tool_call_gate_malformed_exact: an input the laws' reader does not
# read as exactly one gate question (a bad tag, a short or bad field,
# input left over) answers exactly the error form 'E ' + "tool_call:
# malformed gate"
# EXCLUDES: a guessed question (garbage that runs or settles a call),
# another error text
law tool_call_gate_malformed_exact:
  for +i: String
  for no: {tc_read_gate(i) == None{} : Maybe<&2, Tc.Gate>}
  {FTc.ffi(i) == SCon{'E', SCon{' ', "tool_call: malformed gate"}} : String}

# LAW execute_after_committed (E1, E5): in every history of a call, its
# effect runs (a run, or a rerun) only while a committed assistant entry
# holds the call
# EXCLUDES: a call run from its streamed arguments (a dry run of the
# speculation), a run before the commit of its entry, a task created or
# started before that commit
law execute_after_committed:
  for +es: List<&2, Sp.Ev>
  {Sp.early(ef_run(es, Sp.w0())) == 0n : Nat}

# LAW uncommitted_drop_inert (E4, E5): a history in which the call's
# entry never commits (the stream dropped, aborted or crashed before the
# commit) leaves the world as it was: no run, no intent, no settle
# EXCLUDES: an effect, an intent or a result of a call nobody committed,
# an abort that settles a call that never existed
law uncommitted_drop_inert:
  for +es: List<&2, Sp.Ev>
  for no: {Sp.commits(es) == False{} : Bool}
  {ef_run(es, Sp.w0()) == Sp.w0() : Sp.World}

# LAW effect_once (E2, E5): across every crash and resume, a committed
# call's effect runs at most once, unless the policy its intent recorded
# is safe
# EXCLUDES: an unsafe call (bash) run again after a restart, a call run
# again once its result settled, a running call started a second time, a
# call run again by its abort
law effect_once:
  for +es: List<&2, Sp.Ev>
  {Bool.or(Sp.safe_intent(ef_run(es, Sp.w0())), Nat.is_le(Sp.effects(ef_run(es, Sp.w0())), 1n)) == True{} : Bool}

# LAW effect_settles_once (E1-E5): across every crash, resume and abort, a
# call settles at most once
# EXCLUDES: a second result for one call (a rerun after the settle, an
# abort after the end, an interrupted answer after a finished one)
law effect_settles_once:
  for +es: List<&2, Sp.Ev>
  {Nat.is_le(Sp.settles(ef_run(es, Sp.w0())), 1n) == True{} : Bool}

# LAW tool_call_gate_example: anchor: the bytes the Harness sends and the
# replies (the Rust tests' cases: a first run, a tool no longer offered,
# a call no entry holds; a rerun only when the stored and the current
# policy are both safe, a deselected tool; an abort, one by a restart
# after and before the intent); garbage: a short stop, input left over,
# an unknown tag
# EXCLUDES: an entry that answers other bytes than the grammar's
law tool_call_gate_example:
  {[FTc.ffi("0,T1,1,"), FTc.ffi("0,T0,"), FTc.ffi("0,F1,0,"), FTc.ffi("1,T0,1,0,"), FTc.ffi("1,T0,1,1,"), FTc.ffi("1,T1,1,0,"), FTc.ffi("1,T0,0,"), FTc.ffi("2,TFT"), FTc.ffi("2,TTT"), FTc.ffi("2,TTF")] == ["0,", "2,", "1,", "3,", "4,", "4,", "4,", "5,", "4,", "6,"] : List<&2, String>} & {[FTc.ffi("2,TT"), FTc.ffi("0,T0,x"), FTc.ffi("3,T")] == [SCon{'E', SCon{' ', "tool_call: malformed gate"}}, SCon{'E', SCon{' ', "tool_call: malformed gate"}}, SCon{'E', SCon{' ', "tool_call: malformed gate"}}] : List<&2, String>}

# LAW effect_example: anchor: the histories of the Rust tests: a crash
# between the stream's end and the commit (nothing ran, nothing
# settled); an unsafe bash call resumed after a crash mid-run (settled
# interrupted, run once); a safe call resumed (run again, settled once);
# a task abandoned by a restart before it started
# EXCLUDES: a world that drifts from the Rust it models
law effect_example:
  {ef_run([Sp.Delta{}, Sp.Delta{}, Sp.Crash{}], Sp.w0()) == Sp.w0() : Sp.World} & {ef_run([Sp.Delta{}, Sp.Commit{}, Sp.Start{Tc.Offered{Tc.Unsafe{}}}, Sp.Crash{}, Sp.Start{Tc.Offered{Tc.Unsafe{}}}], Sp.w0()) == Sp.Wd{True{}, Sp.Settled{Some{Tc.Unsafe{}}}, False{}, 1n, 1n, 0n} : Sp.World} & {ef_run([Sp.Commit{}, Sp.Start{Tc.Offered{Tc.Safe{}}}, Sp.Crash{}, Sp.Start{Tc.Offered{Tc.Safe{}}}, Sp.Finish{}], Sp.w0()) == Sp.Wd{True{}, Sp.Settled{Some{Tc.Safe{}}}, False{}, 2n, 1n, 0n} : Sp.World} & {ef_run([Sp.Commit{}, Sp.Abort{True{}}], Sp.w0()) == Sp.Wd{True{}, Sp.Settled{None{}}, False{}, 0n, 1n, 0n} : Sp.World}
