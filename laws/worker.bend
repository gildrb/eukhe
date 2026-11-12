# eukhe: the laws of area worker: the "main + worker" session shape
# (bend/worker.bend) and its entry of the compiled core
# (bend/ffi_worker.bend)

import Base
import ../bend/worker.bend as Wk
import ../bend/ffi_worker.bend as FWk
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# Requirements
# ------------
# Sources: the doc comments of bend/worker.bend, of
# crates/eukhe-bend/src/rules/worker.rs and of the one caller
# crates/eukhe-core/src/durable/children/pause.rs (the "main + worker"
# shape and its pause are Eukhe's own).
#   R1 a pause cancels nothing: Pause, Resume and a message leave the tool
#      calls in flight; only a tool call's end and the run's end lower the
#      count, a tool call's start raises it
#                     pause_never_cancels, pause_only_done_lowers,
#                     tool_count_ledger
#   R2 while paused, every boundary (model request, tool call, child
#      spawn) holds and is parked; nothing starts until a Resume or a
#      waking message
#                     pause_then_holds, parked_names_held, answers_by_event
#   R3 a Resume, or a waking message, runs the tree again: the parked
#      boundary goes on, the kept messages are released in arrival order
#      (a waking message last) and nothing stays kept
#                     wake_runs, running_then_goes, kept_once_in_order,
#                     running_keeps_nothing, answers_by_event
#   R4 a message that arrives while paused and does not wake is kept, and
#      nothing is released while paused; while running a message passes
#      (neither kept nor released); over any history every message that
#      arrived while paused is released or still kept, once, in order
#                     paused_keeps_arrivals, kept_once_in_order,
#                     running_keeps_nothing, answers_by_event
#   R5 a running boundary goes (a tool call counts in flight); a tool
#      call's end lowers the count, never below none; the run's end
#      clears the parked boundary and the count and keeps the mode
#                     running_then_goes, tool_count_ledger,
#                     parked_names_held, pause_then_holds
#   R6 the forward pick hands on every message past the cursor, in list
#      order, its text verbatim (joined by a blank line, then main's note),
#      moves the cursor to the largest seq handed on (never back), and a
#      second pick never hands on a seq again
#                     laws/worker/forward.bend: forward_picks_split,
#                     forward_picks_one, forward_verbatim,
#                     forward_cursor_largest, forward_cursor_monotone,
#                     forward_once
#   R7 the entry answers every request Rust spells with the spelling of
#      the model's answer, refuses input left over and any input that is
#      not a spelled request; the reply grammar spells each answer apart
#                     worker_ffi_* (the entry laws below),
#                     worker_reply_verdict_unambiguous,
#                     worker_reply_pick_unambiguous
#   A1 a gate answers Go or Hold, nothing else: the caller fails the run on
#      any other answer at a gate (pause.rs:270-277)
#                     running_then_goes, pause_then_holds, answers_by_event
#   A2 the parked boundary is the one a gate holds now: the caller counts a
#      paused run with a parked boundary and no tool call in flight as idle
#      (pause.rs:105-116, PauseView.held)
#                     parked_names_held, pause_then_holds
#   A3 a running tree keeps no message: kept messages wait only while the
#      tree is paused (pause.rs:15-20); a new tree keeps none
#                     running_keeps_nothing
# Anchors (not coverage): pause_example, pause_rust_example,
# forward_example, worker_ffi_example; witness: worker_ffi_premises_witness.

# Spec helpers: the pause
# -----------------------

# the state of a new worker tree (Rust's PauseState::default): running,
# nothing parked, kept or in flight
def wk_init() -> Wk.St:
  Wk.St{Wk.Run{}, None{}, Nil{}, 0n}

def wk_state(r: Wk.St & Wk.Verdict) -> Wk.St:
  (s, v) = r
  s

def wk_verdict(r: Wk.St & Wk.Verdict) -> Wk.Verdict:
  (s, v) = r
  v

def wk_inflight(s: Wk.St) -> Nat:
  match s:
    case Wk.St{m, p, k, n}:
      n

def wk_kept(s: Wk.St) -> List<&2, Nat>:
  match s:
    case Wk.St{m, p, k, n}:
      k

# the tree is paused
def wk_paused(s: Wk.St) -> Bool:
  match s:
    case Wk.St{m, p, k, n}:
      match m:
        case Wk.Run{}:
          False{}
        case Wk.Paused{}:
          True{}

# the events that leave the count of tool calls in flight as it is: a
# pause, a resume, a message
def wk_keeps_count(e: Wk.Ev) -> Bool:
  match e:
    case Wk.Pause{}:
      True{}
    case Wk.Resume{}:
      True{}
    case Wk.Gate{g, i}:
      False{}
    case Wk.ToolDone{}:
      False{}
    case Wk.Msg{i, w}:
      True{}
    case Wk.End{}:
      False{}

# the events that may lower the count: a tool call's end, the run's end
def wk_may_lower(e: Wk.Ev) -> Bool:
  match e:
    case Wk.Pause{}:
      False{}
    case Wk.Resume{}:
      False{}
    case Wk.Gate{g, i}:
      False{}
    case Wk.ToolDone{}:
      True{}
    case Wk.Msg{i, w}:
      False{}
    case Wk.End{}:
      True{}

# the parked boundary
def wk_parked(s: Wk.St) -> Maybe<&2, Nat>:
  match s:
    case Wk.St{m, p, k, n}:
      p

# the events that wake the tree: a resume, a waking message
def wk_wakes(e: Wk.Ev) -> Bool:
  match e:
    case Wk.Pause{}:
      False{}
    case Wk.Resume{}:
      True{}
    case Wk.Gate{g, i}:
      False{}
    case Wk.ToolDone{}:
      False{}
    case Wk.Msg{i, w}:
      w
    case Wk.End{}:
      False{}

# no pause among the events h
def wk_no_pause(h: List<&2, Wk.Ev>) -> Bool:
  match h:
    case Nil{}:
      True{}
    case Con{e, r}:
      match e:
        case Wk.Pause{}:
          False{}
        case Wk.Resume{}:
          wk_no_pause(r)
        case Wk.Gate{g, i}:
          wk_no_pause(r)
        case Wk.ToolDone{}:
          wk_no_pause(r)
        case Wk.Msg{i, w}:
          wk_no_pause(r)
        case Wk.End{}:
          wk_no_pause(r)

# the tree is paused, or it keeps no message
def wk_clean(s: Wk.St) -> Bool:
  match s:
    case Wk.St{m, p, k, n}:
      match m:
        case Wk.Paused{}:
          True{}
        case Wk.Run{}:
          match k:
            case Nil{}:
              True{}
            case Con{x, r}:
              False{}

# the ids of the messages of h, in order (whatever the mode)
def wk_msg_ids(h: List<&2, Wk.Ev>) -> List<&2, Nat>:
  match h:
    case Nil{}:
      Nil{}
    case Con{e, r}:
      match e:
        case Wk.Msg{i, w}:
          i <> wk_msg_ids(r)
        case Wk.Pause{}:
          wk_msg_ids(r)
        case Wk.Resume{}:
          wk_msg_ids(r)
        case Wk.Gate{g, i}:
          wk_msg_ids(r)
        case Wk.ToolDone{}:
          wk_msg_ids(r)
        case Wk.End{}:
          wk_msg_ids(r)

# one when b holds, else none
def wk_one_if(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# the tool calls a gate of kind g answered v starts: one for a tool call
# (kind 1: Rust's kind_code, worker.rs:176-182) that goes, else none
def wk_went_tool(g: Nat, v: Wk.Verdict) -> Nat:
  match v:
    case Wk.Go{}:
      wk_one_if(Nat.is_eq(g, 1n))
    case Wk.Hold{}:
      0n
    case Wk.Release{xs}:
      0n
    case Wk.Kept{}:
      0n
    case Wk.Pass{}:
      0n
    case Wk.Ack{}:
      0n

# the count of tool calls in flight after event e answered v, from n: a
# tool call that goes adds one; a tool call's end takes one, never below
# none (Base Nat.sub); the run's end clears it; nothing else moves it
def wk_counts(e: Wk.Ev, v: Wk.Verdict, n: Nat) -> Nat:
  match e:
    case Wk.Pause{}:
      n
    case Wk.Resume{}:
      n
    case Wk.Gate{g, i}:
      Nat.add(wk_went_tool(g, v), n)
    case Wk.ToolDone{}:
      Nat.sub(n, 1n)
    case Wk.Msg{i, w}:
      n
    case Wk.End{}:
      0n

# the parked boundary after a gate named i answered v, from p: a hold
# parks i, a go clears it
def wk_parks.gate(v: Wk.Verdict, i: Nat, p: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match v:
    case Wk.Hold{}:
      Some{i}
    case Wk.Go{}:
      None{}
    case Wk.Release{xs}:
      p
    case Wk.Kept{}:
      p
    case Wk.Pass{}:
      p
    case Wk.Ack{}:
      p

# the parked boundary after event e answered v, from p: a gate parks or
# clears it, the run's end clears it, nothing else moves it
def wk_parks(e: Wk.Ev, v: Wk.Verdict, p: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match e:
    case Wk.Gate{g, i}:
      wk_parks.gate(v, i, p)
    case Wk.End{}:
      None{}
    case Wk.Pause{}:
      p
    case Wk.Resume{}:
      p
    case Wk.ToolDone{}:
      p
    case Wk.Msg{i, w}:
      p

# the class of an answer: 0 go, 1 hold, 2 release, 3 kept, 4 pass, 5 ack
def wk_class(v: Wk.Verdict) -> Nat:
  match v:
    case Wk.Go{}:
      0n
    case Wk.Hold{}:
      1n
    case Wk.Release{xs}:
      2n
    case Wk.Kept{}:
      3n
    case Wk.Pass{}:
      4n
    case Wk.Ack{}:
      5n

# a gate goes when the tree ran (R5) and holds when it was paused (R2, A1);
# b: paused before
def wk_expect.gate(b: Bool) -> Nat:
  match b:
    case False{}:
      0n
    case True{}:
      1n

# a message passes when the tree ran (R4), is kept when the tree stays
# paused (R4), releases when it woke the tree (R3); b, a: paused before,
# after
def wk_expect.msg(b: Bool, a: Bool) -> Nat:
  match b:
    case False{}:
      4n
    case True{}:
      match a:
        case True{}:
          3n
        case False{}:
          2n

# the class of the answer to e, the tree paused before it (b) and after it
# (a): a pause, a tool call's end and the run's end are noted (R1, R5); a
# resume releases what was kept (R3)
def wk_expect(e: Wk.Ev, b: Bool, a: Bool) -> Nat:
  match e:
    case Wk.Pause{}:
      5n
    case Wk.Resume{}:
      2n
    case Wk.Gate{g, i}:
      wk_expect.gate(b)
    case Wk.ToolDone{}:
      5n
    case Wk.Msg{i, w}:
      wk_expect.msg(b, a)
    case Wk.End{}:
      5n

# the state that holds the boundary id: paused, with what s kept and has
# in flight
def wk_held(s: Wk.St, id: Nat) -> Wk.St:
  match s:
    case Wk.St{m, p, k, n}:
      Wk.St{Wk.Paused{}, Some{id}, k, n}

# the state after the events h, from s
def wk_after(h: List<&2, Wk.Ev>, s: Wk.St) -> Wk.St:
  match h:
    case Nil{}:
      s
    case Con{e, r}:
      wk_after(r, wk_state(Wk.step(s, e)))

# the answers to the events h, from s, in order
def wk_answers(h: List<&2, Wk.Ev>, +s: Wk.St) -> List<&2, Wk.Verdict>:
  match h:
    case Nil{}:
      Nil{}
    case Con{+e, r}:
      wk_verdict(Wk.step(s, e)) <> wk_answers(r, wk_state(Wk.step(s, e)))

# no resume and no waking message
def wk_quiet(h: List<&2, Wk.Ev>) -> Bool:
  match h:
    case Nil{}:
      True{}
    case Con{e, r}:
      match e:
        case Wk.Resume{}:
          False{}
        case Wk.Msg{i, w}:
          match w:
            case True{}:
              False{}
            case False{}:
              wk_quiet(r)
        case Wk.Pause{}:
          wk_quiet(r)
        case Wk.Gate{g, i}:
          wk_quiet(r)
        case Wk.ToolDone{}:
          wk_quiet(r)
        case Wk.End{}:
          wk_quiet(r)

# the ids an answer releases
def wk_released(v: Wk.Verdict) -> List<&2, Nat>:
  match v:
    case Wk.Release{xs}:
      xs
    case Wk.Go{}:
      Nil{}
    case Wk.Hold{}:
      Nil{}
    case Wk.Kept{}:
      Nil{}
    case Wk.Pass{}:
      Nil{}
    case Wk.Ack{}:
      Nil{}

# the ids released over the events h from s, in order, then the ids still
# kept at the end
def wk_out(h: List<&2, Wk.Ev>, +s: Wk.St) -> List<&2, Nat>:
  match h:
    case Nil{}:
      wk_kept(s)
    case Con{+e, r}:
      List.append(&2, Nat, wk_released(wk_verdict(Wk.step(s, e))), wk_out(r, wk_state(Wk.step(s, e))))

# the ids of the messages of h that arrive while the tree is paused, in
# arrival order; p: the tree is paused before h. Only the mode is tracked:
# a pause pauses, a resume runs, a waking message runs a paused tree.
def wk_arrived(h: List<&2, Wk.Ev>, p: Bool) -> List<&2, Nat>:
  match h:
    case Nil{}:
      Nil{}
    case Con{e, r}:
      match e:
        case Wk.Pause{}:
          wk_arrived(r, True{})
        case Wk.Resume{}:
          wk_arrived(r, False{})
        case Wk.Msg{i, w}:
          match p:
            case True{}:
              i <> wk_arrived(r, Bool.not(w))
            case False{}:
              wk_arrived(r, False{})
        case Wk.Gate{g, i}:
          wk_arrived(r, p)
        case Wk.ToolDone{}:
          wk_arrived(r, p)
        case Wk.End{}:
          wk_arrived(r, p)

# Laws: the pause, event by event, in any state
# ---------------------------------------------

# LAW wake_runs: in any state, a resume or a waking message (the user's,
# or a forward from main) leaves the tree running
# EXCLUDES: a resume or a user's message that leaves the tree paused (its
#   parked boundary would hold on), a resume that pauses a running tree
law wake_runs:
  for +s: Wk.St
  for +e: Wk.Ev
  for wakes: {wk_wakes(e) == True{} : Bool}
  {wk_paused(wk_state(Wk.step(s, e))) == False{} : Bool}

# LAW tool_count_ledger: in any state, after any event, the count of tool
# calls in flight is the count before, plus one for a tool call (kind 1)
# whose gate answered Go, less one for a tool call's end (Base Nat.sub:
# never below none), none after the run's end, and the same otherwise
# EXCLUDES: a tool call counted when its gate held, or never counted; a
#   model request or a spawn counted; a count that wraps or goes below
#   none; a stale count kept past the run's end
law tool_count_ledger:
  for +s: Wk.St
  for +e: Wk.Ev
  {wk_inflight(wk_state(Wk.step(s, e))) == wk_counts(e, wk_verdict(Wk.step(s, e)), wk_inflight(s)) : Nat}

# LAW parked_names_held: in any state, after any event, the parked
# boundary is the one a gate holds: a gate answered Hold parks its id, a
# gate answered Go and the run's end clear it, every other event leaves it
# EXCLUDES: a held boundary not parked (the run would not count as idle
#   at it), a boundary still parked after it went or after the run ended,
#   a pause, resume, message or tool's end that drops or invents one
law parked_names_held:
  for +s: Wk.St
  for +e: Wk.Ev
  {wk_parked(wk_state(Wk.step(s, e))) == wk_parks(e, wk_verdict(Wk.step(s, e)), wk_parked(s)) : Maybe<&2, Nat>}

# LAW answers_by_event: in any state, the answer to an event says what
# happened (table wk_expect, over the mode before and after): a pause, a
# tool call's end and the run's end are noted (Ack); a resume releases; a
# gate goes when the tree ran and holds when it was paused; a message
# passes when the tree ran, is kept when the tree stays paused, releases
# when it woke the tree
# EXCLUDES: a gate answered anything but Go or Hold (the caller fails the
#   run), a pause, tool's end or run's end that releases (and so drops)
#   kept messages, a waking message answered Kept, a message to a running
#   tree kept
law answers_by_event:
  for +s: Wk.St
  for +e: Wk.Ev
  {wk_class(wk_verdict(Wk.step(s, e))) == wk_expect(e, wk_paused(s), wk_paused(wk_state(Wk.step(s, e)))) : Nat}

# LAW running_keeps_nothing: a tree that is paused or keeps no message is
# so after any event: a running tree never keeps a message (a new tree,
# wk_init, keeps none)
# EXCLUDES: a resume or a waking message that runs the tree but keeps the
#   messages it held (they would never be released), a message kept by a
#   running tree
law running_keeps_nothing:
  for +s: Wk.St
  for +e: Wk.Ev
  for clean: {wk_clean(s) == True{} : Bool}
  {wk_clean(wk_state(Wk.step(s, e))) == True{} : Bool}

# Laws: the pause, over events and histories
# ------------------------------------------

# LAW pause_never_cancels: a pause, a resume and a message leave the count
# of tool calls in flight as it is, in any state
# EXCLUDES: a pause (or resume, or message) that cancels or forgets a
#   running tool call
law pause_never_cancels:
  for +s: Wk.St
  for +e: Wk.Ev
  for keeps: {wk_keeps_count(e) == True{} : Bool}
  {wk_inflight(wk_state(Wk.step(s, e))) == wk_inflight(s) : Nat}

# LAW pause_only_done_lowers: no event but a tool call's end and the run's
# end lowers the count of tool calls in flight
# EXCLUDES: a gate, pause, resume or message that lowers the count
law pause_only_done_lowers:
  for +s: Wk.St
  for +e: Wk.Ev
  for other: {wk_may_lower(e) == False{} : Bool}
  {Nat.is_le(wk_inflight(s), wk_inflight(wk_state(Wk.step(s, e)))) == True{} : Bool}

# LAW pause_then_holds: from any state, after a pause and then any events
# with no resume and no waking message, a gate of any kind holds and is
# parked, the count and the kept messages as they are
# EXCLUDES: a pause undone by a gate, a tool's end, a report, the run's
#   end or another pause, so that a later boundary starts
law pause_then_holds:
  for +s: Wk.St
  for +h: List<&2, Wk.Ev>
  for quiet: {wk_quiet(h) == True{} : Bool}
  for +kind: Nat
  for +id: Nat
  {Wk.step(wk_after(h, wk_state(Wk.step(s, Wk.Pause{}))), Wk.Gate{kind, id}) == (wk_held(wk_after(h, wk_state(Wk.step(s, Wk.Pause{}))), id), Wk.Hold{}) : Wk.St & Wk.Verdict}

# LAW running_then_goes: from any running state, after any events with no
# pause among them, a gate of any kind goes (with wake_runs: after a resume
# or a waking message the parked boundary goes on)
# EXCLUDES: a running boundary that holds; a gate, a tool's end, a
#   message, a resume or the run's end that pauses a running tree; a
#   boundary still held after a resume
law running_then_goes:
  for +s: Wk.St
  for run: {wk_paused(s) == False{} : Bool}
  for +h: List<&2, Wk.Ev>
  for calm: {wk_no_pause(h) == True{} : Bool}
  for +kind: Nat
  for +id: Nat
  {wk_verdict(Wk.step(wk_after(h, s), Wk.Gate{kind, id})) == Wk.Go{} : Wk.Verdict}

# LAW paused_keeps_arrivals: from any state, after a pause and then any
# events with no resume and no waking message, the kept messages are the
# ones kept before, then every message of those events, in arrival order:
# nothing is released while paused
# EXCLUDES: a report released or passed by a paused tree, a kept message
#   dropped, reordered or put first
law paused_keeps_arrivals:
  for +s: Wk.St
  for +h: List<&2, Wk.Ev>
  for quiet: {wk_quiet(h) == True{} : Bool}
  {wk_kept(wk_after(h, wk_state(Wk.step(s, Wk.Pause{})))) == List.append(&2, Nat, wk_kept(s), wk_msg_ids(h)) : List<&2, Nat>}

# LAW kept_once_in_order: over any events from any state, the ids released
# (every Release, in order), then the ids still kept, are the ids kept at
# the start, then the ids of the messages that arrived while paused, in
# arrival order: each once, none invented (from the initial state: exactly
# the messages that arrived while paused)
# EXCLUDES: a kept message lost, released twice, released out of order, or
#   a message that arrived while running released as if kept
law kept_once_in_order:
  for +h: List<&2, Wk.Ev>
  for +s: Wk.St
  {wk_out(h, s) == List.append(&2, Nat, wk_kept(s), wk_arrived(h, wk_paused(s))) : List<&2, Nat>}

# LAW pause_example: anchor: from a new tree: a tool call goes; a pause;
# a model request holds; a report is kept; the tool call ends; the user's
# message releases the report then itself; the request goes on
# EXCLUDES: a model whose answers to this session differ
law pause_example:
  {wk_answers([Wk.Gate{1n, 1n}, Wk.Pause{}, Wk.Gate{0n, 2n}, Wk.Msg{7n, False{}}, Wk.ToolDone{}, Wk.Msg{8n, True{}}, Wk.Gate{0n, 2n}], wk_init()) == [Wk.Go{}, Wk.Ack{}, Wk.Hold{}, Wk.Kept{}, Wk.Ack{}, Wk.Release{[7n, 8n]}, Wk.Go{}] : List<&2, Wk.Verdict>}

# LAW pause_rust_example: anchor: the nine steps of the Rust test
# each_event_steps_in_the_core (crates/eukhe-bend/src/rules/worker.rs:
# 251-310): the states after them, then the answers, as that test expects
# EXCLUDES: a model whose steps differ from the Rust test's vectors
law pause_rust_example:
  {[wk_state(Wk.step(wk_init(), Wk.Pause{})), wk_state(Wk.step(Wk.St{Wk.Paused{}, Some{5n}, [7n], 1n}, Wk.Resume{})), wk_state(Wk.step(Wk.St{Wk.Run{}, Some{5n}, [], 1n}, Wk.Gate{1n, 6n})), wk_state(Wk.step(Wk.St{Wk.Paused{}, None{}, [], 1n}, Wk.Gate{2n, 6n})), wk_state(Wk.step(Wk.St{Wk.Paused{}, Some{6n}, [], 1n}, Wk.ToolDone{})), wk_state(Wk.step(Wk.St{Wk.Paused{}, Some{6n}, [7n], 0n}, Wk.Msg{9n, False{}})), wk_state(Wk.step(Wk.St{Wk.Paused{}, Some{6n}, [7n, 9n], 0n}, Wk.Msg{10n, True{}})), wk_state(Wk.step(Wk.St{Wk.Run{}, None{}, [], 0n}, Wk.Msg{11n, True{}})), wk_state(Wk.step(Wk.St{Wk.Paused{}, Some{6n}, [7n], 2n}, Wk.End{}))] == [Wk.St{Wk.Paused{}, None{}, [], 0n}, Wk.St{Wk.Run{}, Some{5n}, [], 1n}, Wk.St{Wk.Run{}, None{}, [], 2n}, Wk.St{Wk.Paused{}, Some{6n}, [], 1n}, Wk.St{Wk.Paused{}, Some{6n}, [], 0n}, Wk.St{Wk.Paused{}, Some{6n}, [7n, 9n], 0n}, Wk.St{Wk.Run{}, Some{6n}, [], 0n}, Wk.St{Wk.Run{}, None{}, [], 0n}, Wk.St{Wk.Paused{}, None{}, [7n], 0n}] : List<&2, Wk.St>} & {[wk_verdict(Wk.step(wk_init(), Wk.Pause{})), wk_verdict(Wk.step(Wk.St{Wk.Paused{}, Some{5n}, [7n], 1n}, Wk.Resume{})), wk_verdict(Wk.step(Wk.St{Wk.Run{}, Some{5n}, [], 1n}, Wk.Gate{1n, 6n})), wk_verdict(Wk.step(Wk.St{Wk.Paused{}, None{}, [], 1n}, Wk.Gate{2n, 6n})), wk_verdict(Wk.step(Wk.St{Wk.Paused{}, Some{6n}, [], 1n}, Wk.ToolDone{})), wk_verdict(Wk.step(Wk.St{Wk.Paused{}, Some{6n}, [7n], 0n}, Wk.Msg{9n, False{}})), wk_verdict(Wk.step(Wk.St{Wk.Paused{}, Some{6n}, [7n, 9n], 0n}, Wk.Msg{10n, True{}})), wk_verdict(Wk.step(Wk.St{Wk.Run{}, None{}, [], 0n}, Wk.Msg{11n, True{}})), wk_verdict(Wk.step(Wk.St{Wk.Paused{}, Some{6n}, [7n], 2n}, Wk.End{}))] == [Wk.Ack{}, Wk.Release{[7n]}, Wk.Go{}, Wk.Hold{}, Wk.Ack{}, Wk.Kept{}, Wk.Release{[7n, 9n, 10n]}, Wk.Pass{}, Wk.Ack{}] : List<&2, Wk.Verdict>}

# Spec spellers: the entry
# ------------------------
# The grammar of the header of bend/ffi_worker.bend, spelled with the wire
# primitives and the spellers of laws/base.bend, never with the entry's own
# encoders.

# a mode: tag 0 run, 1 paused
def wk_spell_mode(m: Wk.Mode, rest: String) -> String:
  match m:
    case Wk.Run{}:
      Wr.put_nat(0n, rest)
    case Wk.Paused{}:
      Wr.put_nat(1n, rest)

# the parked boundary: tag 0 none, 1 then its id
def wk_spell_parked(p: Maybe<&2, Nat>, rest: String) -> String:
  match p:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      Wr.put_nat(1n, Wr.put_nat(x, rest))

# a pause state: mode, parked, kept, in flight
def wk_spell_st(s: Wk.St, rest: String) -> String:
  match s:
    case Wk.St{m, p, k, n}:
      wk_spell_mode(m, wk_spell_parked(p, LawsBase.wire_spell_nats(k, Wr.put_nat(n, rest))))

# an event: tag 0 pause, 1 resume, 2 gate (kind, id), 3 done, 4 message
# (id, wakes), 5 end
def wk_spell_ev(e: Wk.Ev, rest: String) -> String:
  match e:
    case Wk.Pause{}:
      Wr.put_nat(0n, rest)
    case Wk.Resume{}:
      Wr.put_nat(1n, rest)
    case Wk.Gate{g, i}:
      Wr.put_nat(2n, Wr.put_nat(g, Wr.put_nat(i, rest)))
    case Wk.ToolDone{}:
      Wr.put_nat(3n, rest)
    case Wk.Msg{i, w}:
      Wr.put_nat(4n, Wr.put_nat(i, Wr.put_bool(w, rest)))
    case Wk.End{}:
      Wr.put_nat(5n, rest)

# a message: its seq, then its text
def wk_spell_umsg(m: Wk.UMsg, rest: String) -> String:
  match m:
    case Wk.UMsg{q, t}:
      Wr.put_nat(q, Wr.put_str(t, rest))

def wk_spell_umsgs.items(ms: List<&2, Wk.UMsg>, rest: String) -> String:
  match ms:
    case Nil{}:
      rest
    case Con{m, r}:
      wk_spell_umsg(m, wk_spell_umsgs.items(r, rest))

# the messages: their count, then each
def wk_spell_umsgs(+ms: List<&2, Wk.UMsg>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Wk.UMsg, ms), wk_spell_umsgs.items(ms, rest))

# main's note: tag 0 none, 1 then its text
def wk_spell_note(n: Maybe<&2, String>, rest: String) -> String:
  match n:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{t}:
      Wr.put_nat(1n, Wr.put_str(t, rest))

# a request: tag 0 a step (state, event), 1 a forward (cursor, messages,
# note)
def wk_spell_req(r: FWk.Req, rest: String) -> String:
  match r:
    case FWk.Step{s, e}:
      Wr.put_nat(0n, wk_spell_st(s, wk_spell_ev(e, rest)))
    case FWk.Forward{c, ms, n}:
      Wr.put_nat(1n, Wr.put_nat(c, wk_spell_umsgs(ms, wk_spell_note(n, rest))))

# an answer: tag 0 go, 1 hold, 2 release (ids), 3 kept, 4 pass, 5 ack
def wk_spell_verdict(v: Wk.Verdict, rest: String) -> String:
  match v:
    case Wk.Go{}:
      Wr.put_nat(0n, rest)
    case Wk.Hold{}:
      Wr.put_nat(1n, rest)
    case Wk.Release{xs}:
      Wr.put_nat(2n, LawsBase.wire_spell_nats(xs, rest))
    case Wk.Kept{}:
      Wr.put_nat(3n, rest)
    case Wk.Pass{}:
      Wr.put_nat(4n, rest)
    case Wk.Ack{}:
      Wr.put_nat(5n, rest)

# a pick: the cursor, the seqs, the text
def wk_spell_pick(x: Wk.Pick, rest: String) -> String:
  match x:
    case Wk.Pick{c, ps, b}:
      Wr.put_nat(c, LawsBase.wire_spell_nats(ps, Wr.put_str(b, rest)))

# a step's reply: the new state, then the answer
def wk_spell_stepped(r: Wk.St & Wk.Verdict) -> String:
  (s, v) = r
  wk_spell_st(s, wk_spell_verdict(v, ""))

# the spelling of the model's answer to request r
def wk_spell_reply(r: FWk.Req) -> String:
  match r:
    case FWk.Step{s, e}:
      wk_spell_stepped(Wk.step(s, e))
    case FWk.Forward{c, ms, n}:
      wk_spell_pick(Wk.pick(c, ms, n), "")

# Spec readers: the replies
# -------------------------
# Readers of the reply grammar (the header of bend/ffi_worker.bend), in the
# order Rust reads a reply (crates/eukhe-bend/src/rules/worker.rs:129-140,
# 166-172). They witness that a reply spelling names one answer; no
# shipped code calls them (Rust reads the replies).

def wk_read_verdict.release(d: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<Wk.Verdict>:
  match d:
    case Wr.Got{xs, s}:
      Wr.Got{Wk.Release{xs}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def wk_read_verdict.tag(t: Nat, s: String) -> Wr.Dec<Wk.Verdict>:
  match t:
    case 0n:
      Wr.Got{Wk.Go{}, s}
    case 1n:
      Wr.Got{Wk.Hold{}, s}
    case 2n:
      wk_read_verdict.release(Wr.get_list(~Nat, ~Wr.get_nat, s))
    case 3n:
      Wr.Got{Wk.Kept{}, s}
    case 4n:
      Wr.Got{Wk.Pass{}, s}
    case 5n:
      Wr.Got{Wk.Ack{}, s}
    case 6n+x:
      Wr.Bad{}

def wk_read_verdict.go(d: Wr.Dec<Nat>) -> Wr.Dec<Wk.Verdict>:
  match d:
    case Wr.Got{t, s}:
      wk_read_verdict.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

# a verdict: its tag, then the released ids of a release
def wk_read_verdict(s: String) -> Wr.Dec<Wk.Verdict>:
  wk_read_verdict.go(Wr.get_nat(s))

def wk_read_pick.body(c: Nat, ps: List<&2, Nat>, d: Wr.Dec<String>) -> Wr.Dec<Wk.Pick>:
  match d:
    case Wr.Got{b, s}:
      Wr.Got{Wk.Pick{c, ps, b}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def wk_read_pick.picked(c: Nat, d: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<Wk.Pick>:
  match d:
    case Wr.Got{ps, s}:
      wk_read_pick.body(c, ps, Wr.get_str(s))
    case Wr.Bad{}:
      Wr.Bad{}

def wk_read_pick.cursor(d: Wr.Dec<Nat>) -> Wr.Dec<Wk.Pick>:
  match d:
    case Wr.Got{c, s}:
      wk_read_pick.picked(c, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case Wr.Bad{}:
      Wr.Bad{}

# a pick: the cursor, the seqs, the text
def wk_read_pick(s: String) -> Wr.Dec<Wk.Pick>:
  wk_read_pick.cursor(Wr.get_nat(s))

# Spec helpers: what fits the wire
# --------------------------------

def wk_nats_fit(+xs: List<&2, Nat>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs))

def wk_st_fits(s: Wk.St) -> Bool:
  match s:
    case Wk.St{m, p, k, n}:
      Bool.and(LawsBase.wire_mfits(p), Bool.and(wk_nats_fit(k), LawsBase.wire_fits(n)))

def wk_ev_fits(e: Wk.Ev) -> Bool:
  match e:
    case Wk.Pause{}:
      True{}
    case Wk.Resume{}:
      True{}
    case Wk.Gate{g, i}:
      Bool.and(LawsBase.wire_fits(g), LawsBase.wire_fits(i))
    case Wk.ToolDone{}:
      True{}
    case Wk.Msg{i, w}:
      LawsBase.wire_fits(i)
    case Wk.End{}:
      True{}

def wk_umsg_fits(m: Wk.UMsg) -> Bool:
  match m:
    case Wk.UMsg{q, t}:
      Bool.and(LawsBase.wire_fits(q), LawsBase.wire_fits(String.length(t)))

def wk_umsgs_all(ms: List<&2, Wk.UMsg>) -> Bool:
  match ms:
    case Nil{}:
      True{}
    case Con{m, r}:
      Bool.and(wk_umsg_fits(m), wk_umsgs_all(r))

def wk_umsgs_fit(+ms: List<&2, Wk.UMsg>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Wk.UMsg, ms)), wk_umsgs_all(ms))

def wk_note_fits(n: Maybe<&2, String>) -> Bool:
  match n:
    case None{}:
      True{}
    case Some{t}:
      LawsBase.wire_fits(String.length(t))

# every count, length and Nat of a request fits the wire
def wk_req_fits(r: FWk.Req) -> Bool:
  match r:
    case FWk.Step{s, e}:
      Bool.and(wk_st_fits(s), wk_ev_fits(e))
    case FWk.Forward{c, ms, n}:
      Bool.and(LawsBase.wire_fits(c), Bool.and(wk_umsgs_fit(ms), wk_note_fits(n)))

def wk_verdict_fits(v: Wk.Verdict) -> Bool:
  match v:
    case Wk.Release{xs}:
      wk_nats_fit(xs)
    case Wk.Go{}:
      True{}
    case Wk.Hold{}:
      True{}
    case Wk.Kept{}:
      True{}
    case Wk.Pass{}:
      True{}
    case Wk.Ack{}:
      True{}

def wk_pick_fits(x: Wk.Pick) -> Bool:
  match x:
    case Wk.Pick{c, ps, b}:
      Bool.and(LawsBase.wire_fits(c), Bool.and(wk_nats_fit(ps), LawsBase.wire_fits(String.length(b))))

# Laws: the entry
# ---------------

# LAW worker_ffi_decides: a request spelled by the grammar, whose counts,
# lengths and Nats fit the wire, is answered with the spelling of the
# model's answer: the new state and the verdict of a step, the pick of a
# forward
# EXCLUDES: an entry that answers another event, state or cursor, a field
#   lost or swapped on the way to the model, a reply in another tag or
#   order, a default
law worker_ffi_decides:
  for +r: FWk.Req
  for h: {wk_req_fits(r) == True{} : Bool}
  {FWk.ffi(wk_spell_req(r, "")) == wk_spell_reply(r) : String}

# LAW worker_ffi_spelled_left_over: input left over after a spelled request
# is refused
# EXCLUDES: trailing input ignored, or read as part of the request
law worker_ffi_spelled_left_over:
  for +r: FWk.Req
  for +rest: String
  for h: {wk_req_fits(r) == True{} : Bool}
  for more: {String.is_empty(rest) == False{} : Bool}
  {FWk.ffi(wk_spell_req(r, rest)) == Wr.err("worker: input left over") : String}

# LAW worker_ffi_reads_only_requests: an answer that is not the error form
# answers a request: the input is the spelling of a request that fits the
# wire, and the answer is the model's answer to it
# EXCLUDES: a decoder that accepts an unknown tag, a bad flag, a short
#   string, a count or Nat past the wire, or a missing field, and answers
#   it anyway (a default instead of the error form)
law worker_ffi_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FWk.ffi(s)) == False{} : Bool}
  exs r: FWk.Req
  {(s, (wk_req_fits(r), FWk.ffi(s))) == (wk_spell_req(r, ""), (True{}, wk_spell_reply(r))) : String & (Bool & String)}

# LAW worker_ffi_malformed_unless_request: an input that does not begin
# with a spelled request that fits answers the malformed error: any other
# answer comes from an input that is a spelled request that fits, then
# possibly more
# EXCLUDES: the left-over error, another error text, or a reply, for input
#   that holds no request
law worker_ffi_malformed_unless_request:
  for +s: String
  for other: {String.eq(FWk.ffi(s), Wr.err("worker: malformed request")) == False{} : Bool}
  exs r: FWk.Req
  exs rest: String
  {(s, wk_req_fits(r)) == (wk_spell_req(r, rest), True{}) : String & Bool}

# LAW worker_ffi_unknown_req: a request tag past 1 (step, forward) is
# malformed, whatever follows
# EXCLUDES: an unknown request read as a step or a forward
law worker_ffi_unknown_req:
  for +n: Nat
  for +rest: String
  {FWk.ffi(Wr.put_nat(2n+n, rest)) == Wr.err("worker: malformed request") : String}

# LAW worker_ffi_unknown_mode: in a step, a mode tag past 1 (run, paused) is
# malformed, whatever follows
# EXCLUDES: an unknown mode read as running or paused
law worker_ffi_unknown_mode:
  for +n: Nat
  for +rest: String
  {FWk.ffi(Wr.put_nat(0n, Wr.put_nat(2n+n, rest))) == Wr.err("worker: malformed request") : String}

# LAW worker_ffi_unknown_parked: in a step, a parked tag past 1 (none, an
# id) is malformed, whatever follows
# EXCLUDES: an unknown parked tag read as none or as an id
law worker_ffi_unknown_parked:
  for +m: Wk.Mode
  for +n: Nat
  for +rest: String
  {FWk.ffi(Wr.put_nat(0n, wk_spell_mode(m, Wr.put_nat(2n+n, rest)))) == Wr.err("worker: malformed request") : String}

# LAW worker_ffi_unknown_ev: in a step, after a state that fits, an event
# tag past 5 is malformed, whatever follows
# EXCLUDES: an unknown event read as a pause, a gate, a message or an end
law worker_ffi_unknown_ev:
  for +s: Wk.St
  for +n: Nat
  for +rest: String
  for h: {wk_st_fits(s) == True{} : Bool}
  {FWk.ffi(Wr.put_nat(0n, wk_spell_st(s, Wr.put_nat(6n+n, rest)))) == Wr.err("worker: malformed request") : String}

# LAW worker_ffi_unknown_note: in a forward, after a cursor and messages
# that fit, a note tag past 1 (none, a text) is malformed, whatever follows
# EXCLUDES: an unknown note tag read as no note or as a note
law worker_ffi_unknown_note:
  for +c: Nat
  for +ms: List<&2, Wk.UMsg>
  for +n: Nat
  for +rest: String
  for h: {Bool.and(LawsBase.wire_fits(c), wk_umsgs_fit(ms)) == True{} : Bool}
  {FWk.ffi(Wr.put_nat(1n, Wr.put_nat(c, wk_spell_umsgs(ms, Wr.put_nat(2n+n, rest))))) == Wr.err("worker: malformed request") : String}

# LAW worker_ffi_st_reads_spelled: the state reader reads every state the
# grammar spells back as itself, the rest untouched
# EXCLUDES: a reader (and its own writer) that swap the fields or tags of a
#   state both ways, so Rust and the laws read one state apart
law worker_ffi_st_reads_spelled:
  for +x: Wk.St
  for +rest: String
  for h: {wk_st_fits(x) == True{} : Bool}
  {FWk.get_st(wk_spell_st(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Wk.St>}

# LAW worker_reply_verdict_unambiguous: the reply grammar spells every
# verdict apart: a reader of the grammar in Rust's order (wk_read_verdict)
# reads each verdict that fits the wire back as itself, the rest untouched
# EXCLUDES: a reply grammar (wk_spell_verdict, the spelling
#   worker_ffi_decides pins the replies to) that spells two verdicts alike
#   (a hold read as a go) or loses the released ids
law worker_reply_verdict_unambiguous:
  for +x: Wk.Verdict
  for +rest: String
  for h: {wk_verdict_fits(x) == True{} : Bool}
  {wk_read_verdict(wk_spell_verdict(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Wk.Verdict>}

# LAW worker_reply_pick_unambiguous: the reply grammar spells every pick
# apart: a reader of the grammar in Rust's order (wk_read_pick) reads each
# pick that fits the wire back as itself, the rest untouched
# EXCLUDES: a reply grammar (wk_spell_pick) that swaps the cursor and the
#   seqs, or loses the text
law worker_reply_pick_unambiguous:
  for +x: Wk.Pick
  for +rest: String
  for h: {wk_pick_fits(x) == True{} : Bool}
  {wk_read_pick(wk_spell_pick(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Wk.Pick>}

# LAW worker_ffi_example: anchor: exact strings in and out of the entry: a
# pause of a new tree; a report kept by a paused tree that holds 5 with 1
# tool in flight; the user's message releasing it; a forward past cursor 1
# with a note; request tag 2, mode tag 2, parked tag 2, event tag 6 and
# note tag 2 are malformed; input left over is refused
law worker_ffi_example:
  {[FWk.ffi("0,0,0,0,0,0,"), FWk.ffi("0,1,1,5,1,7,1,4,9,F"), FWk.ffi("0,1,1,5,1,7,1,4,9,T"), FWk.ffi("1,1,2,1,2,hi3,2,yo1,1,n"), FWk.ffi("2,"), FWk.ffi("0,2,"), FWk.ffi("0,0,2,"), FWk.ffi("0,0,0,0,0,6,"), FWk.ffi("1,0,0,2,"), FWk.ffi("0,0,0,0,0,0,x")] == ["1,0,0,0,5,", "1,1,5,2,7,9,1,3,", "0,1,5,0,1,2,2,7,9,", "3,1,3,22,yo\n\n[note from main] n", "E worker: malformed request", "E worker: malformed request", "E worker: malformed request", "E worker: malformed request", "E worker: malformed request", "E worker: input left over"] : List<&2, String>}

# LAW worker_ffi_premises_witness: witness: requests and replies that fit
# exist, and so does a malformed input
# EXCLUDES: a vacuous entry law whose premise no request meets
law worker_ffi_premises_witness:
  {Bool.and(wk_req_fits(FWk.Step{wk_init(), Wk.Pause{}}), Bool.and(wk_req_fits(FWk.Forward{0n, [], None{}}), Bool.and(wk_st_fits(wk_init()), Bool.and(wk_verdict_fits(Wk.Go{}), wk_pick_fits(Wk.Pick{0n, [], ""}))))) == True{} : Bool} & {FWk.ffi("") == Wr.err("worker: malformed request") : String}

# LAW resume_running_noop: a resume of a running tree releases nothing and
# changes nothing
# EXCLUDES: a second resume that releases (or drops) messages again
law resume_running_noop:
  for +p: Maybe<&2, Nat>
  for +k: List<&2, Nat>
  for +n: Nat
  {Wk.step(Wk.St{Wk.Run{}, p, k, n}, Wk.Resume{}) == (Wk.St{Wk.Run{}, p, k, n}, Wk.Release{Nil{}}) : Wk.St & Wk.Verdict}
