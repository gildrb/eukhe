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
#   R1 a pause cancels nothing: Pause, Resume and a message leave the tool
#      calls in flight; only a tool call's end and the run's end lower the
#      count, a tool call's start raises it
#                     pause_never_cancels, pause_only_done_lowers
#   R2 while paused, every boundary (model request, tool call, child
#      spawn) holds and is parked; nothing starts until a Resume or a
#      waking message
#                     paused_starts_nothing, pause_then_holds
#   R3 a Resume, or a waking message, runs the tree again: the parked
#      boundary goes on, the kept messages are released in arrival order
#      (a waking message last)
#                     resume_continues, resume_releases_kept,
#                     waking_msg_resumes, resume_running_noop
#   R4 a message that arrives while paused and does not wake is kept; while
#      running a message passes; over any history every message that
#      arrived while paused is released or still kept, once, in order
#                     paused_msg_kept, running_passes, kept_once_in_order
#   R5 a running boundary goes (a tool call counts in flight); a tool
#      call's end lowers the count, never below none; the run's end
#      clears the parked boundary and the count and keeps the mode
#                     running_tool_counts, running_gate_goes,
#                     done_settles, end_clears, pause_acks
#   R6 the forward pick hands on every message past the cursor, in list
#      order, its text verbatim (joined by a blank line, then main's note),
#      moves the cursor to the largest seq handed on (never back), and a
#      second pick never hands on a seq again
#                     forward_all_new, forward_verbatim,
#                     forward_cursor_exact, forward_cursor_monotone,
#                     forward_once, forward_example
#   R7 the entry answers every request Rust spells with the spelling of
#      the model's answer, refuses input left over and any input that is
#      not a spelled request, and its reply readers read the reply grammar
#                     worker_ffi_* (the entry laws below)

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

# k, then x
def wk_snoc(k: List<&2, Nat>, x: Nat) -> List<&2, Nat>:
  match k:
    case Nil{}:
      [x]
    case Con{y, r}:
      y <> wk_snoc(r, x)

# n less one, none below 0
def wk_less(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# the count after a boundary of this kind starts: one more for a tool call
# (kind 1)
def wk_started.is(tool: Bool, n: Nat) -> Nat:
  match tool:
    case True{}:
      1n+n
    case False{}:
      n

def wk_started(kind: Nat, n: Nat) -> Nat:
  wk_started.is(Nat.is_eq(kind, 1n), n)

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

# Laws: the pause, event by event
# -------------------------------

# LAW pause_acks: a pause pauses the tree in any state and touches nothing else
# EXCLUDES: a pause that cancels tool calls, drops the parked boundary or
#   the kept messages, or answers anything but Ack
law pause_acks:
  for +m: Wk.Mode
  for +p: Maybe<&2, Nat>
  for +k: List<&2, Nat>
  for +n: Nat
  {Wk.step(Wk.St{m, p, k, n}, Wk.Pause{}) == (Wk.St{Wk.Paused{}, p, k, n}, Wk.Ack{}) : Wk.St & Wk.Verdict}

# LAW resume_releases_kept: a resume runs a paused tree and releases every
# kept message, in order; the parked boundary stays (its next gate goes)
# EXCLUDES: kept messages lost, reordered or released twice, a resume that
#   leaves the tree paused or forgets the parked boundary
law resume_releases_kept:
  for +p: Maybe<&2, Nat>
  for +k: List<&2, Nat>
  for +n: Nat
  {Wk.step(Wk.St{Wk.Paused{}, p, k, n}, Wk.Resume{}) == (Wk.St{Wk.Run{}, p, Nil{}, n}, Wk.Release{k}) : Wk.St & Wk.Verdict}

# LAW resume_running_noop: a resume of a running tree releases nothing and
# changes nothing
# EXCLUDES: a second resume that releases (or drops) messages again
law resume_running_noop:
  for +p: Maybe<&2, Nat>
  for +k: List<&2, Nat>
  for +n: Nat
  {Wk.step(Wk.St{Wk.Run{}, p, k, n}, Wk.Resume{}) == (Wk.St{Wk.Run{}, p, k, n}, Wk.Release{Nil{}}) : Wk.St & Wk.Verdict}

# LAW running_tool_counts: a running tree starts a tool call (kind 1): it
# goes, counts one more in flight and parks nothing
# EXCLUDES: a tool call not counted (a later Done would then go below the
#   real count), a stale parked boundary kept
law running_tool_counts:
  for +p: Maybe<&2, Nat>
  for +k: List<&2, Nat>
  for +n: Nat
  for +id: Nat
  {Wk.step(Wk.St{Wk.Run{}, p, k, n}, Wk.Gate{1n, id}) == (Wk.St{Wk.Run{}, None{}, k, 1n+n}, Wk.Go{}) : Wk.St & Wk.Verdict}

# LAW running_gate_goes: a running tree starts any other boundary (a model
# request, a child spawn, any kind but 1): it goes, the count stays
# EXCLUDES: a request or spawn counted as a tool call, a running boundary
#   that holds
law running_gate_goes:
  for +p: Maybe<&2, Nat>
  for +k: List<&2, Nat>
  for +n: Nat
  for +kind: Nat
  for +id: Nat
  for other: {Nat.is_eq(kind, 1n) == False{} : Bool}
  {Wk.step(Wk.St{Wk.Run{}, p, k, n}, Wk.Gate{kind, id}) == (Wk.St{Wk.Run{}, None{}, k, n}, Wk.Go{}) : Wk.St & Wk.Verdict}

# LAW paused_starts_nothing: in a paused tree every boundary, of any kind,
# holds: it is parked, the count stays
# EXCLUDES: a tool call, model request or child spawn started while paused
#   (or counted in flight), a boundary held but not parked
law paused_starts_nothing:
  for +p: Maybe<&2, Nat>
  for +k: List<&2, Nat>
  for +n: Nat
  for +kind: Nat
  for +id: Nat
  {Wk.step(Wk.St{Wk.Paused{}, p, k, n}, Wk.Gate{kind, id}) == (Wk.St{Wk.Paused{}, Some{id}, k, n}, Wk.Hold{}) : Wk.St & Wk.Verdict}

# LAW done_settles: a tool call's end lowers the count by one, never below
# none, and touches nothing else (a paused tree stays paused)
# EXCLUDES: a count that wraps or goes below none, an end that resumes or
#   pauses the tree
law done_settles:
  for +m: Wk.Mode
  for +p: Maybe<&2, Nat>
  for +k: List<&2, Nat>
  for +n: Nat
  {Wk.step(Wk.St{m, p, k, n}, Wk.ToolDone{}) == (Wk.St{m, p, k, wk_less(n)}, Wk.Ack{}) : Wk.St & Wk.Verdict}

# LAW running_passes: in a running tree a message passes and the state stays
# EXCLUDES: a message kept or held while running
law running_passes:
  for +p: Maybe<&2, Nat>
  for +k: List<&2, Nat>
  for +n: Nat
  for +id: Nat
  for +w: Bool
  {Wk.step(Wk.St{Wk.Run{}, p, k, n}, Wk.Msg{id, w}) == (Wk.St{Wk.Run{}, p, k, n}, Wk.Pass{}) : Wk.St & Wk.Verdict}

# LAW waking_msg_resumes: a waking message (the user's, or a forward from
# main) runs a paused tree: the kept messages are released in order, the
# waking one last
# EXCLUDES: a user message that waits behind the pause, a waking message
#   released before the ones kept earlier, a kept message lost
law waking_msg_resumes:
  for +p: Maybe<&2, Nat>
  for +k: List<&2, Nat>
  for +n: Nat
  for +id: Nat
  {Wk.step(Wk.St{Wk.Paused{}, p, k, n}, Wk.Msg{id, True{}}) == (Wk.St{Wk.Run{}, p, Nil{}, n}, Wk.Release{wk_snoc(k, id)}) : Wk.St & Wk.Verdict}

# LAW paused_msg_kept: a message that does not wake (a report, a note) is
# kept by a paused tree, after the ones kept before; the tree stays paused
# EXCLUDES: a report that wakes the tree, a kept message put first or lost
law paused_msg_kept:
  for +p: Maybe<&2, Nat>
  for +k: List<&2, Nat>
  for +n: Nat
  for +id: Nat
  {Wk.step(Wk.St{Wk.Paused{}, p, k, n}, Wk.Msg{id, False{}}) == (Wk.St{Wk.Paused{}, p, wk_snoc(k, id), n}, Wk.Kept{}) : Wk.St & Wk.Verdict}

# LAW end_clears: the run's end clears the parked boundary and the count;
# the mode and the kept messages stay (a paused tree stays paused: the next
# run's first request holds)
# EXCLUDES: a run's end that resumes the tree, drops kept messages, or
#   leaves a stale count or parked boundary for the next run
law end_clears:
  for +m: Wk.Mode
  for +p: Maybe<&2, Nat>
  for +k: List<&2, Nat>
  for +n: Nat
  {Wk.step(Wk.St{m, p, k, n}, Wk.End{}) == (Wk.St{m, None{}, k, 0n}, Wk.Ack{}) : Wk.St & Wk.Verdict}

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

# LAW resume_continues: a paused tree that held a boundary, once resumed,
# lets that same boundary go: the run continues where it parked
# EXCLUDES: a resume after which the parked boundary still holds, is
#   skipped, or is counted twice
law resume_continues:
  for +p: Maybe<&2, Nat>
  for +k: List<&2, Nat>
  for +n: Nat
  for +kind: Nat
  for +id: Nat
  {Wk.step(wk_state(Wk.step(wk_state(Wk.step(Wk.St{Wk.Paused{}, p, k, n}, Wk.Gate{kind, id})), Wk.Resume{})), Wk.Gate{kind, id}) == (Wk.St{Wk.Run{}, None{}, Nil{}, wk_started(kind, n)}, Wk.Go{}) : Wk.St & Wk.Verdict}

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
# EXCLUDES: a model whose answers differ from the documented session
law pause_example:
  {wk_answers([Wk.Gate{1n, 1n}, Wk.Pause{}, Wk.Gate{0n, 2n}, Wk.Msg{7n, False{}}, Wk.ToolDone{}, Wk.Msg{8n, True{}}, Wk.Gate{0n, 2n}], wk_init()) == [Wk.Go{}, Wk.Ack{}, Wk.Hold{}, Wk.Kept{}, Wk.Ack{}, Wk.Release{[7n, 8n]}, Wk.Go{}] : List<&2, Wk.Verdict>}

# Spec helpers: the forward pick
# ------------------------------

def fw_new.put(keep: Bool, m: Wk.UMsg, r: List<&2, Wk.UMsg>) -> List<&2, Wk.UMsg>:
  match keep:
    case True{}:
      m <> r
    case False{}:
      r

# the messages of ms whose seq is greater than the cursor c, in list order
def fw_new(+c: Nat, ms: List<&2, Wk.UMsg>) -> List<&2, Wk.UMsg>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{Wk.UMsg{+q, t}, r}:
      fw_new.put(Nat.is_gt(q, c), Wk.UMsg{q, t}, fw_new(c, r))

def fw_seqs(ms: List<&2, Wk.UMsg>) -> List<&2, Nat>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{Wk.UMsg{q, t}, r}:
      q <> fw_seqs(r)

def fw_texts(ms: List<&2, Wk.UMsg>) -> List<&2, String>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{Wk.UMsg{q, t}, r}:
      t <> fw_texts(r)

def fw_body.note(ts: List<&2, String>, n: String) -> String:
  match ts:
    case Nil{}:
      String.append("[note from main] ", n)
    case Con{t, r}:
      String.append(String.join(t <> r, "\n\n"), String.append("\n\n[note from main] ", n))

# the texts ts joined by a blank line (Base String.join), then main's note:
# after a blank line when a text comes first, alone when none does
def fw_body(ts: List<&2, String>, note: Maybe<&2, String>) -> String:
  match note:
    case None{}:
      String.join(ts, "\n\n")
    case Some{n}:
      fw_body.note(ts, n)

# the largest of the cursor c and the seqs ps (Base Nat.max)
def fw_cursor(ps: List<&2, Nat>, c: Nat) -> Nat:
  match ps:
    case Nil{}:
      c
    case Con{x, r}:
      fw_cursor(r, Nat.max(c, x))

def fw_cursor_of(x: Wk.Pick) -> Nat:
  match x:
    case Wk.Pick{c, ps, b}:
      c

def fw_picked_of(x: Wk.Pick) -> List<&2, Nat>:
  match x:
    case Wk.Pick{c, ps, b}:
      ps

def fw_body_of(x: Wk.Pick) -> String:
  match x:
    case Wk.Pick{c, ps, b}:
      b

# x is one of ys
def fw_in(+x: Nat, ys: List<&2, Nat>) -> Bool:
  match ys:
    case Nil{}:
      False{}
    case Con{y, r}:
      Bool.or(Nat.is_eq(x, y), fw_in(x, r))

# no x of xs is one of ys
def fw_disjoint(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, r}:
      Bool.and(Bool.not(fw_in(x, ys)), fw_disjoint(r, ys))

# Laws: the forward pick
# ----------------------

# LAW forward_all_new: the pick hands on the seq of every message past the
# cursor, in list order, and no other
# EXCLUDES: a message past the cursor skipped, one at or before it handed
#   on again, the seqs reordered (sorted, reversed) or deduplicated
law forward_all_new:
  for +c: Nat
  for +ms: List<&2, Wk.UMsg>
  for +note: Maybe<&2, String>
  {fw_picked_of(Wk.pick(c, ms, note)) == fw_seqs(fw_new(c, ms)) : List<&2, Nat>}

# LAW forward_verbatim: the text handed on is the texts of the messages past
# the cursor, unchanged, joined by a blank line, then main's note after
# "[note from main] " (after a blank line when a text comes first)
# EXCLUDES: a text trimmed, changed, dropped or reordered, another joint,
#   a note lost, placed first, or an empty note dropped
law forward_verbatim:
  for +c: Nat
  for +ms: List<&2, Wk.UMsg>
  for +note: Maybe<&2, String>
  {fw_body_of(Wk.pick(c, ms, note)) == fw_body(fw_texts(fw_new(c, ms)), note) : String}

# LAW forward_cursor_exact: the new cursor is the largest of the cursor and
# the seqs handed on (the largest seq handed on, or the cursor when none is)
# EXCLUDES: a cursor moved to the last seq instead of the largest, past a
#   message not handed on, or left behind
law forward_cursor_exact:
  for +c: Nat
  for +ms: List<&2, Wk.UMsg>
  for +note: Maybe<&2, String>
  {fw_cursor_of(Wk.pick(c, ms, note)) == fw_cursor(fw_seqs(fw_new(c, ms)), c) : Nat}

# LAW forward_cursor_monotone: the new cursor is never below the old one
# EXCLUDES: a cursor that moves back and hands messages on twice
law forward_cursor_monotone:
  for +c: Nat
  for +ms: List<&2, Wk.UMsg>
  for +note: Maybe<&2, String>
  {Nat.is_le(c, fw_cursor_of(Wk.pick(c, ms, note))) == True{} : Bool}

# LAW forward_once: a second pick from the new cursor, over any messages
# and note, never hands on a seq the first pick handed on
# EXCLUDES: a user message forwarded twice
law forward_once:
  for +c: Nat
  for +ms: List<&2, Wk.UMsg>
  for +note: Maybe<&2, String>
  for +ms2: List<&2, Wk.UMsg>
  for +note2: Maybe<&2, String>
  {fw_disjoint(fw_picked_of(Wk.pick(c, ms, note)), fw_picked_of(Wk.pick(fw_cursor_of(Wk.pick(c, ms, note)), ms2, note2))) == True{} : Bool}

# LAW forward_example: anchor: past cursor 1, messages 5 and 3 (not 1) are
# handed on, cursor 5; an empty note still opens with its head; no message
# and no note hand on nothing
# EXCLUDES: a pick that differs from the documented texts
law forward_example:
  {[Wk.pick(1n, [Wk.UMsg{1n, "a"}, Wk.UMsg{5n, " b "}, Wk.UMsg{3n, "c\n"}], Some{"n"}), Wk.pick(4n, [Wk.UMsg{2n, "x"}], Some{""}), Wk.pick(0n, [], None{})] == [Wk.Pick{5n, [5n, 3n], " b \n\nc\n\n\n[note from main] n"}, Wk.Pick{4n, [], "[note from main] "}, Wk.Pick{0n, [], ""}] : List<&2, Wk.Pick>}

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

# LAW worker_ffi_unknown_verdict: a verdict reply tag past 5 reads as no
# reply, whatever follows
# EXCLUDES: a reply grammar where an unknown tag reads as a verdict (two
#   spellings of one answer, a reply Rust and the laws read apart)
law worker_ffi_unknown_verdict:
  for +n: Nat
  for +rest: String
  {FWk.get_verdict(Wr.put_nat(6n+n, rest)) == Wr.Bad{} : Wr.Dec<Wk.Verdict>}

# LAW worker_ffi_unknown_reply_mode: a state whose mode tag is past 1 reads
# as no state, whatever follows
# EXCLUDES: a state reader that reads an unknown mode as run or paused
law worker_ffi_unknown_reply_mode:
  for +n: Nat
  for +rest: String
  {FWk.get_st(Wr.put_nat(2n+n, rest)) == Wr.Bad{} : Wr.Dec<Wk.St>}

# LAW worker_ffi_unknown_reply_parked: a state whose parked tag is past 1
# reads as no state, whatever follows
# EXCLUDES: a state reader that reads an unknown parked tag as none or an id
law worker_ffi_unknown_reply_parked:
  for +m: Wk.Mode
  for +n: Nat
  for +rest: String
  {FWk.get_st(wk_spell_mode(m, Wr.put_nat(2n+n, rest))) == Wr.Bad{} : Wr.Dec<Wk.St>}

# LAW worker_ffi_st_reads_spelled: the state reader reads every state the
# grammar spells back as itself, the rest untouched
# EXCLUDES: a reader (and its own writer) that swap the fields or tags of a
#   state both ways, so Rust and the laws read one state apart
law worker_ffi_st_reads_spelled:
  for +x: Wk.St
  for +rest: String
  for h: {wk_st_fits(x) == True{} : Bool}
  {FWk.get_st(wk_spell_st(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Wk.St>}

# LAW worker_ffi_verdict_reads_spelled: the verdict reader reads every
# verdict the grammar spells back as itself, the rest untouched
# EXCLUDES: a reader that swaps verdict tags (a hold read as a go) or loses
#   the released ids
law worker_ffi_verdict_reads_spelled:
  for +x: Wk.Verdict
  for +rest: String
  for h: {wk_verdict_fits(x) == True{} : Bool}
  {FWk.get_verdict(wk_spell_verdict(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Wk.Verdict>}

# LAW worker_ffi_pick_reads_spelled: the pick reader reads every pick the
# grammar spells back as itself, the rest untouched
# EXCLUDES: a reader that swaps the cursor and the seqs, or loses the text
law worker_ffi_pick_reads_spelled:
  for +x: Wk.Pick
  for +rest: String
  for h: {wk_pick_fits(x) == True{} : Bool}
  {FWk.get_pick(wk_spell_pick(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Wk.Pick>}

# LAW worker_ffi_example: anchor: the exact strings Rust sends and reads: a
# pause of a new tree; a report kept by a paused tree that holds 5 with 1
# tool in flight; the user's message releasing it; a forward past cursor 1
# with a note; request tag 2, mode tag 2, parked tag 2, event tag 6 and
# note tag 2 are malformed
law worker_ffi_example:
  {[FWk.ffi("0,0,0,0,0,0,"), FWk.ffi("0,1,1,5,1,7,1,4,9,F"), FWk.ffi("0,1,1,5,1,7,1,4,9,T"), FWk.ffi("1,1,2,1,2,hi3,2,yo1,1,n"), FWk.ffi("2,"), FWk.ffi("0,2,"), FWk.ffi("0,0,2,"), FWk.ffi("0,0,0,0,0,6,"), FWk.ffi("1,0,0,2,"), FWk.ffi("0,0,0,0,0,0,x")] == ["1,0,0,0,5,", "1,1,5,2,7,9,1,3,", "0,1,5,0,1,2,2,7,9,", "3,1,3,22,yo\n\n[note from main] n", "E worker: malformed request", "E worker: malformed request", "E worker: malformed request", "E worker: malformed request", "E worker: malformed request", "E worker: input left over"] : List<&2, String>}

# LAW worker_ffi_premises_witness: witness: requests and replies that fit
# exist, and so does a malformed input
# EXCLUDES: a vacuous entry law whose premise no request meets
law worker_ffi_premises_witness:
  {Bool.and(wk_req_fits(FWk.Step{wk_init(), Wk.Pause{}}), Bool.and(wk_req_fits(FWk.Forward{0n, [], None{}}), Bool.and(wk_st_fits(wk_init()), Bool.and(wk_verdict_fits(Wk.Go{}), wk_pick_fits(Wk.Pick{0n, [], ""}))))) == True{} : Bool} & {FWk.ffi("") == Wr.err("worker: malformed request") : String}
