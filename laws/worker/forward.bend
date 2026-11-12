# eukhe: the laws of area worker, section forward: main hands the worker
# the user's words (bend/worker.bend `pick`, entry bend/ffi_worker.bend).
# Requirement R6 of laws/worker.bend:
#   R6 the forward pick hands on every message past the cursor, in list
#      order, its text verbatim (joined by a blank line, then main's note),
#      moves the cursor to the largest seq handed on (never back), and a
#      second pick never hands on a seq again
#                     forward_picks_split, forward_picks_one (which seqs,
#                     in which order), forward_verbatim (the text),
#                     forward_cursor_largest, forward_cursor_monotone (the
#                     cursor), forward_once (never twice)
# Anchor (not coverage): forward_example.

import Base
import ../../bend/worker.bend as Wk

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

# the seqs one message with seq q hands on: q when it is past the cursor,
# none when it is not
def fw_one(past: Bool, q: Nat) -> List<&2, Nat>:
  match past:
    case True{}:
      [q]
    case False{}:
      Nil{}

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

# every one of xs is at most b
def fw_all_le(xs: List<&2, Nat>, +b: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, r}:
      Bool.and(Nat.is_le(x, b), fw_all_le(r, b))

# Laws: the forward pick
# ----------------------

# LAW forward_picks_split: the seqs handed on from two runs of messages,
# one after the other, are the seqs handed on from the first run, then
# those from the second, whatever the note (with forward_picks_one: the
# seq of every message past the cursor, in list order, and no other)
# EXCLUDES: seqs reordered (sorted, reversed) or deduplicated, a message
#   handed on or skipped because of its neighbours or of the note
law forward_picks_split:
  for +c: Nat
  for +ms: List<&2, Wk.UMsg>
  for +ns: List<&2, Wk.UMsg>
  for +note: Maybe<&2, String>
  {fw_picked_of(Wk.pick(c, List.append(&2, Wk.UMsg, ms, ns), note)) == List.append(&2, Nat, fw_picked_of(Wk.pick(c, ms, None{})), fw_picked_of(Wk.pick(c, ns, None{}))) : List<&2, Nat>}

# LAW forward_picks_one: one message, whatever its text and the note, is
# handed on (its seq) exactly when its seq is past the cursor (c < q)
# EXCLUDES: a message past the cursor skipped, one at or before it handed
#   on again (an off-by-one at the cursor), another seq handed on
law forward_picks_one:
  for +c: Nat
  for +q: Nat
  for +t: String
  for +note: Maybe<&2, String>
  {fw_picked_of(Wk.pick(c, [Wk.UMsg{q, t}], note)) == fw_one(Nat.is_lt(c, q), q) : List<&2, Nat>}

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

# LAW forward_cursor_largest: the new cursor is the largest of the old
# cursor and the seqs handed on: none of them is above it, and it is one
# of them (the old cursor when nothing is handed on)
# EXCLUDES: a cursor moved to the last seq instead of the largest, past
#   every message handed on, or to a seq never handed on
law forward_cursor_largest:
  for +c: Nat
  for +ms: List<&2, Wk.UMsg>
  for +note: Maybe<&2, String>
  {Bool.and(fw_all_le(c <> fw_picked_of(Wk.pick(c, ms, note)), fw_cursor_of(Wk.pick(c, ms, note))), fw_in(fw_cursor_of(Wk.pick(c, ms, note)), c <> fw_picked_of(Wk.pick(c, ms, note)))) == True{} : Bool}

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
# handed on, cursor 5 (the Rust test the_core_picks_what_to_forward,
# crates/eukhe-bend/src/rules/worker.rs:315-325); an empty note still opens
# with its head; no message and no note hand on nothing
# EXCLUDES: a pick that differs from these texts
law forward_example:
  {[Wk.pick(1n, [Wk.UMsg{1n, "a"}, Wk.UMsg{5n, " b "}, Wk.UMsg{3n, "c\n"}], Some{"n"}), Wk.pick(4n, [Wk.UMsg{2n, "x"}], Some{""}), Wk.pick(0n, [], None{})] == [Wk.Pick{5n, [5n, 3n], " b \n\nc\n\n\n[note from main] n"}, Wk.Pick{4n, [], "[note from main] "}, Wk.Pick{0n, [], ""}] : List<&2, Wk.Pick>}
