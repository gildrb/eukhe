# eukhe: the laws of area tree

import Base
import ../bend/director.bend as Dr
import ../bend/ffi_tree.bend as Ft
import ../bend/tree.bend as Tr
import ../bend/wire.bend as Wr
import ../spec/durable/tree.bend as TS
import ./base.bend as LawsBase

# Requirements
# ------------
# The tags the laws below answer to, each with its source. S1, T1-T7 and
# S5 keep their earlier names; R1-R5 are stated in the Rust tree, A1-A2
# are inferred.
#
# S1  the session tree (bend/tree.bend:1-20, crates/eukhe-durable/src/
#     tree/mod.rs:10-16): one tree holds the state of a session, the
#     journal is its records, a replay of the journal makes the tree, a
#     replay of a prefix is a snapshot; its rules are T1-T7
# T1-T7  spec/durable/tree.bend:5-26: T1 a valid tree, T2 a put, T3 a
#     delete, T4 a rewind, T5 a journal's tree, T6 the rewind from a to
#     b, T7 the answer to a record and the work of a plan
# S5  the Director stack lives in the tree and a rewind restores it
#     (bend/director.bend; section S5 below)
# R1  a question (a rewind plan, a snapshot) leaves the core as it was:
#     the journal asks it through &self (crates/eukhe-durable/src/tree/
#     journal.rs:79-83)
# R2  the snapshot after the first n records is their replay; all the
#     records when n is past their count (journal.rs:184-185, 209-211)
# R3  the rewind plan from the live tree to the snapshot after the first
#     n records: a stop for each node the snapshot does not have, then a
#     start or a restore for each node of the snapshot the live tree does
#     not have the same, in id order (journal.rs:195-199); a start for a
#     node that is new, a restore for one that changes (mod.rs:100-107)
# R4  the entry (bend/ffi_tree.bend:1-19): an open reads the halves, a
#     list of Nats, and answers nothing; a step reads one ask and answers
#     the core's answer; a malformed input or one with input left over
#     answers the error form and keeps the core; a malformed open opens the
#     refused state, which answers every step with the error form
# R5  the bytes Rust writes and reads (journal.rs:47-58 ops, 128-142
#     records, 209-217 questions, 257-298 answers), anchored by the Rust
#     test the_live_tree_follows_the_core (journal.rs:326-390)
# A1  a client that holds the snapshot after n records and replays the
#     records after it holds the live tree
# A2  every halves: Rust opens the core with 2^46, ..., 2, 1
#     (journal.rs:17-22); the laws hold for any halves
#
# Coverage (requirement laws; *_example and *_exists laws are anchors and
# witnesses, never coverage):
#   T1 tree_apply_sound, tree_replay_sound; T2 tree_put_sets,
#   tree_put_keeps_others; T3 tree_delete_removes, tree_delete_only_below,
#   tree_delete_within; T4 tree_rewind_reaches; T6 tree_rewind_reaches,
#   tree_rewind_still, tree_rewind_minimal; T1-T5 tree_replay_spec; T5-T7
#   tree_core_tree, tree_core_answer, tree_ffi_step_spec; R1
#   tree_core_questions_keep; R2 tree_core_snap; R3 tree_core_plan; A1
#   tree_snapshot_catches_up; R4 tree_ffi_open, tree_ffi_open_left_over,
#   tree_ffi_open_reads_only_halves, tree_ffi_open_malformed_unless_halves,
#   tree_ffi_refused_stays, tree_ffi_ask_round_trip and the tree_ffi_*
#   laws of section "The spelled entry"; R5 the same spelled laws; S5
#   dir_encode_sound, dir_rewind_restores; A2: every law on the core is for
#   all halves hs.

# (S1) The session tree
# ---------------------
# the model in bend/tree.bend. One tree holds the
# state of a session; the journal is its list of records. Every record
# is free: any put (valid or not), any delete, any rewind ops.

# LAW tree_apply_sound: a record keeps a valid tree valid: keys in order, and every node
# under the root or under a node (no orphan, no cycle)
law tree_apply_sound:
  for +t: List<&2, Tr.Ent>
  for good: {Tr.sound(t) == True{} : Bool}
  for r: Tr.Rec
  {Tr.sound(Tr.apply(t, r)) == True{} : Bool}

# LAW tree_replay_sound: so every journal makes a valid tree
law tree_replay_sound:
  for rs: List<&2, Tr.Rec>
  {Tr.sound(Tr.replay(rs)) == True{} : Bool}

# LAW tree_rewind_reaches: a rewind with diff(current, target) makes the target, exactly
law tree_rewind_reaches:
  for +a: List<&2, Tr.Ent>
  for +b: List<&2, Tr.Ent>
  for ga: {Tr.sound(a) == True{} : Bool}
  for gb: {Tr.sound(b) == True{} : Bool}
  {Tr.apply(a, Tr.Rewind{Tr.diff(a, b)}) == b : List<&2, Tr.Ent>}

# LAW tree_rewind_still: a rewind to the current tree has no ops
law tree_rewind_still:
  for +a: List<&2, Tr.Ent>
  for ga: {Tr.sorted(a) == True{} : Bool}
  {Tr.diff(a, a) == Nil{} : List<&2, Tr.Op>}

# LAW tree_rewind_minimal: every op of a rewind is on a node that differs between the
# current tree and the target: a rewind starts, stops or restores only
# what changed
law tree_rewind_minimal:
  for +a: List<&2, Tr.Ent>
  for +b: List<&2, Tr.Ent>
  for ga: {Tr.sorted(a) == True{} : Bool}
  for gb: {Tr.sorted(b) == True{} : Bool}
  {Tr.changed(a, b, Tr.diff(a, b)) == True{} : Bool}

# LAW tree_delete_removes: a delete removes its node
law tree_delete_removes:
  for +t: List<&2, Tr.Ent>
  for good: {Tr.sound(t) == True{} : Bool}
  for +x: Nat
  {Tr.has(Tr.apply(t, Tr.Do{Tr.Del{x}}), x) == False{} : Bool}

# LAW tree_delete_only_below: a delete removes a node only when it is the deleted node or its
# parent is removed: it removes the subtree, nothing else
law tree_delete_only_below:
  for +t: List<&2, Tr.Ent>
  for good: {Tr.sound(t) == True{} : Bool}
  for +x: Nat
  {Tr.only_below(t, x, Tr.apply(t, Tr.Do{Tr.Del{x}})) == True{} : Bool}

# LAW tree_delete_within: a delete changes no node it keeps
law tree_delete_within:
  for +t: List<&2, Tr.Ent>
  for good: {Tr.sound(t) == True{} : Bool}
  for +x: Nat
  {Tr.within(Tr.apply(t, Tr.Do{Tr.Del{x}}), t) == True{} : Bool}

# LAW tree_put_sets: a put under the root or a node sets its node
law tree_put_sets:
  for +t: List<&2, Tr.Ent>
  for good: {Tr.sound(t) == True{} : Bool}
  for +k: Nat
  for +p: Nat
  for +v: Nat
  for fits: {Tr.ok(t, k, p) == True{} : Bool}
  {Tr.get(Tr.apply(t, Tr.Do{Tr.Put{k, p, v}}), k) == Some{Tr.Ent{k, p, v}} : Maybe<&2, Tr.Ent>}

# LAW tree_put_keeps_others: a put changes no other node
law tree_put_keeps_others:
  for +t: List<&2, Tr.Ent>
  for good: {Tr.sound(t) == True{} : Bool}
  for +k: Nat
  for +p: Nat
  for +v: Nat
  for +x: Nat
  for other: {Nat.is_eq(x, k) == False{} : Bool}
  {Tr.get(Tr.apply(t, Tr.Do{Tr.Put{k, p, v}}), x) == Tr.get(t, x) : Maybe<&2, Tr.Ent>}

# The compiled core: the Rust tree runs the stepper of bend/tree.bend
# (`Tr.core.step`, its state a key map and the journal) through the entry
# bend/ffi_tree.bend (laws tree_ffi_*, after section wire). Every journal
# is free: any records, valid or not; the halves hs that place the map's
# splits are free too (the Rust tree opens with 2^46, ..., 2, 1).

# the keys of the nodes of a that b does not hold, in key order
def tree.lost.at(held: Bool, k: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match held:
    case True{}:
      rest
    case False{}:
      k <> rest

def tree.lost(a: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>) -> List<&2, Nat>:
  match a:
    case Nil{}:
      Nil{}
    case +e <> rest:
      tree.lost.at(Tr.has(b, Tr.Ent.k(e)), Tr.Ent.k(e), tree.lost(rest, b))

def tree.took(good: Bool) -> Tr.Ans:
  match good:
    case True{}:
      Tr.Took{}
    case False{}:
      Tr.Kept{}

# the model's answer to record r on tree t: a put or a rewind is taken
# when the tree accepts it, else kept; a delete of the root is kept; a
# delete of any other key cuts the keys of the nodes it removes
def tree.answer(+t: List<&2, Tr.Ent>, r: Tr.Rec) -> Tr.Ans:
  match r:
    case Tr.Do{o}:
      match o:
        case Tr.Put{+k, +p, v}:
          tree.took(Tr.ok(t, k, p))
        case Tr.Del{x}:
          match x:
            case 0n:
              Tr.Kept{}
            case 1n++y:
              Tr.Cut{tree.lost(t, Tr.prune(t, 1n+y))}
    case Tr.Rewind{ops}:
      tree.took(Tr.sound(Tr.patch(ops, t)))

# R3, from the Rust doc (journal.rs:195-199, mod.rs:100-107), not from
# the code's diff and effects: the plan of a rewind from now to tgt, read
# with the spec's lookups (TS.get, TS.has, TS.same)
def tree.stop.at(held: Bool, k: Nat, rest: List<&2, Tr.Eff>) -> List<&2, Tr.Eff>:
  match held:
    case True{}:
      rest
    case False{}:
      Tr.Stop{k} <> rest

# a stop for each node of now (in key order) whose key tgt does not have
def tree.stops(now: List<&2, Tr.Ent>, +tgt: List<&2, Tr.Ent>) -> List<&2, Tr.Eff>:
  match now:
    case Nil{}:
      Nil{}
    case +e <> rest:
      tree.stop.at(TS.has(tgt, TS.key(e)), TS.key(e), tree.stops(rest, tgt))

# a node of the target that now holds the same needs nothing; one whose
# key now has changes (a restore); one whose key now lacks is new (a start)
def tree.start.at(same: Bool, held: Bool, k: Nat, rest: List<&2, Tr.Eff>) -> List<&2, Tr.Eff>:
  match same:
    case True{}:
      rest
    case False{}:
      match held:
        case True{}:
          Tr.Restore{k} <> rest
        case False{}:
          Tr.Start{k} <> rest

# a start or a restore for each node of tgt (in key order) that now does
# not have the same
def tree.starts(+now: List<&2, Tr.Ent>, tgt: List<&2, Tr.Ent>) -> List<&2, Tr.Eff>:
  match tgt:
    case Nil{}:
      Nil{}
    case +e <> rest:
      tree.start.at(TS.same(TS.get(now, TS.key(e)), e), TS.has(now, TS.key(e)), TS.key(e), tree.starts(now, rest))

# the plan: the stops, then the starts and restores
def tree.plan(+now: List<&2, Tr.Ent>, +tgt: List<&2, Tr.Ent>) -> List<&2, Tr.Eff>:
  List.append(&2, Tr.Eff, tree.stops(now, tgt), tree.starts(now, tgt))

# the core after the asks qs, in order, from s
def tree.asks(qs: List<&2, Tr.Ask>, s: Tr.St) -> Tr.St:
  match qs:
    case Nil{}:
      s
    case q <> rest:
      tree.asks(rest, Pair.fst(Tr.St, Tr.Ans, Tr.core.step(s, q)))

# the records of the asks qs, in order (the questions dropped)
def tree.notes(qs: List<&2, Tr.Ask>) -> List<&2, Tr.Rec>:
  match qs:
    case Nil{}:
      Nil{}
    case q <> rest:
      match q:
        case Tr.Note{r}:
          r <> tree.notes(rest)
        case Tr.Plan{n}:
          tree.notes(rest)
        case Tr.Snap{n}:
          tree.notes(rest)

# a client that holds the nodes of a snapshot answer and replays the
# records post on them (the model's T5 rule); nothing for another answer
def tree.catch_up(a: Tr.Ans, post: List<&2, Tr.Rec>) -> Maybe<&2, List<&2, Tr.Ent>>:
  match a:
    case Tr.Kept{}:
      None{}
    case Tr.Took{}:
      None{}
    case Tr.Cut{ks}:
      None{}
    case Tr.Effects{es}:
      None{}
    case Tr.Nodes{es}:
      Some{Tr.go(post, es)}

# LAW tree_core_tree: the core's tree after any journal is the tree the journal makes
law tree_core_tree:
  for +hs: List<&2, Nat>
  for +rs: List<&2, Tr.Rec>
  {Tr.KMap.read(Tr.St.m(Tr.core.feed(hs, rs))) == Tr.replay(rs) : List<&2, Tr.Ent>}

# LAW tree_core_answer: after any journal, the core answers a record as the model decides
# it: taken or kept, and a delete cuts exactly the nodes it removes
law tree_core_answer:
  for +hs: List<&2, Nat>
  for +rs: List<&2, Tr.Rec>
  for +r: Tr.Rec
  {Pair.snd(Tr.St, Tr.Ans, Tr.core.step(Tr.core.feed(hs, rs), Tr.Note{r})) == tree.answer(Tr.replay(rs), r) : Tr.Ans}

# LAW tree_core_questions_keep (R1): from the open with any halves, after any asks (records,
# plans and snapshots in any order), the core answers every ask as it
# does after the records alone: a question changes no later answer
# EXCLUDES: a plan or a snapshot that changes the tree or the journal
#   (so the &self questions of journal.rs would race a later record), a
#   record lost, repeated or reordered across a question
law tree_core_questions_keep:
  for +hs: List<&2, Nat>
  for +qs: List<&2, Tr.Ask>
  for +q: Tr.Ask
  {Pair.snd(Tr.St, Tr.Ans, Tr.core.step(tree.asks(qs, Tr.core.start(hs)), q)) == Pair.snd(Tr.St, Tr.Ans, Tr.core.step(Tr.core.feed(hs, tree.notes(qs)), q)) : Tr.Ans}

# LAW tree_core_plan (R3): after any journal, the core's rewind plan to the tree after
# the first n records (all of them when n is past their count) is the plan
# R3 states from the live tree (the journal's replay) and that tree
# (tree.plan): a stop for each node that tree lacks, then a start for each
# node of it the live tree lacks and a restore for each node of it the live
# tree has otherwise, each part in key order
# EXCLUDES: a lost, extra, repeated or reordered effect, a start for a node
#   that changes or a restore for a new one, a stop for a node the target
#   keeps, a plan to another prefix
law tree_core_plan:
  for +hs: List<&2, Nat>
  for +rs: List<&2, Tr.Rec>
  for +n: Nat
  {Pair.snd(Tr.St, Tr.Ans, Tr.core.step(Tr.core.feed(hs, rs), Tr.Plan{n})) == Tr.Effects{tree.plan(Tr.replay(rs), Tr.replay(List.take(&2, Tr.Rec, rs, n)))} : Tr.Ans}

# LAW tree_core_snap: the core's snapshot after the first n records is their replay
law tree_core_snap:
  for +hs: List<&2, Nat>
  for +rs: List<&2, Tr.Rec>
  for +n: Nat
  {Pair.snd(Tr.St, Tr.Ans, Tr.core.step(Tr.core.feed(hs, rs), Tr.Snap{n})) == Tr.Nodes{Tr.replay(List.take(&2, Tr.Rec, rs, n))} : Tr.Ans}

# LAW tree_snapshot_catches_up (A1): after any journal, a client that holds the core's
# snapshot after the first n records and replays the records after them
# holds the core's live tree
# EXCLUDES: a snapshot of another prefix than the one the records after it
#   continue, a snapshot that is no Nodes answer, a live tree that drifts
#   from the journal's
law tree_snapshot_catches_up:
  for +hs: List<&2, Nat>
  for +rs: List<&2, Tr.Rec>
  for +n: Nat
  {tree.catch_up(Pair.snd(Tr.St, Tr.Ans, Tr.core.step(Tr.core.feed(hs, rs), Tr.Snap{n})), List.drop(&2, Tr.Rec, rs, n)) == Some{Tr.KMap.read(Tr.St.m(Tr.core.feed(hs, rs)))} : Maybe<&2, List<&2, Tr.Ent>>}

# (S5) The Director stack
# -----------------------
# the model in bend/director.bend. Every verdict is
# free: each layer of each step says what the adversary picks.

# LAW dir_encode_sound: the stack in the tree is a valid tree
law dir_encode_sound:
  for +s: List<&2, Dr.Layer>
  {Tr.sound(Dr.encode(s)) == True{} : Bool}

# LAW dir_rewind_restores: a rewind of any valid tree to the tree of a stack restores that
# stack, exactly: a rewind removes the Directors added after the target
# and brings back the ones removed
law dir_rewind_restores:
  for +a: List<&2, Tr.Ent>
  for +s: List<&2, Dr.Layer>
  for good: {Tr.sound(a) == True{} : Bool}
  {Dr.decode(Tr.apply(a, Tr.Rewind{Tr.diff(a, Dr.encode(s))})) == s : List<&2, Dr.Layer>}

# ---- tree_ffi ----

# LAWS (S1, the session tree's entry of the compiled core): the Rust
# journal (crates/eukhe-durable/src/tree/journal.rs) drives the stepper of
# bend/ffi_tree.bend, whose state is the core of bend/tree.bend. The laws
# tree_core_* of section S1 pin the core; these pin the entry: every ask
# Rust writes reads back, a step answers the core's answer and keeps the
# core's next state, and every other input answers the error form.

# every Nat of an op fits the wire
def tree.op_fits(o: Tr.Op) -> Bool:
  match o:
    case Tr.Put{k, p, v}:
      Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(p), LawsBase.wire_fits(v)))
    case Tr.Del{k}:
      LawsBase.wire_fits(k)

def tree.ops_fit(ops: List<&2, Tr.Op>) -> Bool:
  match ops:
    case Nil{}:
      True{}
    case o <> rest:
      Bool.and(tree.op_fits(o), tree.ops_fit(rest))

# every Nat of an ask fits the wire, and so does the count of a rewind's
# ops
def tree.ask_fits(q: Tr.Ask) -> Bool:
  match q:
    case Tr.Note{r}:
      match r:
        case Tr.Do{o}:
          tree.op_fits(o)
        case Tr.Rewind{+ops}:
          Bool.and(LawsBase.wire_fits(List.length(&2, Tr.Op, ops)), tree.ops_fit(ops))
    case Tr.Plan{n}:
      LawsBase.wire_fits(n)
    case Tr.Snap{n}:
      LawsBase.wire_fits(n)

# LAW tree_ffi_ask_round_trip: an ask that fits the wire reads back, and the rest is untouched
# EXCLUDES: a field read into the wrong slot, a lost, added or reordered
#   op of a rewind, a record or an op read as another kind
law tree_ffi_ask_round_trip:
  for q: Tr.Ask
  for +rest: String
  for h: {tree.ask_fits(q) == True{} : Bool}
  {Ft.get_ask(Ft.put_ask(q, rest)) == Wr.Got{q, rest} : Wr.Dec<Tr.Ask>}

# LAW tree_ffi_open: an open with halves that fit the wire opens the empty core that
# splits at those halves, and answers the empty reply
# EXCLUDES: halves read wrong (a lost, added or changed half), a core that
#   starts with a node or a record
law tree_ffi_open:
  for +hs: List<&2, Nat>
  for h: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, hs)), LawsBase.wire_nats_fit(hs)) == True{} : Bool}
  {Ft.open(Wr.put_list(~Nat, ~Wr.put_nat, hs, "")) == (Ft.Live{Tr.core.start(hs)}, "") : Ft.St & String}

# LAW tree_ffi_open_left_over (R4): halves that fit the wire, followed by any more input,
# open the refused state and answer the error form "tree: input left after
# the halves"
# EXCLUDES: trailing input ignored or read as more halves, a core opened
#   from halves followed by garbage
law tree_ffi_open_left_over:
  for +hs: List<&2, Nat>
  for fits: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, hs)), LawsBase.wire_nats_fit(hs)) == True{} : Bool}
  for +c: Char
  for +t: String
  {Ft.open(Wr.put_list(~Nat, ~Wr.put_nat, hs, SCon{c, t})) == (Ft.Shut{}, Wr.err("tree: input left after the halves")) : Ft.St & String}

# LAW tree_ffi_open_reads_only_halves (R4): an open answered with anything but the error
# form had exactly a list of halves for input, each half and the count
# within the wire, nothing after it, and opened the empty core that splits
# at those halves, answering nothing
# EXCLUDES: an open that accepts a malformed, non-canonical or overlong
#   list, or input left over, and opens a core anyway (a default instead of
#   the refused state)
law tree_ffi_open_reads_only_halves:
  for +input: String
  for ok: {LawsBase.wire_opens_err(Pair.snd(Ft.St, String, Ft.open(input))) == False{} : Bool}
  exs hs: List<&2, Nat>
  {(input, (Bool.and(LawsBase.wire_fits(List.length(&2, Nat, hs)), LawsBase.wire_nats_fit(hs)), Ft.open(input))) == (Wr.put_list(~Nat, ~Wr.put_nat, hs, ""), (True{}, (Ft.Live{Tr.core.start(hs)}, ""))) : String & (Bool & (Ft.St & String))}

# LAW tree_ffi_open_malformed_unless_halves (R4): every open answer but the error form
# "tree: malformed halves" comes from an input that begins with a list of
# halves within the wire
# EXCLUDES: the left-over error (or any answer) for input that does not
#   begin with a list of halves, the malformed error spelled with another
#   text
law tree_ffi_open_malformed_unless_halves:
  for +input: String
  for other: {String.eq(Pair.snd(Ft.St, String, Ft.open(input)), Wr.err("tree: malformed halves")) == False{} : Bool}
  exs hs: List<&2, Nat>
  exs rest: String
  {(input, Bool.and(LawsBase.wire_fits(List.length(&2, Nat, hs)), LawsBase.wire_nats_fit(hs))) == (Wr.put_list(~Nat, ~Wr.put_nat, hs, rest), True{}) : String & Bool}

# the reply p (an open's, or a step's), then the replies of the steps on
# the inputs ins, in order, from the state p left
def tree.trace(ins: List<&2, String>, p: Ft.St & String) -> List<&2, String>:
  match ins:
    case Nil{}:
      [Pair.snd(Ft.St, String, p)]
    case i <> rest:
      (s, a) = p
      a <> tree.trace(rest, Ft.step(s, i))

# one refusal "tree: the open was refused" per input
def tree.refusals(ins: List<&2, String>) -> List<&2, String>:
  match ins:
    case Nil{}:
      Nil{}
    case i <> rest:
      Wr.err("tree: the open was refused") <> tree.refusals(rest)

# LAW tree_ffi_refused_stays (R4): an open answered with the error form opens no core: every
# step after it, whatever the inputs and however many, answers the error
# form "tree: the open was refused"
# EXCLUDES: a core conjured after a refused open (on a later step, or by
#   an open that answers an error but keeps a live core), a step of the
#   refused state answered with another text or with a value
law tree_ffi_refused_stays:
  for +input: String
  for bad: {LawsBase.wire_opens_err(Pair.snd(Ft.St, String, Ft.open(input))) == True{} : Bool}
  for +ins: List<&2, String>
  {tree.trace(ins, Ft.open(input)) == Pair.snd(Ft.St, String, Ft.open(input)) <> tree.refusals(ins) : List<&2, String>}

# LAW tree_ffi_fits_exists: witness: asks and halves that fit exist (the premises above)
# EXCLUDES: a vacuous tree.ask_fits or open premise
law tree_ffi_fits_exists:
  exs q: Tr.Ask
  exs hs: List<&2, Nat>
  {Bool.and(tree.ask_fits(q), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, hs)), LawsBase.wire_nats_fit(hs))) == True{} : Bool}

# LAW tree_ffi_journal_example (R5): anchor: the Rust test the_live_tree_follows_the_core
# (crates/eukhe-durable/src/tree/journal.rs:326-390) through the entry, in
# the bytes the journal writes (journal.rs:47-58, 128-142, 209-217) with
# its value indexes (10, 20, 30, 40, 21, 50 are 0, 1, 2, 3, 4, 5): the puts
# of 1 under 0, 2 under 1, 3 under 2 take, 4 under 9 is kept, 2 again with
# 21 and then 20 take; the plan to 2 records stops 3; the delete of 2 cuts
# 2 and 3; the rewind deleting 1 and putting 5 under 0 takes; the snapshot
# after 3 records is 1, 2, 3; the plan to 3 records stops 5 and starts 1,
# 2, 3; the snapshot after all 8 records is 5. The core opens with the
# halves 4, 2, 1 and answers nothing (Rust: 2^46, ..., 2, 1; the answers
# do not depend on the halves, A2)
# EXCLUDES: a tag, field order or count that differs from the bytes the
#   Rust test drives, a question that changes a later answer
law tree_ffi_journal_example:
  {tree.trace(["0,0,0,1,0,0,", "0,0,0,2,1,1,", "0,0,0,3,2,2,", "0,0,0,4,9,3,", "0,0,0,2,1,4,", "0,0,0,2,1,1,", "1,2,", "0,0,1,2,", "0,1,2,1,1,0,5,0,5,", "2,3,", "1,3,", "2,8,"], Ft.open("3,4,2,1,")) == ["", "1,", "1,", "1,", "0,", "1,", "1,", "3,1,1,3,", "2,2,2,3,", "1,", "4,3,1,0,0,2,1,1,3,2,2,", "3,4,1,5,0,1,0,2,0,3,", "4,1,5,0,5,"] : List<&2, String>}

# The spelled entry
# -----------------
# The bytes Rust writes and reads (crates/eukhe-durable src/tree/journal.rs),
# spelled from the wire's primitives only, never with the entry's own
# put_*/get_*: a tag, a field order or a count that drifts on both sides of
# the entry alike breaks these laws. With them, every input of a live step
# is pinned: a spelled ask that fits answers the core's step
# (tree_ffi_answers_spelled), the same followed by more input answers the
# left-over error (tree_ffi_left_over_spelled), any other input answers
# the malformed error (tree_ffi_malformed_unless_ask), and every error
# keeps the core (tree_ffi_error_keeps). The open is pinned by
# tree_ffi_open* on the wire's own list of Nats, a refused open by
# tree_ffi_refused_stays.

# an op: 0, key, parent, value (put) | 1, key (delete)
def tree.spell_op(o: Tr.Op, rest: String) -> String:
  match o:
    case Tr.Put{k, p, v}:
      Wr.put_nat(0n, Wr.put_nat(k, Wr.put_nat(p, Wr.put_nat(v, rest))))
    case Tr.Del{k}:
      Wr.put_nat(1n, Wr.put_nat(k, rest))

# the ops of a rewind, each spelled, then rest
def tree.spell_ops(ops: List<&2, Tr.Op>, rest: String) -> String:
  match ops:
    case Nil{}:
      rest
    case o <> more:
      tree.spell_op(o, tree.spell_ops(more, rest))

# an ask: 0 then a record (0 then an op: do | 1, the count of ops, then
# the ops: rewind) | 1, n (plan) | 2, n (snapshot)
def tree.spell_ask(q: Tr.Ask, rest: String) -> String:
  match q:
    case Tr.Note{r}:
      match r:
        case Tr.Do{o}:
          Wr.put_nat(0n, Wr.put_nat(0n, tree.spell_op(o, rest)))
        case Tr.Rewind{+ops}:
          Wr.put_nat(0n, Wr.put_nat(1n, Wr.put_nat(List.length(&2, Tr.Op, ops), tree.spell_ops(ops, rest))))
    case Tr.Plan{n}:
      Wr.put_nat(1n, Wr.put_nat(n, rest))
    case Tr.Snap{n}:
      Wr.put_nat(2n, Wr.put_nat(n, rest))

# an effect: 0 start | 1 stop | 2 restore, then the key
def tree.spell_eff(e: Tr.Eff, rest: String) -> String:
  match e:
    case Tr.Start{k}:
      Wr.put_nat(0n, Wr.put_nat(k, rest))
    case Tr.Stop{k}:
      Wr.put_nat(1n, Wr.put_nat(k, rest))
    case Tr.Restore{k}:
      Wr.put_nat(2n, Wr.put_nat(k, rest))

# the effects of a plan, each spelled, then rest
def tree.spell_effs(es: List<&2, Tr.Eff>, rest: String) -> String:
  match es:
    case Nil{}:
      rest
    case e <> more:
      tree.spell_eff(e, tree.spell_effs(more, rest))

# a node: key, parent, value
def tree.spell_ent(e: Tr.Ent, rest: String) -> String:
  match e:
    case Tr.Ent{k, p, v}:
      Wr.put_nat(k, Wr.put_nat(p, Wr.put_nat(v, rest)))

# the nodes of a snapshot, each spelled, then rest
def tree.spell_ents(es: List<&2, Tr.Ent>, rest: String) -> String:
  match es:
    case Nil{}:
      rest
    case e <> more:
      tree.spell_ent(e, tree.spell_ents(more, rest))

# an answer: 0 kept | 1 took | 2, the count, the keys cut | 3, the count,
# the effects | 4, the count, the nodes
def tree.spell_ans(a: Tr.Ans, rest: String) -> String:
  match a:
    case Tr.Kept{}:
      Wr.put_nat(0n, rest)
    case Tr.Took{}:
      Wr.put_nat(1n, rest)
    case Tr.Cut{ks}:
      Wr.put_nat(2n, LawsBase.wire_spell_nats(ks, rest))
    case Tr.Effects{+es}:
      Wr.put_nat(3n, Wr.put_nat(List.length(&2, Tr.Eff, es), tree.spell_effs(es, rest)))
    case Tr.Nodes{+es}:
      Wr.put_nat(4n, Wr.put_nat(List.length(&2, Tr.Ent, es), tree.spell_ents(es, rest)))

# LAW tree_ffi_answers_spelled: in every state of the core, an ask spelled by the grammar,
# every number within the wire, steps the core as the core decides and
# answers the grammar's spelling of the core's answer
# EXCLUDES: an ask or answer tag, a field order or a count that drifts
#   from the grammar Rust writes and reads (on both sides of the entry
#   alike), a field lost, swapped or defaulted, an answer or a next core
#   other than the core's
law tree_ffi_answers_spelled:
  for +s: Tr.St
  for +q: Tr.Ask
  for fits: {tree.ask_fits(q) == True{} : Bool}
  {Ft.step(Ft.Live{s}, tree.spell_ask(q, "")) == (Ft.Live{Pair.fst(Tr.St, Tr.Ans, Tr.core.step(s, q))}, tree.spell_ans(Pair.snd(Tr.St, Tr.Ans, Tr.core.step(s, q)), "")) : Ft.St & String}

# LAW tree_ffi_left_over_spelled: a spelled ask that fits, followed by any more input, keeps
# the core and answers the error form "tree: input left after the ask"
# EXCLUDES: trailing input ignored, or read as part of the ask
law tree_ffi_left_over_spelled:
  for +s: Tr.St
  for +q: Tr.Ask
  for fits: {tree.ask_fits(q) == True{} : Bool}
  for +c: Char
  for +t: String
  {Ft.step(Ft.Live{s}, tree.spell_ask(q, SCon{c, t})) == (Ft.Live{s}, Wr.err("tree: input left after the ask")) : Ft.St & String}

# LAW tree_ffi_unknown_ask: an ask tag of 3 or more (of any length) keeps the core and
# answers the error form "tree: malformed ask", whatever follows
# EXCLUDES: an unknown ask read as a note, a plan or a snapshot, or as the
#   left-over error
law tree_ffi_unknown_ask:
  for +s: Tr.St
  for +n: Nat
  for +rest: String
  {Ft.step(Ft.Live{s}, Wr.put_nat(3n+n, rest)) == (Ft.Live{s}, Wr.err("tree: malformed ask")) : Ft.St & String}

# LAW tree_ffi_unknown_record: a note whose record tag is 2 or more (of any length) keeps the
# core and answers the error form "tree: malformed ask", whatever follows
# EXCLUDES: an unknown record read as a do or a rewind
law tree_ffi_unknown_record:
  for +s: Tr.St
  for +n: Nat
  for +rest: String
  {Ft.step(Ft.Live{s}, Wr.put_nat(0n, Wr.put_nat(2n+n, rest))) == (Ft.Live{s}, Wr.err("tree: malformed ask")) : Ft.St & String}

# LAW tree_ffi_unknown_op: a do whose op tag is 2 or more (of any length) keeps the core and
# answers the error form "tree: malformed ask", whatever follows
# EXCLUDES: an unknown op read as a put or a delete
law tree_ffi_unknown_op:
  for +s: Tr.St
  for +n: Nat
  for +rest: String
  {Ft.step(Ft.Live{s}, Wr.put_nat(0n, Wr.put_nat(0n, Wr.put_nat(2n+n, rest)))) == (Ft.Live{s}, Wr.err("tree: malformed ask")) : Ft.St & String}

# LAW tree_ffi_unknown_rewind_op: a rewind of one or more ops (any count) whose first op tag is
# 2 or more (of any length) keeps the core and answers the error form
# "tree: malformed ask", whatever follows
# EXCLUDES: an unknown op of a rewind read as a put or a delete, or
#   skipped
law tree_ffi_unknown_rewind_op:
  for +s: Tr.St
  for +m: Nat
  for +n: Nat
  for +rest: String
  {Ft.step(Ft.Live{s}, Wr.put_nat(0n, Wr.put_nat(1n, Wr.put_nat(1n+m, Wr.put_nat(2n+n, rest))))) == (Ft.Live{s}, Wr.err("tree: malformed ask")) : Ft.St & String}

# LAW tree_ffi_reads_only_asks: in every state, an answer that is not the error form answers an
# ask: the input is exactly the spelling of an ask whose numbers fit the
# wire, and the step is the core's step on it, its answer spelled
# EXCLUDES: a decoder that accepts an unknown tag, a missing or extra
#   field or op, a non-canonical number, or input left over, and answers
#   it anyway (a default instead of the error form)
law tree_ffi_reads_only_asks:
  for +s: Tr.St
  for +input: String
  for ok: {LawsBase.wire_opens_err(Pair.snd(Ft.St, String, Ft.step(Ft.Live{s}, input))) == False{} : Bool}
  exs q: Tr.Ask
  {(input, (tree.ask_fits(q), Ft.step(Ft.Live{s}, input))) == (tree.spell_ask(q, ""), (True{}, (Ft.Live{Pair.fst(Tr.St, Tr.Ans, Tr.core.step(s, q))}, tree.spell_ans(Pair.snd(Tr.St, Tr.Ans, Tr.core.step(s, q)), "")))) : String & (Bool & (Ft.St & String))}

# LAW tree_ffi_malformed_unless_ask: in every state, every answer but the error form "tree:
# malformed ask" comes from an input that begins with a spelled ask that
# fits
# EXCLUDES: the left-over error (or any answer) for input that does not
#   begin with an ask, the malformed error spelled with another text
law tree_ffi_malformed_unless_ask:
  for +s: Tr.St
  for +input: String
  for other: {String.eq(Pair.snd(Ft.St, String, Ft.step(Ft.Live{s}, input)), Wr.err("tree: malformed ask")) == False{} : Bool}
  exs q: Tr.Ask
  exs rest: String
  {(input, tree.ask_fits(q)) == (tree.spell_ask(q, rest), True{}) : String & Bool}

# LAW tree_ffi_error_keeps: in every state, a step answered with the error form keeps the
# core as it was
# EXCLUDES: a malformed or left-over input that changes, resets or
#   refuses the core
law tree_ffi_error_keeps:
  for +s: Tr.St
  for +input: String
  for bad: {LawsBase.wire_opens_err(Pair.snd(Ft.St, String, Ft.step(Ft.Live{s}, input))) == True{} : Bool}
  {Pair.fst(Ft.St, String, Ft.step(Ft.Live{s}, input)) == Ft.Live{s} : Ft.St}

# LAW tree_ffi_tags_example: anchor: the bytes Rust sends and reads, on the core opened with
# the halves [1] (s0) and on it after the put of node 1 under the root with
# value 7 (s1): on s0 that put takes (1,) and a delete of the root is kept
# (0,); on s1 a delete of 1 cuts [1] (2,1,1,), a put of 2 under 0 takes
# and one under 5 is kept, a rewind deleting 1 takes, the plan to 0
# records stops 1 (3,1,1,1,), the snapshot after 1 record is the node
# (4,1,1,0,7,); an ask tag 3, a record tag 2, an op tag 2, a rewind op
# tag 2 and the empty input are malformed, a plan with input after it is
# left over; the open of the halves [2, 1] answers nothing, a short one is
# malformed and one with input after it is left over
# EXCLUDES: a tag or field order that differs from the Rust side (the
#   universal laws share the laws' spelling), an unknown tag read as a
#   known one, an error text that differs
law tree_ffi_tags_example:
  {[Pair.snd(Ft.St, String, Ft.step(Ft.Live{Tr.core.start([1n])}, "0,0,0,1,0,7,")), Pair.snd(Ft.St, String, Ft.step(Ft.Live{Tr.core.start([1n])}, "0,0,1,0,")), Pair.snd(Ft.St, String, Ft.step(Ft.Live{Tr.core.feed([1n], [Tr.Do{Tr.Put{1n, 0n, 7n}}])}, "0,0,1,1,")), Pair.snd(Ft.St, String, Ft.step(Ft.Live{Tr.core.feed([1n], [Tr.Do{Tr.Put{1n, 0n, 7n}}])}, "0,0,0,2,0,3,")), Pair.snd(Ft.St, String, Ft.step(Ft.Live{Tr.core.feed([1n], [Tr.Do{Tr.Put{1n, 0n, 7n}}])}, "0,0,0,2,5,3,")), Pair.snd(Ft.St, String, Ft.step(Ft.Live{Tr.core.feed([1n], [Tr.Do{Tr.Put{1n, 0n, 7n}}])}, "0,1,1,1,1,")), Pair.snd(Ft.St, String, Ft.step(Ft.Live{Tr.core.feed([1n], [Tr.Do{Tr.Put{1n, 0n, 7n}}])}, "1,0,")), Pair.snd(Ft.St, String, Ft.step(Ft.Live{Tr.core.feed([1n], [Tr.Do{Tr.Put{1n, 0n, 7n}}])}, "2,1,")), Pair.snd(Ft.St, String, Ft.step(Ft.Live{Tr.core.start([1n])}, "3,")), Pair.snd(Ft.St, String, Ft.step(Ft.Live{Tr.core.start([1n])}, "0,2,")), Pair.snd(Ft.St, String, Ft.step(Ft.Live{Tr.core.start([1n])}, "0,0,2,")), Pair.snd(Ft.St, String, Ft.step(Ft.Live{Tr.core.start([1n])}, "0,1,1,2,")), Pair.snd(Ft.St, String, Ft.step(Ft.Live{Tr.core.start([1n])}, "")), Pair.snd(Ft.St, String, Ft.step(Ft.Live{Tr.core.start([1n])}, "1,4,x")), Pair.snd(Ft.St, String, Ft.open("2,2,1,")), Pair.snd(Ft.St, String, Ft.open("2,2,")), Pair.snd(Ft.St, String, Ft.open("0,x"))] == ["1,", "0,", "2,1,1,", "1,", "0,", "1,", "3,1,1,1,", "4,1,1,0,7,", Wr.err("tree: malformed ask"), Wr.err("tree: malformed ask"), Wr.err("tree: malformed ask"), Wr.err("tree: malformed ask"), Wr.err("tree: malformed ask"), Wr.err("tree: input left after the ask"), "", Wr.err("tree: malformed halves"), Wr.err("tree: input left after the halves")] : List<&2, String>}

# The session tree against its spec (S1)
# ---------------------------------------
# spec/durable/tree.bend restates S1 (T1-T7) without the code of
# bend/tree.bend: a lookup is the first node of a key, a put drops the
# node's key and inserts the node in key order, a delete keeps the nodes
# that are not the deleted node or below it (walking up their parents), a
# rewind applies its ops exactly and is kept only when the result is a
# valid tree, and the rewind plan and the answers follow from those. The
# laws below state that the model, and so the core (laws tree_core_*) and
# the entry, are that spec.

# LAW tree_replay_spec (S1): the tree any journal makes is the spec's (T1-T5): any puts (valid
# or not), any deletes, any rewinds
# EXCLUDES: a put that lands under a missing parent or replaces another
#   node, a delete that keeps a node below the deleted one or drops another,
#   a rewind kept when its result is no valid tree or refused when it is,
#   records applied out of order
law tree_replay_spec:
  for +rs: List<&2, Tr.Rec>
  {Tr.replay(rs) == TS.replay(rs) : List<&2, Tr.Ent>}

# LAW tree_spec_example (S1): anchor: the spec on a journal: a child, a delete of its parent
# that cuts it and its own child, a put under a deleted node refused, a
# rewind whose result is no valid tree kept out, one that is valid taken
# EXCLUDES: a vacuous or misread spec
law tree_spec_example:
  {TS.replay([Tr.Do{Tr.Put{2n, 0n, 7n}}, Tr.Do{Tr.Put{5n, 2n, 1n}}, Tr.Do{Tr.Put{3n, 0n, 4n}}, Tr.Do{Tr.Put{9n, 5n, 4n}}, Tr.Do{Tr.Del{2n}}, Tr.Do{Tr.Put{4n, 9n, 1n}}, Tr.Rewind{[Tr.Put{6n, 3n, 2n}, Tr.Del{3n}]}, Tr.Rewind{[Tr.Put{6n, 3n, 2n}]}]) == [Tr.Ent{3n, 0n, 4n}, Tr.Ent{6n, 3n, 2n}] : List<&2, Tr.Ent>} &
  {TS.answer(TS.replay([Tr.Do{Tr.Put{2n, 0n, 7n}}, Tr.Do{Tr.Put{5n, 2n, 1n}}, Tr.Do{Tr.Put{3n, 0n, 4n}}, Tr.Do{Tr.Put{9n, 5n, 4n}}]), Tr.Do{Tr.Del{2n}}) == Tr.Cut{[2n, 5n, 9n]} : Tr.Ans} &
  {TS.diff([Tr.Ent{2n, 0n, 1n}, Tr.Ent{3n, 0n, 1n}], [Tr.Ent{3n, 0n, 2n}, Tr.Ent{4n, 3n, 1n}]) == [Tr.Del{2n}, Tr.Put{3n, 0n, 2n}, Tr.Put{4n, 3n, 1n}] : List<&2, Tr.Op>}

# The stepper as a machine over journals: the state the entry holds after
# an open with halves hs and the records rs is the core fed rs
# (Tr.core.feed, the only states the entry reaches); a step answers from
# the spec's tree of that journal, its answer spelled by the grammar of
# section "The spelled entry".

# the step of the entry after the journal rs on the ask q: its next state
# and the spec's answer, spelled
def ts_step(+hs: List<&2, Nat>, +rs: List<&2, Tr.Rec>, q: Tr.Ask) -> Ft.St & String:
  match q:
    case Tr.Note{+r}:
      (Ft.Live{Tr.core.feed(hs, List.append(&2, Tr.Rec, rs, [r]))}, tree.spell_ans(TS.answer(TS.replay(rs), r), ""))
    case Tr.Plan{+n}:
      +now = TS.replay(rs)
      (Ft.Live{Tr.core.feed(hs, rs)}, tree.spell_ans(Tr.Effects{TS.effects(TS.diff(now, TS.replay(List.take(&2, Tr.Rec, rs, n))), now)}, ""))
    case Tr.Snap{+n}:
      (Ft.Live{Tr.core.feed(hs, rs)}, tree.spell_ans(Tr.Nodes{TS.replay(List.take(&2, Tr.Rec, rs, n))}, ""))

# LAW tree_ffi_step_spec (S1, T5-T7): after any open and any journal, an ask spelled by the
# grammar, every number within the wire, steps the entry as the spec says:
# a record moves to the journal with it at its end and answers the spec's
# answer to it on the spec's tree (T7); a plan keeps the journal and
# answers the spec's work of the spec's rewind (T6) from the spec's tree to
# the tree after the first n records; a snapshot keeps the journal and
# answers the spec's tree after the first n records; each answer spelled by
# the grammar. Every other input (left over, malformed) is pinned in every
# state by tree_ffi_reads_only_asks, tree_ffi_malformed_unless_ask,
# tree_ffi_left_over_spelled and tree_ffi_error_keeps.
# EXCLUDES: an answer, a plan or a snapshot other than the spec's, a
#   journal that drops, repeats or reorders a record or moves on a plan or
#   a snapshot, another spelling
law tree_ffi_step_spec:
  for +hs: List<&2, Nat>
  for +rs: List<&2, Tr.Rec>
  for +q: Tr.Ask
  for fits: {tree.ask_fits(q) == True{} : Bool}
  {Ft.step(Ft.Live{Tr.core.feed(hs, rs)}, tree.spell_ask(q, "")) == ts_step(hs, rs, q) : Ft.St & String}

# LAW tree_diff_spec (S1): the rewind from any tree to any tree is the spec's (T6): the
# deletes of the nodes the target lacks, then the puts of the nodes the
# current tree does not hold the same, each in key order
# EXCLUDES: a lost, extra or reordered op, a put of a node already held
#   the same
law tree_diff_spec:
  for +a: List<&2, Tr.Ent>
  for +b: List<&2, Tr.Ent>
  {Tr.diff(a, b) == TS.diff(a, b) : List<&2, Tr.Op>}

def tree.effect(held: Bool, k: Nat) -> Tr.Eff:
  match held:
    case True{}:
      Tr.Restore{k}
    case False{}:
      Tr.Start{k}

# what the ops of a rewind of t do to the work of each node: a Del stops
# it; a Put restores a node t has and starts one t does not have
def tree.effects(ops: List<&2, Tr.Op>, +t: List<&2, Tr.Ent>) -> List<&2, Tr.Eff>:
  match ops:
    case Nil{}:
      Nil{}
    case o <> rest:
      match o:
        case Tr.Del{k}:
          Tr.Stop{k} <> tree.effects(rest, t)
        case Tr.Put{+k, p, v}:
          tree.effect(Tr.has(t, k), k) <> tree.effects(rest, t)

# LAW tree_core_plan: the core's rewind plan to the tree after the first n records is
# what diff(live tree, that tree) does to the work of each node
law tree_core_plan_orig:
  for +hs: List<&2, Nat>
  for +rs: List<&2, Tr.Rec>
  for +n: Nat
  {Pair.snd(Tr.St, Tr.Ans, Tr.core.step(Tr.core.feed(hs, rs), Tr.Plan{n})) == Tr.Effects{tree.effects(Tr.diff(Tr.replay(rs), Tr.replay(List.take(&2, Tr.Rec, rs, n))), Tr.replay(rs))} : Tr.Ans}
