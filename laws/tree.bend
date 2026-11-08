# eukhe: the laws of area tree

import Base
import ../bend/director.bend as Dr
import ../bend/ffi_tree.bend as Ft
import ../bend/tree.bend as Tr
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (S1) The session tree
# ---------------------
# docs/state.md S1, the model in bend/tree.bend. One tree holds the
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

# LAW tree_snapshot: a snapshot after any prefix of the journal, with the records after
# it, makes the tree of the whole journal. So a client that holds a
# snapshot and gets the records after it holds the live tree.
law tree_snapshot:
  for +pre: List<&2, Tr.Rec>
  for post: List<&2, Tr.Rec>
  {Tr.go(post, Tr.replay(pre)) == Tr.replay(List.append(&2, Tr.Rec, pre, post)) : List<&2, Tr.Ent>}

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

# LAW tree_core_note: a record steps the core to the core of the journal with the record
# at its end, so the laws on core.feed hold for the live core
law tree_core_note:
  for +hs: List<&2, Nat>
  for +rs: List<&2, Tr.Rec>
  for +r: Tr.Rec
  {Pair.fst(Tr.St, Tr.Ans, Tr.core.step(Tr.core.feed(hs, rs), Tr.Note{r})) == Tr.core.feed(hs, List.append(&2, Tr.Rec, rs, [r])) : Tr.St}

# LAW tree_core_plan: the core's rewind plan to the tree after the first n records is
# what diff(live tree, that tree) does to the work of each node
law tree_core_plan:
  for +hs: List<&2, Nat>
  for +rs: List<&2, Tr.Rec>
  for +n: Nat
  {Pair.snd(Tr.St, Tr.Ans, Tr.core.step(Tr.core.feed(hs, rs), Tr.Plan{n})) == Tr.Effects{tree.effects(Tr.diff(Tr.replay(rs), Tr.replay(List.take(&2, Tr.Rec, rs, n))), Tr.replay(rs))} : Tr.Ans}

# LAW tree_core_snap: the core's snapshot after the first n records is their replay
law tree_core_snap:
  for +hs: List<&2, Nat>
  for +rs: List<&2, Tr.Rec>
  for +n: Nat
  {Pair.snd(Tr.St, Tr.Ans, Tr.core.step(Tr.core.feed(hs, rs), Tr.Snap{n})) == Tr.Nodes{Tr.replay(List.take(&2, Tr.Rec, rs, n))} : Tr.Ans}

# LAW tree_core_plan_keeps: a rewind plan leaves the core as it was
law tree_core_plan_keeps:
  for +hs: List<&2, Nat>
  for +rs: List<&2, Tr.Rec>
  for +n: Nat
  {Pair.fst(Tr.St, Tr.Ans, Tr.core.step(Tr.core.feed(hs, rs), Tr.Plan{n})) == Tr.core.feed(hs, rs) : Tr.St}

# LAW tree_core_snap_keeps: a snapshot leaves the core as it was
law tree_core_snap_keeps:
  for +hs: List<&2, Nat>
  for +rs: List<&2, Tr.Rec>
  for +n: Nat
  {Pair.fst(Tr.St, Tr.Ans, Tr.core.step(Tr.core.feed(hs, rs), Tr.Snap{n})) == Tr.core.feed(hs, rs) : Tr.St}

# (S5) The Director stack
# -----------------------
# docs/control.md S5, the model in bend/director.bend. Every verdict is
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

# LAW tree_ffi_step: a step answers the core's answer to the ask and keeps the core's
# next state
# EXCLUDES: an entry that answers anything but the core's decision, or
#   that drops, repeats or reorders a record of the core's journal
law tree_ffi_step:
  for +s: Tr.St
  for +q: Tr.Ask
  for h: {tree.ask_fits(q) == True{} : Bool}
  {Ft.step(Ft.Live{s}, Ft.put_ask(q, "")) == (Ft.Live{Pair.fst(Tr.St, Tr.Ans, Tr.core.step(s, q))}, Ft.put_ans(Pair.snd(Tr.St, Tr.Ans, Tr.core.step(s, q)), "")) : Ft.St & String}

# LAW tree_ffi_malformed: malformed input answers the error form and keeps the core
# EXCLUDES: a default answer, or a changed core, for input that is no ask
law tree_ffi_malformed:
  for +s: Tr.St
  for +input: String
  for h: {Ft.get_ask(input) == Wr.Bad{} : Wr.Dec<Tr.Ask>}
  {Ft.step(Ft.Live{s}, input) == (Ft.Live{s}, Wr.err("tree: malformed ask")) : Ft.St & String}

# LAW tree_ffi_trailing: input left after an ask answers the error form and keeps the core
# EXCLUDES: an answer to an ask followed by garbage
law tree_ffi_trailing:
  for +s: Tr.St
  for +input: String
  for q: Tr.Ask
  for rest: String
  for h: {Ft.get_ask(input) == Wr.Got{q, rest} : Wr.Dec<Tr.Ask>}
  for left: {Wr.end(rest) == False{} : Bool}
  {Ft.step(Ft.Live{s}, input) == (Ft.Live{s}, Wr.err("tree: input left after the ask")) : Ft.St & String}

# LAW tree_ffi_refused: a refused open answers every step with the error form
# EXCLUDES: a core conjured after a refused open
law tree_ffi_refused:
  for input: String
  {Ft.step(Ft.Shut{}, input) == (Ft.Shut{}, Wr.err("tree: the open was refused")) : Ft.St & String}

# LAW tree_ffi_open: an open with halves that fit the wire opens the empty core that
# splits at those halves, and answers the empty reply
# EXCLUDES: halves read wrong (a lost, added or changed half), a core that
#   starts with a node or a record
law tree_ffi_open:
  for +hs: List<&2, Nat>
  for h: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, hs)), LawsBase.wire_nats_fit(hs)) == True{} : Bool}
  {Ft.open(Wr.put_list(~Nat, ~Wr.put_nat, hs, "")) == (Ft.Live{Tr.core.start(hs)}, "") : Ft.St & String}

# LAW tree_ffi_open_malformed: an open whose input is no list of halves is refused
# EXCLUDES: a default core for malformed input
law tree_ffi_open_malformed:
  for +input: String
  for h: {Wr.get_list(~Nat, ~Wr.get_nat, input) == Wr.Bad{} : Wr.Dec<List<&2, Nat>>}
  {Ft.open(input) == (Ft.Shut{}, Wr.err("tree: malformed halves")) : Ft.St & String}

# LAW tree_ffi_open_trailing: an open with input left after the halves is refused
# EXCLUDES: a core opened from halves followed by garbage
law tree_ffi_open_trailing:
  for +input: String
  for hs: List<&2, Nat>
  for rest: String
  for h: {Wr.get_list(~Nat, ~Wr.get_nat, input) == Wr.Got{hs, rest} : Wr.Dec<List<&2, Nat>>}
  for left: {Wr.end(rest) == False{} : Bool}
  {Ft.open(input) == (Ft.Shut{}, Wr.err("tree: input left after the halves")) : Ft.St & String}

# LAW tree_ffi_fits_exists: witness: asks and halves that fit exist (the premises above)
# EXCLUDES: a vacuous tree.ask_fits or open premise
law tree_ffi_fits_exists:
  exs q: Tr.Ask
  exs hs: List<&2, Nat>
  {Bool.and(tree.ask_fits(q), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, hs)), LawsBase.wire_nats_fit(hs))) == True{} : Bool}

# LAW tree_ffi_example: anchors of the encodings Rust writes and reads (crates/eukhe-durable
# src/tree/journal.rs): an ask of each kind, and an answer of each kind
# EXCLUDES: a field order or a tag that differs from the Rust side
law tree_ffi_example:
  {[Ft.put_ask(Tr.Note{Tr.Do{Tr.Put{2n, 1n, 7n}}}, ""), Ft.put_ask(Tr.Note{Tr.Do{Tr.Del{2n}}}, ""), Ft.put_ask(Tr.Note{Tr.Rewind{[Tr.Del{3n}, Tr.Put{2n, 1n, 0n}]}}, ""), Ft.put_ask(Tr.Plan{4n}, ""), Ft.put_ask(Tr.Snap{5n}, ""), Ft.put_ans(Tr.Kept{}, ""), Ft.put_ans(Tr.Took{}, ""), Ft.put_ans(Tr.Cut{[2n, 3n]}, ""), Ft.put_ans(Tr.Effects{[Tr.Start{1n}, Tr.Stop{2n}, Tr.Restore{3n}]}, ""), Ft.put_ans(Tr.Nodes{[Tr.Ent{1n, 0n, 9n}]}, "")] == ["0,0,0,2,1,7,", "0,0,1,2,", "0,1,2,1,3,0,2,1,0,", "1,4,", "2,5,", "0,", "1,", "2,2,2,3,", "3,3,0,1,1,2,2,3,", "4,1,1,0,9,"] : List<&2, String>}

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
# tree_ffi_refused.

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
