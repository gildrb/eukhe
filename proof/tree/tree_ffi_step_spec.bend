# eukhe: the proof of LAW tree_ffi_step_spec
#
# PROOF: a step of the live core is tt_step (tree_ffi_step_exact). On a
# whole ask the core's next state and answer are the core laws' (a record:
# tree_core_note, tree_core_answer; a plan: tree_core_plan_keeps,
# tree_core_plan; a snapshot: tree_core_snap_keeps, tree_core_snap), and
# those are the spec's: the replay (tree_replay_spec), the rewind
# (tree_diff_spec), the answer and the work of a plan (TA.ta.answer on a
# valid tree, tree_replay_sound; TA.ta.effects).

import Base
import ../../bend/ffi_tree.bend as Ft
import ../../bend/tree.bend as Tr
import ../../bend/wire.bend as Wr
import ../../laws/tree.bend as Tree
import ../../spec/durable/tree.bend as TS
import ./tree_ffi_step_exact.bend as PTreeFfiStepExact
import ./tree_core_note.bend as PTreeCoreNote
import ./tree_core_answer.bend as PTreeCoreAnswer
import ./tree_core_plan.bend as PTreeCorePlan
import ./tree_core_plan_keeps.bend as PTreeCorePlanKeeps
import ./tree_core_snap.bend as PTreeCoreSnap
import ./tree_core_snap_keeps.bend as PTreeCoreSnapKeeps
import ./tree_replay_sound.bend as PTreeReplaySound
import ./tree_replay_spec.bend as PTreeReplaySpec
import ./tree_diff_spec.bend as PTreeDiffSpec
import ./tree_ffi_step_spec/answer.bend as TA

# a step's reply is the pair's parts
def te.ans(p: Tr.St & Tr.Ans) -> {Tree.tt_step.ans(p) == (Ft.Live{Pair.fst(Tr.St, Tr.Ans, p)}, Tree.tt_spell_ans(Pair.snd(Tr.St, Tr.Ans, p))) : Ft.St & String}:
  (s, a) = p
  {==}

def te.q(+hs: List<&2, Nat>, +rs: List<&2, Tr.Rec>, q: Tr.Ask) -> {Tree.tt_step.ans(Tr.core.step(Tr.core.feed(hs, rs), q)) == Tree.ts_step.q(hs, rs, q) : Ft.St & String}:
  match q:
    case Tr.Note{+r}:
      +s = Tr.core.feed(hs, rs)
      %Equal.sym(Ft.St & String, Tree.tt_step.ans(Tr.core.step(s, Tr.Note{r})), (Ft.Live{Pair.fst(Tr.St, Tr.Ans, Tr.core.step(s, Tr.Note{r}))}, Tree.tt_spell_ans(Pair.snd(Tr.St, Tr.Ans, Tr.core.step(s, Tr.Note{r})))), te.ans(Tr.core.step(s, Tr.Note{r}))) : {_ == Tree.ts_step.q(hs, rs, Tr.Note{r}) : Ft.St & String}
      %Equal.sym(Tr.St, Pair.fst(Tr.St, Tr.Ans, Tr.core.step(s, Tr.Note{r})), Tr.core.feed(hs, List.append(&2, Tr.Rec, rs, [r])), Tree.tree_core_note(hs, rs, r)) : {(Ft.Live{_}, Tree.tt_spell_ans(Pair.snd(Tr.St, Tr.Ans, Tr.core.step(s, Tr.Note{r})))) == Tree.ts_step.q(hs, rs, Tr.Note{r}) : Ft.St & String}
      %Equal.sym(Tr.Ans, Pair.snd(Tr.St, Tr.Ans, Tr.core.step(s, Tr.Note{r})), Tree.tree.answer(Tr.replay(rs), r), Tree.tree_core_answer(hs, rs, r)) : {(Ft.Live{Tr.core.feed(hs, List.append(&2, Tr.Rec, rs, [r]))}, Tree.tt_spell_ans(_)) == Tree.ts_step.q(hs, rs, Tr.Note{r}) : Ft.St & String}
      %Equal.sym(Tr.Ans, Tree.tree.answer(Tr.replay(rs), r), TS.answer(Tr.replay(rs), r), TA.ta.answer(Tr.replay(rs), r, Tree.tree_replay_sound(rs))) : {(Ft.Live{Tr.core.feed(hs, List.append(&2, Tr.Rec, rs, [r]))}, Tree.tt_spell_ans(_)) == Tree.ts_step.q(hs, rs, Tr.Note{r}) : Ft.St & String}
      %Tree.tree_replay_spec(rs) : {(Ft.Live{Tr.core.feed(hs, List.append(&2, Tr.Rec, rs, [r]))}, Tree.tt_spell_ans(TS.answer(Tr.replay(rs), r))) == (Ft.Live{Tr.core.feed(hs, List.append(&2, Tr.Rec, rs, [r]))}, Tree.tt_spell_ans(TS.answer(_, r))) : Ft.St & String}
      {==}
    case Tr.Plan{+n}:
      +s = Tr.core.feed(hs, rs)
      +now = Tr.replay(rs)
      +old = Tr.replay(List.take(&2, Tr.Rec, rs, n))
      %Equal.sym(Ft.St & String, Tree.tt_step.ans(Tr.core.step(s, Tr.Plan{n})), (Ft.Live{Pair.fst(Tr.St, Tr.Ans, Tr.core.step(s, Tr.Plan{n}))}, Tree.tt_spell_ans(Pair.snd(Tr.St, Tr.Ans, Tr.core.step(s, Tr.Plan{n})))), te.ans(Tr.core.step(s, Tr.Plan{n}))) : {_ == Tree.ts_step.q(hs, rs, Tr.Plan{n}) : Ft.St & String}
      %Equal.sym(Tr.St, Pair.fst(Tr.St, Tr.Ans, Tr.core.step(s, Tr.Plan{n})), s, Tree.tree_core_plan_keeps(hs, rs, n)) : {(Ft.Live{_}, Tree.tt_spell_ans(Pair.snd(Tr.St, Tr.Ans, Tr.core.step(s, Tr.Plan{n})))) == Tree.ts_step.q(hs, rs, Tr.Plan{n}) : Ft.St & String}
      %Equal.sym(Tr.Ans, Pair.snd(Tr.St, Tr.Ans, Tr.core.step(s, Tr.Plan{n})), Tr.Effects{Tree.tree.effects(Tr.diff(now, old), now)}, Tree.tree_core_plan(hs, rs, n)) : {(Ft.Live{s}, Tree.tt_spell_ans(_)) == Tree.ts_step.q(hs, rs, Tr.Plan{n}) : Ft.St & String}
      %Equal.sym(List<&2, Tr.Eff>, Tree.tree.effects(Tr.diff(now, old), now), TS.effects(Tr.diff(now, old), now), TA.ta.effects(Tr.diff(now, old), now)) : {(Ft.Live{s}, Tree.tt_spell_ans(Tr.Effects{_})) == Tree.ts_step.q(hs, rs, Tr.Plan{n}) : Ft.St & String}
      %Equal.sym(List<&2, Tr.Op>, Tr.diff(now, old), TS.diff(now, old), Tree.tree_diff_spec(now, old)) : {(Ft.Live{s}, Tree.tt_spell_ans(Tr.Effects{TS.effects(_, now)})) == Tree.ts_step.q(hs, rs, Tr.Plan{n}) : Ft.St & String}
      %Tree.tree_replay_spec(rs) : {(Ft.Live{s}, Tree.tt_spell_ans(Tr.Effects{TS.effects(TS.diff(now, old), now)})) == (Ft.Live{s}, Tree.tt_spell_ans(Tr.Effects{TS.effects(TS.diff(_, TS.replay(List.take(&2, Tr.Rec, rs, n))), _)})) : Ft.St & String}
      %Tree.tree_replay_spec(List.take(&2, Tr.Rec, rs, n)) : {(Ft.Live{s}, Tree.tt_spell_ans(Tr.Effects{TS.effects(TS.diff(now, old), now)})) == (Ft.Live{s}, Tree.tt_spell_ans(Tr.Effects{TS.effects(TS.diff(now, _), now)})) : Ft.St & String}
      {==}
    case Tr.Snap{+n}:
      +s = Tr.core.feed(hs, rs)
      %Equal.sym(Ft.St & String, Tree.tt_step.ans(Tr.core.step(s, Tr.Snap{n})), (Ft.Live{Pair.fst(Tr.St, Tr.Ans, Tr.core.step(s, Tr.Snap{n}))}, Tree.tt_spell_ans(Pair.snd(Tr.St, Tr.Ans, Tr.core.step(s, Tr.Snap{n})))), te.ans(Tr.core.step(s, Tr.Snap{n}))) : {_ == Tree.ts_step.q(hs, rs, Tr.Snap{n}) : Ft.St & String}
      %Equal.sym(Tr.St, Pair.fst(Tr.St, Tr.Ans, Tr.core.step(s, Tr.Snap{n})), s, Tree.tree_core_snap_keeps(hs, rs, n)) : {(Ft.Live{_}, Tree.tt_spell_ans(Pair.snd(Tr.St, Tr.Ans, Tr.core.step(s, Tr.Snap{n})))) == Tree.ts_step.q(hs, rs, Tr.Snap{n}) : Ft.St & String}
      %Equal.sym(Tr.Ans, Pair.snd(Tr.St, Tr.Ans, Tr.core.step(s, Tr.Snap{n})), Tr.Nodes{Tr.replay(List.take(&2, Tr.Rec, rs, n))}, Tree.tree_core_snap(hs, rs, n)) : {(Ft.Live{s}, Tree.tt_spell_ans(_)) == Tree.ts_step.q(hs, rs, Tr.Snap{n}) : Ft.St & String}
      %Tree.tree_replay_spec(List.take(&2, Tr.Rec, rs, n)) : {(Ft.Live{s}, Tree.tt_spell_ans(Tr.Nodes{Tr.replay(List.take(&2, Tr.Rec, rs, n))})) == (Ft.Live{s}, Tree.tt_spell_ans(Tr.Nodes{_})) : Ft.St & String}
      {==}

def te.ask(+hs: List<&2, Nat>, +rs: List<&2, Tr.Rec>, d: Wr.Dec<Tr.Ask>) -> {Tree.tt_step.ask(Tr.core.feed(hs, rs), d) == Tree.ts_step.ask(hs, rs, d) : Ft.St & String}:
  match d:
    case Wr.Got{q, r}:
      match r:
        case SNil{}:
          te.q(hs, rs, q)
        case SCon{c, t}:
          {==}
    case Wr.Bad{}:
      {==}

def Tree.tree_ffi_step_spec(hs, rs, input):
  %Equal.sym(Ft.St & String, Ft.step(Ft.Live{Tr.core.feed(hs, rs)}, input), Tree.tt_step(Tr.core.feed(hs, rs), input), Tree.tree_ffi_step_exact(Tr.core.feed(hs, rs), input)) : {_ == Tree.ts_step(hs, rs, input) : Ft.St & String}
  te.ask(hs, rs, Tree.tt_read_ask(input))
