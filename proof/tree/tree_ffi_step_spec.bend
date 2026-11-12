# eukhe: the proof of LAW tree_ffi_step_spec
#
# PROOF: a spelled ask that fits steps the entry as the core steps, its
# answer spelled (tree_ffi_answers_spelled). The core's next state and
# answer after a journal are the core laws' (a record: tc.note,
# tree_core_answer; a plan: tc.plan_keeps, tree_core_plan; a snapshot:
# tc.snap_keeps, tree_core_snap), and those are the spec's: the replay
# (tree_replay_spec), the answer on a valid tree (TA.ta.answer,
# tree_replay_sound), and the plan (PL.pl.plan: the spec's work of the
# spec's rewind is the plan R3 states).

import Base
import ../../bend/ffi_tree.bend as Ft
import ../../bend/tree.bend as Tr
import ../../laws/tree.bend as Tree
import ../../spec/durable/tree.bend as TS
import ./base/tree/core.bend as LATreeCore
import ./tree_ffi_answers_spelled.bend as PTreeFfiAnswersSpelled
import ./tree_core_answer.bend as PTreeCoreAnswer
import ./tree_core_plan.bend as PTreeCorePlan
import ./tree_core_snap.bend as PTreeCoreSnap
import ./tree_replay_sound.bend as PTreeReplaySound
import ./tree_replay_spec.bend as PTreeReplaySpec
import ./tree_core_plan/plan.bend as PL
import ./tree_ffi_step_spec/answer.bend as TA

def te.q(+hs: List<&2, Nat>, +rs: List<&2, Tr.Rec>, q: Tr.Ask) -> {(Ft.Live{Pair.fst(Tr.St, Tr.Ans, Tr.core.step(Tr.core.feed(hs, rs), q))}, Tree.tree.spell_ans(Pair.snd(Tr.St, Tr.Ans, Tr.core.step(Tr.core.feed(hs, rs), q)), "")) == Tree.ts_step(hs, rs, q) : Ft.St & String}:
  match q:
    case Tr.Note{+r}:
      +s = Tr.core.feed(hs, rs)
      +S2 = Tr.core.feed(hs, List.append(&2, Tr.Rec, rs, [r]))
      %Equal.sym(Tr.St, Pair.fst(Tr.St, Tr.Ans, Tr.core.step(s, Tr.Note{r})), S2, LATreeCore.tc.note(hs, rs, r)) : {(Ft.Live{_}, Tree.tree.spell_ans(Pair.snd(Tr.St, Tr.Ans, Tr.core.step(s, Tr.Note{r})), "")) == Tree.ts_step(hs, rs, Tr.Note{r}) : Ft.St & String}
      %Equal.sym(Tr.Ans, Pair.snd(Tr.St, Tr.Ans, Tr.core.step(s, Tr.Note{r})), Tree.tree.answer(Tr.replay(rs), r), Tree.tree_core_answer(hs, rs, r)) : {(Ft.Live{S2}, Tree.tree.spell_ans(_, "")) == Tree.ts_step(hs, rs, Tr.Note{r}) : Ft.St & String}
      %Equal.sym(Tr.Ans, Tree.tree.answer(Tr.replay(rs), r), TS.answer(Tr.replay(rs), r), TA.ta.answer(Tr.replay(rs), r, Tree.tree_replay_sound(rs))) : {(Ft.Live{S2}, Tree.tree.spell_ans(_, "")) == Tree.ts_step(hs, rs, Tr.Note{r}) : Ft.St & String}
      %Tree.tree_replay_spec(rs) : {(Ft.Live{S2}, Tree.tree.spell_ans(TS.answer(Tr.replay(rs), r), "")) == (Ft.Live{S2}, Tree.tree.spell_ans(TS.answer(_, r), "")) : Ft.St & String}
      {==}
    case Tr.Plan{+n}:
      +s = Tr.core.feed(hs, rs)
      +now = Tr.replay(rs)
      +old = Tr.replay(List.take(&2, Tr.Rec, rs, n))
      %Equal.sym(Tr.St, Pair.fst(Tr.St, Tr.Ans, Tr.core.step(s, Tr.Plan{n})), s, LATreeCore.tc.plan_keeps(hs, rs, n)) : {(Ft.Live{_}, Tree.tree.spell_ans(Pair.snd(Tr.St, Tr.Ans, Tr.core.step(s, Tr.Plan{n})), "")) == Tree.ts_step(hs, rs, Tr.Plan{n}) : Ft.St & String}
      %Equal.sym(Tr.Ans, Pair.snd(Tr.St, Tr.Ans, Tr.core.step(s, Tr.Plan{n})), Tr.Effects{Tree.tree.plan(now, old)}, Tree.tree_core_plan(hs, rs, n)) : {(Ft.Live{s}, Tree.tree.spell_ans(_, "")) == Tree.ts_step(hs, rs, Tr.Plan{n}) : Ft.St & String}
      %PL.pl.plan(now, old) : {(Ft.Live{s}, Tree.tree.spell_ans(Tr.Effects{_}, "")) == Tree.ts_step(hs, rs, Tr.Plan{n}) : Ft.St & String}
      %Tree.tree_replay_spec(rs) : {(Ft.Live{s}, Tree.tree.spell_ans(Tr.Effects{TS.effects(TS.diff(now, old), now)}, "")) == (Ft.Live{s}, Tree.tree.spell_ans(Tr.Effects{TS.effects(TS.diff(_, TS.replay(List.take(&2, Tr.Rec, rs, n))), _)}, "")) : Ft.St & String}
      %Tree.tree_replay_spec(List.take(&2, Tr.Rec, rs, n)) : {(Ft.Live{s}, Tree.tree.spell_ans(Tr.Effects{TS.effects(TS.diff(now, old), now)}, "")) == (Ft.Live{s}, Tree.tree.spell_ans(Tr.Effects{TS.effects(TS.diff(now, _), now)}, "")) : Ft.St & String}
      {==}
    case Tr.Snap{+n}:
      +s = Tr.core.feed(hs, rs)
      %Equal.sym(Tr.St, Pair.fst(Tr.St, Tr.Ans, Tr.core.step(s, Tr.Snap{n})), s, LATreeCore.tc.snap_keeps(hs, rs, n)) : {(Ft.Live{_}, Tree.tree.spell_ans(Pair.snd(Tr.St, Tr.Ans, Tr.core.step(s, Tr.Snap{n})), "")) == Tree.ts_step(hs, rs, Tr.Snap{n}) : Ft.St & String}
      %Equal.sym(Tr.Ans, Pair.snd(Tr.St, Tr.Ans, Tr.core.step(s, Tr.Snap{n})), Tr.Nodes{Tr.replay(List.take(&2, Tr.Rec, rs, n))}, Tree.tree_core_snap(hs, rs, n)) : {(Ft.Live{s}, Tree.tree.spell_ans(_, "")) == Tree.ts_step(hs, rs, Tr.Snap{n}) : Ft.St & String}
      %Tree.tree_replay_spec(List.take(&2, Tr.Rec, rs, n)) : {(Ft.Live{s}, Tree.tree.spell_ans(Tr.Nodes{Tr.replay(List.take(&2, Tr.Rec, rs, n))}, "")) == (Ft.Live{s}, Tree.tree.spell_ans(Tr.Nodes{_}, "")) : Ft.St & String}
      {==}

def Tree.tree_ffi_step_spec(hs, rs, q, fits):
  +s = Tr.core.feed(hs, rs)
  %Equal.sym(Ft.St & String, Ft.step(Ft.Live{s}, Tree.tree.spell_ask(q, "")), (Ft.Live{Pair.fst(Tr.St, Tr.Ans, Tr.core.step(s, q))}, Tree.tree.spell_ans(Pair.snd(Tr.St, Tr.Ans, Tr.core.step(s, q)), "")), Tree.tree_ffi_answers_spelled(s, q, fits)) : {_ == Tree.ts_step(hs, rs, q) : Ft.St & String}
  te.q(hs, rs, q)
