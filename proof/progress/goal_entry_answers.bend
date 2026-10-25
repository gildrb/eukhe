# eukhe: the proof of LAW goal_entry_answers
# The spelled request is the entry's own encoding (field by field), so
# the answer is goal_entry's.

import Base
import ../../laws/progress.bend as Progress
import ../../bend/ffi_progress.bend as FPr
import ../../bend/progress.bend as Pr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../base/logic/bool.bend as LLogicBool
import ./goal_entry.bend as PGoalEntry

def gea.prior(p: Maybe<&2, Pr.Prior>, rest: String) -> {FPr.put_prior(p, rest) == Progress.gs_spell_prior(p, rest) : String}:
  match p:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case Pr.Prior{s, w}:
          {==}

def gea.goal(g: Pr.Goal) -> {FPr.put_goal(g, "") == Progress.gs_spell_goal(g) : String}:
  match g:
    case Pr.Go{s}:
      {==}
    case Pr.Stop{s}:
      {==}

def Progress.goal_entry_answers(q, h):
  match q:
    case Progress.gs.Req{+t, +cap, +p, +work}:
      +hh = h
      +ht = LLogicBool.wr_and_l(LawsBase.wire_fits(t), Bool.and(LawsBase.wire_fits(cap), Bool.and(Progress.wire_prior_fits(p), LawsBase.wire_fits(work))), hh)
      +h1 = LLogicBool.wr_and_r(LawsBase.wire_fits(t), Bool.and(LawsBase.wire_fits(cap), Bool.and(Progress.wire_prior_fits(p), LawsBase.wire_fits(work))), hh)
      +hc = LLogicBool.wr_and_l(LawsBase.wire_fits(cap), Bool.and(Progress.wire_prior_fits(p), LawsBase.wire_fits(work)), h1)
      +h2 = LLogicBool.wr_and_r(LawsBase.wire_fits(cap), Bool.and(Progress.wire_prior_fits(p), LawsBase.wire_fits(work)), h1)
      +hp = LLogicBool.wr_and_l(Progress.wire_prior_fits(p), LawsBase.wire_fits(work), h2)
      +hw = LLogicBool.wr_and_r(Progress.wire_prior_fits(p), LawsBase.wire_fits(work), h2)
      %gea.prior(p, Wr.put_nat(work, "")) : {FPr.ffi(Wr.put_nat(t, Wr.put_nat(cap, _))) == Progress.gs_spell_goal(Pr.judge(t, cap, p, work)) : String}
      %gea.goal(Pr.judge(t, cap, p, work)) : {FPr.ffi(Wr.put_nat(t, Wr.put_nat(cap, FPr.put_prior(p, Wr.put_nat(work, ""))))) == _ : String}
      Progress.goal_entry(t, cap, p, work, ht, hc, hp, hw)
