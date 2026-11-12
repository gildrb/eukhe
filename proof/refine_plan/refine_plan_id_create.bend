# eukhe: the proof of LAW refine_plan_id_create
#
# PROOF: the code's kind name with its memory default is R2's (rpd.name);
# the code's slug is the R1 spec's (refine_plan_slug_words' rps.slug).

import Base
import ../../bend/refine_plan.bend as Rp
import ../../laws/refine_plan/model.bend as RefinePlan
import ./refine_plan_slug_words.bend as PSlug

def rpd.name(c: Maybe<&2, Rp.Comp>) -> {Rp.comp_name(Rp.comp_or_memory(c)) == RefinePlan.rs_kind_name(c) : String}:
  match c:
    case None{}:
      {==}
    case Some{k}:
      match k:
        case Rp.KPrompt{}:
          {==}
        case Rp.KMemory{}:
          {==}
        case Rp.KSkill{}:
          {==}
        case Rp.KSubagent{}:
          {==}
        case Rp.KFactory{}:
          {==}

def rpd.create(+c: Maybe<&2, Rp.Comp>, +t: Maybe<&2, String>) -> {[Some{Rp.slug(Maybe.default(&2, String, t, Rp.comp_name(Rp.comp_or_memory(c))), Rp.comp_name(Rp.comp_or_memory(c)))}] == [Some{RefinePlan.rs_slug(Maybe.default(&2, String, t, RefinePlan.rs_kind_name(c)), RefinePlan.rs_kind_name(c))}] : List<&2, Maybe<&2, String>>}:
  +K = RefinePlan.rs_kind_name(c)
  %Equal.sym(String, Rp.comp_name(Rp.comp_or_memory(c)), K, rpd.name(c)) : {[Some{Rp.slug(Maybe.default(&2, String, t, _), _)}] == [Some{RefinePlan.rs_slug(Maybe.default(&2, String, t, K), K)}] : List<&2, Maybe<&2, String>>}
  Equal.cong(String, List<&2, Maybe<&2, String>>, s => [Some{s}], Rp.slug(Maybe.default(&2, String, t, K), K), RefinePlan.rs_slug(Maybe.default(&2, String, t, K), K), PSlug.rps.slug(Maybe.default(&2, String, t, K), K))

def RefinePlan.refine_plan_id_create(c, t, content, p, a, ex, df, hd):
  rpd.create(c, t)
