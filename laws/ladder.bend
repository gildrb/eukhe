# LAWS (S6.9): the thinking ladder of a model is rulebook data. Each law
# is an open claim about the model in bend/infer.bend section 6;
# PROOF.bend proves them (as Ladder.<law>) with the lemmas of
# bend/proof_quirks.bend.

import Base
import ../bend/infer.bend as If
import ../bend/effort.bend as Ef

# (S6.9) The thinking ladder
# --------------------------
# docs/inference.md S6.9 and S10 (the ladder 0), the model in
# bend/infer.bend section 6. Every input is free: any explicit map, any
# rulebook ladder, any default ladders, any level.

# LAW: a model's explicit thinking-level map is its chosen ladder, over
# any ladder of the rulebook
law quirk_ladder_explicit_first:
  for +e: Ef.LvMap
  for +rule: Maybe<&2, Ef.LvMap>
  {If.lad.chosen(Some{e}, rule) == e : Ef.LvMap}

# LAW: with no explicit map, the rulebook's ladder is the chosen ladder
law quirk_ladder_rule_second:
  for +l: Ef.LvMap
  {If.lad.chosen(None{}, Some{l}) == l : Ef.LvMap}

# LAW: with no explicit map and no rulebook ladder, the chosen ladder has
# no entry: the default ladder gives every level
law quirk_ladder_default_last:
  {If.lad.chosen(None{}, None{}) == Ef.LvMap.none() : Ef.LvMap}

# LAW: a reasoning model offers a level exactly when its chosen ladder
# gives the level a wire string, or gives it no entry and the default
# ladder lists it; no other path offers a level
law quirk_ladder_offered_exact:
  for +explicit: Maybe<&2, Ef.LvMap>
  for +rule: Maybe<&2, Ef.LvMap>
  for +d: If.Defaults
  for +l: Ef.Lv
  {Ef.has(If.lad.offered(True{}, explicit, rule, d), l) == If.lad.keep(l, Ef.entry(l, If.lad.chosen(explicit, rule)), If.Defaults.reasoning(d)) : Bool}

# LAW: a model without reasoning offers exactly the levels of the plain
# default ladder, whatever its maps
law quirk_ladder_plain_exact:
  for +explicit: Maybe<&2, Ef.LvMap>
  for +rule: Maybe<&2, Ef.LvMap>
  for +d: If.Defaults
  for +l: Ef.Lv
  {Ef.has(If.lad.offered(False{}, explicit, rule, d), l) == Ef.has(If.Defaults.plain(d), l) : Bool}

# LAW: with the shipped default ladders, the levels a model offers are the
# S10 ladder of its chosen map, so every law of S10 holds for them
law quirk_ladder_shipped_is_s10:
  for r: Bool
  for +map: Ef.LvMap
  {If.lad.offered.of(r, map, If.lad.shipped()) == Ef.offered(Ef.Mdl{r, map}) : List<&2, Ef.Lv>}
