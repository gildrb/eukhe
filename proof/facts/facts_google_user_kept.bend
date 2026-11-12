# eukhe: the proof of LAW facts_google_user_kept
#
# PROOF: the rule is ordered (LA.fg.tokens), the user's budget is the
# model's (LA.fg.at), and a budget inside the range is held as it is
# (LA.fg.kept).

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts/model.bend as Facts
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ./base.bend as LA

def Facts.facts_google_user_kept(mi, lo, me, hi, c, l, n, ok, u, above, below):
  Equal.trans(Fx.GB, Fx.gbudget(Some{Fx.Budgets{mi, lo, me, hi}}, c, l), Fx.Tokens{Fx.clamp(n, mi, hi)}, Fx.Tokens{n}, LA.fg.user(mi, lo, me, hi, c, l, n, ok, u), LA.fg.tok(Fx.clamp(n, mi, hi), n, LA.fg.kept(n, mi, hi, above, below)))
