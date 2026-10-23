# eukhe: the proof of LAW facts_bedrock_budget_oracle

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts.bend as Facts

def pf.facts_bedrock_budget_oracle(c: Fx.Customs, +l: Fx.Lv) -> {Fx.budget(c, Fx.budgets.shipped(), l) == Fx.budget.old(c, l) : Nat}:
  match l:
    case Fx.Minimal{}:
      {==}
    case Fx.Low{}:
      {==}
    case Fx.Medium{}:
      {==}
    case Fx.High{}:
      {==}

def Facts.facts_bedrock_budget_oracle(c, l):
  pf.facts_bedrock_budget_oracle(c, l)
