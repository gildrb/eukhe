# eukhe: the proof of LAW replace_after_exact
#
# PROOF of LAW replace_after_exact: with no daemon both sides are the
# client's build; else the model's verdict is verdict_spec(rel_spec(c, b), k)
# (replace_verdict_exact), and after.put picks as rp_after_pick (rae.pick).

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace
import ./replace_verdict_exact.bend as PReplaceVerdictExact

def rae.pick(v: Rp.Verdict, -c: Rp.Build, -b: Rp.Build) -> {Rp.after.put(v, c, b) == Replace.rp_after_pick(v, c, b) : Rp.Build}:
  match v:
    case Rp.Replace{}:
      {==}
    case Rp.Keep{r}:
      {==}

def rae.go(s: Rp.Start, d: Maybe<&2, Rp.Build>) -> {Rp.after(s, d) == Replace.rp_after_spec(s, d) : Rp.Build}:
  match s:
    case Rp.Start{+c, +k}:
      match d:
        case None{}:
          {==}
        case Some{+b}:
          %Replace.replace_verdict_exact(c, b, k) : {Rp.after.put(Rp.verdict(c, b, k), c, b) == Replace.rp_after_pick(_, c, b) : Rp.Build}
          rae.pick(Rp.verdict(c, b, k), c, b)

def Replace.replace_after_exact(s, d):
  rae.go(s, d)
