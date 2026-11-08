# eukhe: the proof of LAW replace_replaces_exact
#
# PROOF of LAW replace_replaces_exact: split the start and the daemon. No
# daemon: both are 0. A running b: the model counts its own verdict, which
# is verdict_spec(rel_spec(c, b), k) (replace_verdict_exact), and both
# sides count a Replace as 1 and a Keep as 0 (rre.put).

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace
import ./replace_verdict_exact.bend as PReplaceVerdictExact

def rre.put(v: Rp.Verdict) -> {Rp.replaces.put(v) == Replace.rp_verdict_count(v) : Nat}:
  match v:
    case Rp.Replace{}:
      {==}
    case Rp.Keep{r}:
      {==}

def Replace.replace_replaces_exact(s, d):
  match s:
    case Rp.Start{+c, +k}:
      match d:
        case None{}:
          {==}
        case Some{+b}:
          %Replace.replace_verdict_exact(c, b, k) : {Rp.replaces.put(Rp.verdict(c, b, k)) == Replace.rp_verdict_count(_) : Nat}
          rre.put(Rp.verdict(c, b, k))
