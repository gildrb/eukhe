# eukhe: the proof of LAW replace_replaced_exact_spec
#
# PROOF of LAW replace_replaced_exact_spec: by induction on the starts, from
# any running daemon (rre.go): a start counts as rp_replaces_spec (rre.one:
# the model counts its own verdict, which is verdict_spec(rel_spec(c, b), k)
# by replace_verdict_exact, and both count a Replace as 1 and a Keep as 0),
# and the next daemon is rp_after_spec (replace_after_exact_spec).

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace
import ./replace_verdict_exact.bend as PReplaceVerdictExact
import ./replace_after_exact_spec.bend as PReplaceAfterExact

def rre.put(v: Rp.Verdict) -> {Rp.replaces.put(v) == Replace.rp_verdict_count(v) : Nat}:
  match v:
    case Rp.Replace{}:
      {==}
    case Rp.Keep{r}:
      {==}

# one start counts as rp_replaces_spec
def rre.one(+s: Rp.Start, +d: Maybe<&2, Rp.Build>) -> {Rp.replaces(s, d) == Replace.rp_replaces_spec(s, d) : Nat}:
  match s:
    case Rp.Start{+c, +k}:
      match d:
        case None{}:
          {==}
        case Some{+b}:
          %Replace.replace_verdict_exact(c, b, k) : {Rp.replaces.put(Rp.verdict(c, b, k)) == Replace.rp_verdict_count(_) : Nat}
          rre.put(Rp.verdict(c, b, k))

def rre.go(ss: List<&2, Rp.Start>, +d: Maybe<&2, Rp.Build>) -> {Rp.replaced.go(ss, d) == Replace.rp_replaced_spec.go(ss, d) : Nat}:
  match ss:
    case Nil{}:
      {==}
    case +s <> +rest:
      %rre.go(rest, Some{Replace.rp_after_spec(s, d)}) : {Rp.replaced.go(s <> rest, d) == Nat.add(Replace.rp_replaces_spec(s, d), _) : Nat}
      %Replace.replace_after_exact_spec(s, d) : {Rp.replaced.go(s <> rest, d) == Nat.add(Replace.rp_replaces_spec(s, d), Rp.replaced.go(rest, Some{_})) : Nat}
      %rre.one(s, d) : {Rp.replaced.go(s <> rest, d) == Nat.add(_, Rp.replaced.go(rest, Some{Rp.after(s, d)})) : Nat}
      {==}

def Replace.replace_replaced_exact_spec(ss):
  rre.go(ss, None{})
