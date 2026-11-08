# eukhe: the proof of LAW replace_replaced_exact
#
# PROOF of LAW replace_replaced_exact: by induction on the starts, from
# any running daemon (rre.go): a start counts as rp_replaces_spec
# (replace_replaces_exact), and the next daemon is rp_after_spec
# (replace_after_exact).

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace
import ./replace_replaces_exact.bend as PReplaceReplacesExact
import ./replace_after_exact.bend as PReplaceAfterExact

def rre.go(ss: List<&2, Rp.Start>, +d: Maybe<&2, Rp.Build>) -> {Rp.replaced.go(ss, d) == Replace.rp_replaced_spec.go(ss, d) : Nat}:
  match ss:
    case Nil{}:
      {==}
    case +s <> +rest:
      %rre.go(rest, Some{Replace.rp_after_spec(s, d)}) : {Rp.replaced.go(s <> rest, d) == Nat.add(Replace.rp_replaces_spec(s, d), _) : Nat}
      %Replace.replace_after_exact(s, d) : {Rp.replaced.go(s <> rest, d) == Nat.add(Replace.rp_replaces_spec(s, d), Rp.replaced.go(rest, Some{_})) : Nat}
      %Replace.replace_replaces_exact(s, d) : {Rp.replaced.go(s <> rest, d) == Nat.add(_, Rp.replaced.go(rest, Some{Rp.after(s, d)})) : Nat}
      {==}

def Replace.replace_replaced_exact(ss):
  rre.go(ss, None{})
