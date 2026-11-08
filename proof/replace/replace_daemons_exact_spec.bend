# eukhe: the proof of LAW replace_daemons_exact_spec
#
# PROOF of LAW replace_daemons_exact_spec: by induction on the starts, from any
# running daemon (rde.go): each daemon is rp_after_spec of its start
# (replace_after_exact_spec), threaded to the next start.

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace
import ./replace_after_exact_spec.bend as PReplaceAfterExact

def rde.go(ss: List<&2, Rp.Start>, +d: Maybe<&2, Rp.Build>) -> {Rp.trace.go(ss, d) == Replace.rp_daemons_spec.go(ss, d) : List<&2, Rp.Build>}:
  match ss:
    case Nil{}:
      {==}
    case +s <> +rest:
      %rde.go(rest, Some{Replace.rp_after_spec(s, d)}) : {Rp.trace.go(s <> rest, d) == Replace.rp_after_spec(s, d) <> _ : List<&2, Rp.Build>}
      Equal.cong(Rp.Build, List<&2, Rp.Build>, z => z <> Rp.trace.go(rest, Some{z}), Rp.after(s, d), Replace.rp_after_spec(s, d), Replace.replace_after_exact_spec(s, d))

def Replace.replace_daemons_exact_spec(ss):
  rde.go(ss, None{})
