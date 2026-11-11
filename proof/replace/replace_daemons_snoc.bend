# eukhe: the proof of LAW replace_daemons_snoc: by induction on the starts,
# from any running daemon d (rds.go): the trace of no start and one more is
# the daemon after it on d; a start before them puts its daemon first and
# hands it on as the running one, which is the last daemon so far

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace

def rds.go(ss: List<&2, Rp.Start>, +s: Rp.Start, +d: Maybe<&2, Rp.Build>) -> {Rp.trace.go(List.append(&2, Rp.Start, ss, [s]), d) == List.append(&2, Rp.Build, Rp.trace.go(ss, d), [Rp.after(s, Replace.rp_last.go(Rp.trace.go(ss, d), d))]) : List<&2, Rp.Build>}:
  match ss:
    case Nil{}:
      {==}
    case +x <> +rest:
      Equal.cong(List<&2, Rp.Build>, List<&2, Rp.Build>, z => Rp.after(x, d) <> z,
        Rp.trace.go(List.append(&2, Rp.Start, rest, [s]), Some{Rp.after(x, d)}),
        List.append(&2, Rp.Build, Rp.trace.go(rest, Some{Rp.after(x, d)}), [Rp.after(s, Replace.rp_last.go(Rp.trace.go(rest, Some{Rp.after(x, d)}), Some{Rp.after(x, d)}))]),
        rds.go(rest, s, Some{Rp.after(x, d)}))

def Replace.replace_daemons_snoc(ss, s):
  rds.go(ss, s, None{})
