# eukhe: the proof of LAW replace_daemons_length: by induction on the
# starts, from any running daemon (rdl.go): each start adds one daemon

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace

def rdl.go(ss: List<&2, Rp.Start>, +d: Maybe<&2, Rp.Build>) -> {List.length(&2, Rp.Build, Rp.trace.go(ss, d)) == List.length(&2, Rp.Start, ss) : Nat}:
  match ss:
    case Nil{}:
      {==}
    case +x <> +rest:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Rp.Build, Rp.trace.go(rest, Some{Rp.after(x, d)})), List.length(&2, Rp.Start, rest), rdl.go(rest, Some{Rp.after(x, d)}))

def Replace.replace_daemons_length(ss):
  rdl.go(ss, None{})
