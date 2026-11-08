# eukhe: the proof of LAW replace_daemons_exact

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace
import ./base.bend as LA

# (D1) replace_daemons_exact: by induction on the starts, from any daemon:
# each step's daemon is rp_after's (LA.st.after_exact)

def st.trace_go(ss: List<&2, Rp.Start>, +d: Maybe<&2, Rp.Build>) -> {Rp.trace.go(ss, d) == Replace.rp_trace.go(ss, d) : List<&2, Rp.Build>}:
  match ss:
    case Nil{}:
      {==}
    case +s <> rest:
      %LA.st.after_exact(s, d) : {Rp.after(s, d) <> Rp.trace.go(rest, Some{Rp.after(s, d)}) == _ <> Replace.rp_trace.go(rest, Some{_}) : List<&2, Rp.Build>}
      %st.trace_go(rest, Some{Rp.after(s, d)}) : {Rp.after(s, d) <> Rp.trace.go(rest, Some{Rp.after(s, d)}) == Rp.after(s, d) <> _ : List<&2, Rp.Build>}
      {==}

def Replace.replace_daemons_exact(ss):
  st.trace_go(ss, None{})
