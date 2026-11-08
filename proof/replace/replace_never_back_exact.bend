# eukhe: the proof of LAW replace_never_back_exact

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace
import ./base.bend as LA

# (D1) replace_never_back_exact: by induction on the builds, from any seen:
# each check is rp_not_below's (LA.st.not_below_exact)

def st.never_back_go(xs: List<&2, Rp.Build>, +seen: List<&2, Rp.Build>) -> {Rp.never_back.go(xs, seen) == Replace.rp_never_back.go(xs, seen) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      %LA.st.not_below_exact(x, seen) : {Bool.and(Rp.not_below(seen, x), Rp.never_back.go(t, x <> seen)) == Bool.and(_, Replace.rp_never_back.go(t, x <> seen)) : Bool}
      %st.never_back_go(t, x <> seen) : {Bool.and(Rp.not_below(seen, x), Rp.never_back.go(t, x <> seen)) == Bool.and(Rp.not_below(seen, x), _) : Bool}
      {==}

def Replace.replace_never_back_exact(xs):
  st.never_back_go(xs, Nil{})
