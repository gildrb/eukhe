# eukhe: the proof of LAW replace_not_below_exact

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace
import ./base.bend as LA

# (D1) replace_not_below_exact: by induction on seen; each rank compare is
# rank_below's (LA.rk.lt_spec)

def Replace.replace_not_below_exact(seen, b):
  LA.st.not_below_exact(b, seen)
