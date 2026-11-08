# eukhe: the proof of LAW replace_after_exact

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace
import ./base.bend as LA

# (D1) replace_after_exact: the verdict is verdict_spec of rel_spec
# (LA.rk.relation_exact), and each verdict picks the build rp_after picks
# (LA.st.after_put)

def Replace.replace_after_exact(s, d):
  LA.st.after_exact(s, d)
