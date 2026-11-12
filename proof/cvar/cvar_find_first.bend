# eukhe: the proof of LAW cvar_find_first
# Induction on pre: each declaration of pre has another id, so the lookup
# passes it; at d the test is the id's own (LR.rs.find_first).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/resolution.bend as Cvar
import ./base/resolve.bend as LR

def Cvar.cvar_find_first(pre, d, post, fresh):
  LR.rs.find_first(pre, Cvar.spec_id(d), d, post, {==}, fresh)
