# eukhe: the proof of LAW env_terms_exact

import Base
import ../../bend/child_env.bend as Env
import ../../bend/ffi_child_env.bend as FEnv
import ../../bend/wire.bend as Wr
import ../../laws/child_env.bend as ChildEnv
import ./base/spec.bend as LS

def ChildEnv.env_terms_exact(reg, ns, n, base, over, v):
  (LS.pcs.cred(reg, n), (LS.pcs.registered(reg, n), (LS.pcs.listed(ns, n), (LS.pcs.merge(base, over), LS.pcs.in(v, over)))))
