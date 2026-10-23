# eukhe: the proof of LAW kernel_session_never_downloads

import Base
import ../../bend/kernel_local.bend as KL
import ../../LAWS.bend as Laws

# The setup
# ---------

def pk.session_never_downloads(f: KL.Found) -> {KL.acts.fetching(KL.plan(f, KL.Local{})) == False{} : Bool}:
  match f:
    case KL.Current{}:
      {==}
    case KL.Skills{}:
      {==}
    case KL.Stale{}:
      {==}

# (K1) The kernel environment is local

def Laws.kernel_session_never_downloads(f):
  pk.session_never_downloads(f)
