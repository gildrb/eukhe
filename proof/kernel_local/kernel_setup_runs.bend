# eukhe: the proof of LAW kernel_setup_runs

import Base
import ../../bend/kernel_local.bend as KL
import ../../LAWS.bend as Laws

def pk.setup_runs(f: KL.Found, s: KL.Setup) -> {KL.acts.runs(KL.plan(f, s)) == True{} : Bool}:
  match f s:
    case KL.Current{} KL.Local{}:
      {==}
    case KL.Current{} KL.Install{}:
      {==}
    case KL.Skills{} KL.Local{}:
      {==}
    case KL.Skills{} KL.Install{}:
      {==}
    case KL.Stale{} KL.Local{}:
      {==}
    case KL.Stale{} KL.Install{}:
      {==}

def Laws.kernel_setup_runs(f, s):
  pk.setup_runs(f, s)
