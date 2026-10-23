# eukhe: the proof of LAW wf_admitted_never_respawns

import Base
import ../../bend/workflow.bend as W
import ../../LAWS.bend as Laws

def pw.again(s: W.Sts) -> {W.again(s) == Laws.wf_again(s) : W.Admit}:
  match s:
    case W.Queued{}:
      {==}
    case W.Running{}:
      {==}
    case W.Finished{}:
      {==}
    case W.Erred{}:
      {==}
    case W.Cancelled{}:
      {==}
    case W.Cached{}:
      {==}

def pw.admitted(s: W.Sts, k: Nat, rs: List<&2, W.Row>, p: W.Pool) -> {W.admit(Some{s}, k, rs, p) == (Laws.wf_again(s), p) : W.Admit & W.Pool}:
  %pw.again(s) : {(W.again(s), p) == (_, p) : W.Admit & W.Pool}
  {==}

# ---- wire ----

# The proofs of LAWS.bend section wire are proof/wire.bend (imported as
# PWire): the sections after it use its Laws.wire_* fills and its lemmas
# PWire.wr_and_l, PWire.wr_and_r, PWire.wr_absurd, PWire.wn_and_intro.

def Laws.wf_admitted_never_respawns(s, k, rs, p):
  pw.admitted(s, k, rs, p)
