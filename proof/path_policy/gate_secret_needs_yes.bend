# eukhe: the proof of LAW gate_secret_needs_yes
#
# PROOF: every access to a Secret path has the secret effect 6, which the
# auto test never grants, so the gate's verdict computes to the answer's
# yes test (split the access); a yes test that holds is a yes (pgs.yes).

import Base
import ../../bend/path_policy.bend as Pp
import ../../laws/path_policy/gate.bend as PathPolicyGate
import ./base.bend as LA

# the yes test holds only for a yes
def pgs.yes(ans: Pp.Ans, ran: {Pp.Ans.yes(ans) == True{} : Bool}) -> {ans == Pp.Yes{} : Pp.Ans}:
  match ans:
    case Pp.Yes{}:
      {==}
    case Pp.No{}:
      LA.pp.absurdF({Pp.No{} == Pp.Yes{} : Pp.Ans}, ran)
    case Pp.Gone{}:
      LA.pp.absurdF({Pp.Gone{} == Pp.Yes{} : Pp.Ans}, ran)

def PathPolicyGate.gate_secret_needs_yes(a, auto, ans, ran):
  match a:
    case Pp.Rd{}:
      pgs.yes(ans, ran)
    case Pp.Ls{}:
      pgs.yes(ans, ran)
    case Pp.Sr{h}:
      match h:
        case True{}:
          pgs.yes(ans, ran)
        case False{}:
          pgs.yes(ans, ran)
    case Pp.Wr{}:
      pgs.yes(ans, ran)
