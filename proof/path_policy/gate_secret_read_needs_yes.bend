# eukhe: the proof of LAW gate_secret_read_needs_yes

import Base
import ../../bend/path_policy.bend as Pp
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pp.gate_secret_read_needs_yes(c: Pp.Cls, a: Pp.Acc, +auto: List<&2, Nat>, +ans: Pp.Ans, s: {Pp.secret_read(c, a) == True{} : Bool}, ran: {Pp.runs(c, a, auto, ans) == True{} : Bool}) -> {Pp.Ans.yes(ans) == True{} : Bool}:
  match c:
    case Pp.Secret{}:
      match a:
        case Pp.Rd{}:
          ran
        case Pp.Ls{}:
          ran
        case Pp.Sr{h}:
          match h:
            case True{}:
              ran
            case False{}:
              ran
        case Pp.Wr{}:
          LA.pp.absurdF({Pp.Ans.yes(ans) == True{} : Bool}, s)
    case Pp.Inside{}:
      match a:
        case Pp.Rd{}:
          LA.pp.absurdF({Pp.Ans.yes(ans) == True{} : Bool}, s)
        case Pp.Ls{}:
          LA.pp.absurdF({Pp.Ans.yes(ans) == True{} : Bool}, s)
        case Pp.Sr{h}:
          match h:
            case True{}:
              ran
            case False{}:
              LA.pp.absurdF({Pp.Ans.yes(ans) == True{} : Bool}, s)
        case Pp.Wr{}:
          LA.pp.absurdF({Pp.Ans.yes(ans) == True{} : Bool}, s)
    case Pp.Outside{}:
      match a:
        case Pp.Rd{}:
          LA.pp.absurdF({Pp.Ans.yes(ans) == True{} : Bool}, s)
        case Pp.Ls{}:
          LA.pp.absurdF({Pp.Ans.yes(ans) == True{} : Bool}, s)
        case Pp.Sr{h}:
          match h:
            case True{}:
              ran
            case False{}:
              LA.pp.absurdF({Pp.Ans.yes(ans) == True{} : Bool}, s)
        case Pp.Wr{}:
          LA.pp.absurdF({Pp.Ans.yes(ans) == True{} : Bool}, s)
    case Pp.Protected{}:
      match a:
        case Pp.Rd{}:
          LA.pp.absurdF({Pp.Ans.yes(ans) == True{} : Bool}, s)
        case Pp.Ls{}:
          LA.pp.absurdF({Pp.Ans.yes(ans) == True{} : Bool}, s)
        case Pp.Sr{h}:
          match h:
            case True{}:
              ran
            case False{}:
              LA.pp.absurdF({Pp.Ans.yes(ans) == True{} : Bool}, s)
        case Pp.Wr{}:
          LA.pp.absurdF({Pp.Ans.yes(ans) == True{} : Bool}, s)

def Laws.gate_secret_read_needs_yes(c, a, auto, ans, s, ran):
  pp.gate_secret_read_needs_yes(c, a, auto, ans, s, ran)
