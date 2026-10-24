# eukhe: the proof of LAW skill_diag_kinds

import Base
import ../../bend/skill_load.bend as Sk
import ../../laws/skill_load.bend as SkillLoad

def sdk.kinds(cs: List<&2, Sk.Cand>) -> {Sk.diags(cs) == SkillLoad.diags_spec(cs) : List<&2, Sk.Diag>}:
  match cs:
    case Nil{}:
      {==}
    case Sk.Cand{p, o} <> rest:
      match o:
        case Sk.Good{}:
          sdk.kinds(rest)
        case Sk.Unreadable{}:
          %sdk.kinds(rest) : {Sk.Diag{p, 0n} <> Sk.diags(rest) == Sk.Diag{p, 0n} <> _ : List<&2, Sk.Diag>}
          {==}
        case Sk.Malformed{}:
          %sdk.kinds(rest) : {Sk.Diag{p, 1n} <> Sk.diags(rest) == Sk.Diag{p, 1n} <> _ : List<&2, Sk.Diag>}
          {==}
        case Sk.Incomplete{}:
          %sdk.kinds(rest) : {Sk.Diag{p, 2n} <> Sk.diags(rest) == Sk.Diag{p, 2n} <> _ : List<&2, Sk.Diag>}
          {==}

def SkillLoad.skill_diag_kinds(cs):
  sdk.kinds(cs)
