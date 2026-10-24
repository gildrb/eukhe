# eukhe: the proof of LAW skill_loaded_exact

import Base
import ../../bend/skill_load.bend as Sk
import ../../laws/skill_load.bend as SkillLoad

def sle.loaded(cs: List<&2, Sk.Cand>) -> {Sk.loaded(cs) == SkillLoad.loaded_spec(cs) : List<&2, Nat>}:
  match cs:
    case Nil{}:
      {==}
    case Sk.Cand{p, o} <> rest:
      match o:
        case Sk.Good{}:
          %sle.loaded(rest) : {p <> Sk.loaded(rest) == p <> _ : List<&2, Nat>}
          {==}
        case Sk.Unreadable{}:
          sle.loaded(rest)
        case Sk.Malformed{}:
          sle.loaded(rest)
        case Sk.Incomplete{}:
          sle.loaded(rest)

def SkillLoad.skill_loaded_exact(cs):
  sle.loaded(cs)
