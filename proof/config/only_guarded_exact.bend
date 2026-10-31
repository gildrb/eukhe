# eukhe: the proof of LAW only_guarded_exact

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../../spec/settings/config_rules.bend as CR

def po.at(+j: Nat, c: Cf.Class, +k: Nat) -> {Cf.guarded_at(j, c, k) == Bool.not(Bool.and(CR.cr_pref(c), Nat.is_eq(j, k))) : Bool}:
  match c:
    case Cf.Pref{}:
      {==}
    case Cf.Limit{}:
      {==}
    case Cf.Prompt{}:
      {==}
    case Cf.Credential{}:
      {==}
    case Cf.Code{}:
      {==}

def Config.only_guarded_exact(items, k):
  match items:
    case Nil{}:
      {==}
    case i <> +rest:
      match i:
        case Cf.Item{+j, +c, v}:
          %po.at(j, c, k) : {Bool.and(Cf.guarded_at(j, c, k), Cf.only_guarded(rest, k)) == Bool.and(_, CR.cr_only_guarded(rest, k)) : Bool}
          %Config.only_guarded_exact(rest, k) : {Bool.and(Cf.guarded_at(j, c, k), Cf.only_guarded(rest, k)) == Bool.and(Cf.guarded_at(j, c, k), _) : Bool}
          {==}
