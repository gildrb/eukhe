# eukhe: the proof of LAW untrusted_changes_nothing_guarded

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../base/logic/bool.bend as LLogicBool
import ./base.bend as LA

# Trust
# -----

# LAW untrusted_changes_nothing_guarded
def pcf.untrusted_changes_nothing_guarded(+g: List<&2, Cf.Entry>, items: List<&2, Cf.Item>, +k: Nat, +h: {Cf.only_guarded(items, k) == True{} : Bool}) -> {Cf.lookup(Cf.effective(Cf.Untrusted{}, g, items), k) == Cf.lookup(g, k) : Maybe<&2, Nat>}:
  match items:
    case Nil{}:
      {==}
    case i <> +rest:
      match i:
        case Cf.Item{+j, kind, v}:
          match kind:
            case Cf.Pref{}:
              +ne = Bool.not(Nat.is_eq(j, k))
              +og = Cf.only_guarded(rest, k)
              +ejk = LLogicBool.ppr.not_t(Nat.is_eq(j, k), LLogicBool.ppr.and_l(ne, og, h))
              +later = Cf.lookup(Cf.effective(Cf.Untrusted{}, g, rest), k)
              %Equal.sym(Maybe<&2, Nat>, Cf.pick(Nat.is_eq(j, k), v, later), later, LA.pcf.pick_false(Nat.is_eq(j, k), v, later, ejk)) : {_ == Cf.lookup(g, k) : Maybe<&2, Nat>}
              pcf.untrusted_changes_nothing_guarded(g, rest, k, LLogicBool.ppr.and_r(ne, og, h))
            case Cf.Limit{}:
              pcf.untrusted_changes_nothing_guarded(g, rest, k, h)
            case Cf.Prompt{}:
              pcf.untrusted_changes_nothing_guarded(g, rest, k, h)
            case Cf.Credential{}:
              pcf.untrusted_changes_nothing_guarded(g, rest, k, h)

def Config.untrusted_changes_nothing_guarded(g, items, k, h):
  pcf.untrusted_changes_nothing_guarded(g, items, k, h)
