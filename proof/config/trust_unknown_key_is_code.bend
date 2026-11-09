# eukhe: the proof of LAW trust_unknown_key_is_code
# An induction on the table: no rule's path starts with the key's first
# name, so none is a prefix of the key's path.

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../base/logic/logic.bend as LLogicLogic
import ../base/logic/bool.bend as LLogicBool

def puk.go(rs: List<&2, Cf.Rule>, +x: String, +r: List<&2, String>, +none: {Config.cf_no_rule_starts(rs, x) == True{} : Bool}) -> {Cf.classify.go(rs, x <> r) == Cf.Hit{x, Cf.Proj{Cf.Code{}}} : Cf.Hit}:
  match rs:
    case Nil{}:
      {==}
    case u <> +t:
      match u:
        case Cf.Rule{q, s}:
          match q:
            case Nil{}:
              LLogicLogic.ppr.absurdF({Cf.classify.go(Cf.Rule{Nil{}, s} <> t, x <> r) == Cf.Hit{x, Cf.Proj{Cf.Code{}}} : Cf.Hit}, none)
            case +y <> +ys:
              +hd = LLogicBool.ppr.and_l(Bool.not(String.eq(y, x)), Config.cf_no_rule_starts(t, x), none)
              +tl = LLogicBool.ppr.and_r(Bool.not(String.eq(y, x)), Config.cf_no_rule_starts(t, x), none)
              %Equal.sym(Bool, String.eq(y, x), False{}, LLogicBool.ppr.not_t(String.eq(y, x), hd)) : {Cf.classify.pick(Bool.and(_, Cf.prefix(ys, r)), y <> ys, s, Cf.classify.go(t, x <> r)) == Cf.Hit{x, Cf.Proj{Cf.Code{}}} : Cf.Hit}
              puk.go(t, x, r, tl)

def Config.trust_unknown_key_is_code(x, r, none):
  puk.go(Cf.rules(), x, r, none)
