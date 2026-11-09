# eukhe: the proof of LAW trust_untrusted_withholds_others
# The key's rule makes it something other than a preference: an
# untrusted project does not admit it, and the warning adds its name.

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../base/logic/logic.bend as LLogicLogic

def pwo.adm(c: Cf.Class, other: {Config.cf_is_pref(c) == False{} : Bool}) -> {Cf.admits(Cf.Untrusted{}, c) == False{} : Bool}:
  match c:
    case Cf.Pref{}:
      LLogicLogic.ppr.absurd({True{} == False{} : Bool}, other)
    case Cf.Limit{}:
      {==}
    case Cf.Prompt{}:
      {==}
    case Cf.Credential{}:
      {==}
    case Cf.Code{}:
      {==}

def Config.trust_untrusted_withholds_others(k, p, v, n, c, other, at):
  %Equal.sym(Cf.Hit, Cf.classify(p), Cf.Hit{n, Cf.Proj{c}}, at) : {(Cf.effective(Cf.Untrusted{}, Nil{}, Cf.item.of(Cf.Hit.scope(_), k, v, Nil{})), Cf.withheld.step(Cf.Untrusted{}, _, Nil{})) == (Nil{}, [n]) : List<&2, Cf.Entry> & List<&2, String>}
  %Equal.sym(Bool, Cf.admits(Cf.Untrusted{}, c), False{}, pwo.adm(c, other)) : {(Cf.guard(_, Cf.Entry{k, v}, Nil{}), Cf.withheld.add(_, n, Nil{})) == (Nil{}, [n]) : List<&2, Cf.Entry> & List<&2, String>}
  {==}
