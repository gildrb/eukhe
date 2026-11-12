# eukhe: the proof of LAW trust_global_only_never_applies
# A global-only key is no item, and no trust applies it.

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config

def Config.trust_global_only_never_applies(t, k, p, v, n, at):
  %Equal.sym(Cf.Hit, Cf.classify(p), Cf.Hit{n, Cf.GlobalOnly{}}, at) : {(Cf.effective(t, Nil{}, Cf.item.of(Cf.Hit.scope(_), k, v, Nil{})), Cf.withheld.step(t, _, Nil{})) == (Nil{}, [n]) : List<&2, Cf.Entry> & List<&2, String>}
  {==}
