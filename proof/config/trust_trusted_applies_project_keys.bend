# eukhe: the proof of LAW trust_trusted_applies_project_keys
# A trusted project admits every class.

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config

def Config.trust_trusted_applies_project_keys(k, p, v, n, c, at):
  %Equal.sym(Cf.Hit, Cf.classify(p), Cf.Hit{n, Cf.Proj{c}}, at) : {(Cf.effective(Cf.Trusted{}, Nil{}, Cf.item.of(Cf.Hit.scope(_), k, v, Nil{})), Cf.withheld.step(Cf.Trusted{}, _, Nil{})) == ([Cf.Entry{k, v}], Nil{}) : List<&2, Cf.Entry> & List<&2, String>}
  {==}
