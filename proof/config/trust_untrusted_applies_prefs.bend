# eukhe: the proof of LAW trust_untrusted_applies_prefs
# The key's rule makes it a preference: an untrusted project admits it.

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config

def Config.trust_untrusted_applies_prefs(k, p, v, n, pref):
  %Equal.sym(Cf.Hit, Cf.classify(p), Cf.Hit{n, Cf.Proj{Cf.Pref{}}}, pref) : {(Cf.effective(Cf.Untrusted{}, Nil{}, Cf.item.of(Cf.Hit.scope(_), k, v, Nil{})), Cf.withheld.step(Cf.Untrusted{}, _, Nil{})) == ([Cf.Entry{k, v}], Nil{}) : List<&2, Cf.Entry> & List<&2, String>}
  {==}
