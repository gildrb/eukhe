# eukhe: the proof of LAW save_exact
# A setter is the writer of a set (Cf.save is Cf.rmw of Set): a missing
# file and a broken read compute; a parsed one is set_exact.

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../../spec/config_rules.bend as CR
import ./base/config.bend as LA

def Config.save_exact(loaded, r, k, v):
  match r:
    case Cf.Missing{}:
      {==}
    case Cf.Parsed{+d}:
      %LA.pcf.set_spec(d, k, v) : {Cf.Wrote{Cf.set(d, k, v)} == Cf.Wrote{_} : Cf.Write}
      {==}
    case Cf.Broken{}:
      {==}
