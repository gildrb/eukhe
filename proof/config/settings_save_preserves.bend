# eukhe: the proof of LAW settings_save_preserves

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config

# LAW settings_save_preserves
def pcf.settings_save_preserves(loaded: List<&2, Cf.Entry>, d: List<&2, Cf.Entry>, +k: Nat, v: Nat) -> {Cf.save(loaded, Cf.Parsed{d}, k, v) == Cf.Wrote{Cf.set(d, k, v)} : Cf.Write}:
  {==}

def Config.settings_save_preserves(loaded, d, k, v):
  pcf.settings_save_preserves(loaded, d, k, v)
