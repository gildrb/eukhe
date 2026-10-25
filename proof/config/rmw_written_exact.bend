# eukhe: the proof of LAW rmw_written_exact
# The model's set and delete are the laws' restatements, entry by entry
# (inductions on the document); whether the key is there is the same test.

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ./base/config.bend as LA

def Config.rmw_written_exact(d, e):
  match e:
    case Cf.Set{+k, +v}:
      %LA.pcf.set_spec(d, k, v) : {Cf.Wrote{Cf.set(d, k, v)} == Cf.Wrote{_} : Cf.Write}
      {==}
    case Cf.Del{+k}:
      %LA.pcf.wx.del(d, k) : {Cf.Wrote{Cf.del(d, k)} == Cf.Wrote{_} : Cf.Write}
      {==}
