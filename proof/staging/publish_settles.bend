# eukhe: the proof of LAW publish_settles

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging
import ./base.bend as LA

def Staging.publish_settles(b):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}
