# eukhe: the proof of LAW save_ignores_loaded
# The setter reads only the disk read.

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config

def Config.save_ignores_loaded(l1, l2, r, k, v):
  {==}
