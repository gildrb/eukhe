# eukhe: the proof of LAW rmw_missing_is_empty
# A missing file and the empty document both write the edit applied to
# no entries.

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config

def Config.rmw_missing_is_empty(e):
  {==}
