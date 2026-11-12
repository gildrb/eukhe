# eukhe: the proof of LAW rmw_missing_writes_edit
# A set over the empty document finds no entry of its key and puts the
# one entry last; a delete of the empty document is empty.

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config

def Config.rmw_missing_writes_edit(k, v):
  ({==}, {==})
