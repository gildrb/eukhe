# eukhe: the proof of LAW log_commit_storage
#
# The storage a commit leaves does not depend on the sidecars: by fsync,
# both sides compute.

import Base
import ../../bend/log.bend as Lr
import ../../laws/log.bend as Log

def Log.log_commit_storage(fsync, main, stamp, ds):
  match fsync:
    case True{}:
      {==}
    case False{}:
      {==}
