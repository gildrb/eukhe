# eukhe: the proof of LAW path_real_dots_at_root
#
# PROOF: `..` and `.` meet no link, and the parent of `/` is `/`: both
# walks reduce to the walk of the rest from `/`.

import Base
import ../../laws/path_policy.bend as PathPolicy

def PathPolicy.path_real_dots_at_root(ls, segs):
  {==}
