# eukhe: the proof of LAW replace_rank_reads_semver

import Base
import ../../laws/replace.bend as Replace
import ../base.bend as L

def Replace.replace_rank_reads_semver(s):
  L.rk.rank(s)
