# eukhe: the proof of LAW replace_rank_reads_semver

import Base
import ../../laws/replace.bend as Replace
import ../base/replace.bend as LReplace

def Replace.replace_rank_reads_semver(s):
  LReplace.rk.rank(s)
