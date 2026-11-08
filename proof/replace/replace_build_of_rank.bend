# eukhe: the proof of LAW replace_build_of_rank
# A build of v holds rank(v), which is rank_spec(v) (replace_rank_reads_semver).

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace
import ./replace_rank_reads_semver.bend as PReplaceRankReadsSemver

def Replace.replace_build_of_rank(v, i):
  %Replace.replace_rank_reads_semver(v) : {Rp.Build.of(v, i) == Rp.Build{_, i} : Rp.Build}
  {==}
