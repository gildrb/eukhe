# eukhe: the proof of LAW package_source_git_trims
#
# PROOF: the reader trims its text first; White_Space at both ends does
# not change the trimmed text (LA.psb.trim_pad).

import Base
import ../../bend/package_source.bend as Ps
import ../../bend/gateway_answer.bend as Ga
import ../../laws/package_source/model.bend as PackageSource
import ../base/staging.bend as LStg
import ./base.bend as LA

def PackageSource.package_source_git_trims(w1, b1, s, w2, b2):
  %Equal.sym(String, Ps.trim(String.append(w1, String.append(s, w2))), Ps.trim(s), LA.psb.trim_pad(w1, b1, s, w2, b2)) : {Ps.git.at(String.starts_with(_, "git:"), _) == Ps.git(s) : Ps.GitAns}
  {==}
