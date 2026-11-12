# eukhe: the proof of LAW package_source_git_safe
#
# PROOF: every git answer is a checked candidate; the check accepts one
# only when the code finds no flaw, which is exactly the laws' ps_git_ok
# (LA.psb.flaws: per part, LA.psb.rel / LA.psb.arg / LA.psb.auth); so the
# accepted source answered is safe (LA.psb.git).

import Base
import ../../bend/package_source.bend as Ps
import ../../bend/gateway_answer.bend as Ga
import ../../laws/package_source/model.bend as PackageSource
import ../base/staging.bend as LStg
import ./base.bend as LA

def PackageSource.package_source_git_safe(s, g, got):
  %got : {LA.psb.ans_ok(_) == True{} : Bool}
  LA.psb.git(s)
