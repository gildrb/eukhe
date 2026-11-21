# eukhe: the proof of LAW path_own_dir_only
#
# PROOF: Own means the rule names the path (LA.po.hit): it is the
# directory or the directory is its parent, so it is k ++ p with at most
# one name k (PPathProtectedHasCause.phc.dir).

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_own.bend as PathOwn
import ../path_policy/path_protected_has_cause.bend as PPathProtectedHasCause
import ./base.bend as LA

def PathOwn.path_own_dir_only(p, at, c, own):
  PPathProtectedHasCause.phc.dir(at, p, LA.po.hit(Bool.or(Tl.ids.eq(at, p), Pp.parent_is(at, p)), c, own))
