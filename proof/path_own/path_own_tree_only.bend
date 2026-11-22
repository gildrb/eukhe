# eukhe: the proof of LAW path_own_tree_only
#
# PROOF: Own means the rule names the path (LA.po.hit): its path is at or
# above it, so a suffix of it (PPathInsideNeedsRoot.pin.usplit).

import Base
import ../../bend/path_policy.bend as Pp
import ../../laws/path_own.bend as PathOwn
import ../path_policy/path_inside_needs_root.bend as PPathInsideNeedsRoot
import ./base.bend as LA

def PathOwn.path_own_tree_only(p, at, c, own):
  PPathInsideNeedsRoot.pin.usplit(p, at)(LA.po.hit(Pp.under(p, at), c, own))
