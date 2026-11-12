# eukhe: the proof of LAW glob_ignore_pairs
#
# PROOF: the rule list pairs texts and codes in order and stops at the
# shorter list (GI.ig.irs_take).

import Base
import ../../bend/glob/queries.bend as GQuery
import ../../laws/glob.bend as Glob
import ./base/ignore.bend as GI

def Glob.glob_ignore_pairs(ps, cs, es):
  Equal.cong(List<&2, GQuery.IR>, List<&2, Bool>, z => GQuery.ignored.go(es, z), GQuery.irs(ps, cs, Nil{}), GQuery.irs(List.take(&2, String, ps, List.length(&2, Nat, cs)), List.take(&2, Nat, cs, List.length(&2, String, ps)), Nil{}), GI.ig.irs_take(ps, cs, Nil{}))
