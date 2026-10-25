# eukhe: the proof of LAW glob_groups
#
# PROOF: the patterns' alternatives are the spec's (gq.compile), and each group's search the spec's (gq.groups, gq.hit).

import Base
import ../../bend/glob.bend as G
import ../../bend/ffi_glob.bend as FG
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/glob.bend as Glob
import ./base/query.bend as GQ

def Glob.glob_groups(o, ps, ss, ks):
  %Equal.sym(List<&2, List<&2, G.It>>, G.compile(o, ps), Glob.sp_compile(o, ps), GQ.gq.compile(o, ps)) : {G.groups(ks, _, ss) == Glob.sp_groups(ks, Glob.sp_compile(o, ps), ss) : List<&2, Bool>}
  GQ.gq.groups(ks, Glob.sp_compile(o, ps), ss)
