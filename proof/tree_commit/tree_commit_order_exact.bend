# eukhe: the proof of LAW tree_commit_order_exact

import Base
import ../../bend/tree_commit.bend as Tc
import ../../bend/ffi_tree_commit.bend as FTc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/tree_commit.bend as TreeCommit
import ./base.bend as LATreeCommit

# PROOF of LAW tree_commit_order_exact: with no mark the waiting Puts are all the Puts (tc.T_none); the code's rounds are the spec's (tc.CR: each round answers one spec pass, tc.R).

def TreeCommit.tree_commit_order_exact(cs):
  %LATreeCommit.tc.T_none(cs, 0n) : {Tc.order(cs) == List.append(&2, Tc.Res, TreeCommit.rounds_spec(List.length(&2, Tc.Ch, cs), cs, [], _), TreeCommit.dels_spec(cs, 0n)) : List<&2, Tc.Res>}
  LATreeCommit.tc.CR(List.length(&2, Tc.Ch, cs), cs, [], [])
