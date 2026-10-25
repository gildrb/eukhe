# eukhe: the proof of LAW tree_commit_example

import Base
import ../../bend/tree_commit.bend as Tc
import ../../bend/ffi_tree_commit.bend as FTc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/tree_commit.bend as TreeCommit
import ./base.bend as LATreeCommit

# PROOF of LAW tree_commit_example: each anchor computes.

def TreeCommit.tree_commit_example():
  ({==}, ({==}, ({==}, {==})))
