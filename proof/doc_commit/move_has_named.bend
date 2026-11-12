# eukhe: the proof of LAW move_has_named
#
# PROOF: induction on the files before it (dcl.has_at).

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit.bend as DocCommit
import ./base.bend as LA

def DocCommit.move_has_named(pre, n, b, post):
  LA.dcl.has_at(pre, n, b, post)
