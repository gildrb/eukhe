# eukhe: the proof of LAW move_has_only_named
#
# PROOF: induction on the files: the first file whose name tests equal is named n (dcl.has_only).

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit.bend as DocCommit
import ./base.bend as LA

def DocCommit.move_has_only_named(n, es, taken):
  LA.dcl.has_only(n, es, taken)
