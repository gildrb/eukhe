# eukhe: the proof of LAW glob_rules
#
# PROOF: rule by rule (gr.rules): the rule's patterns' alternatives are
# the spec's (gq.compile), and the search over the texts the spec's
# (gq.hit).

import Base
import ../../bend/ffi_glob.bend as FG
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/glob.bend as Glob
import ./base/ignore.bend as GR

def Glob.glob_rules(ks, o, ps, ss):
  GR.gr.rules(ks, o, ps, ss)
