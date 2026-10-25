# eukhe: the proof of LAW glob_ignored
#
# PROOF: the code's rule list is the spec's pairs, each made a rule
# (gi2.irs); rule by rule, code by code, the decision is the spec's
# (gi2.rule: a glob rule's match by gi2.gh, the prefix rule by its test,
# an unknown code decides nothing); entry by entry, the path and kind are
# the spec's (gi2.split).

import Base
import ../../bend/glob.bend as G
import ../../bend/ffi_glob.bend as FG
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/glob.bend as Glob
import ./base/ignore.bend as GR

def Glob.glob_ignored(ps, cs, es):
  GR.gi2.ignored(ps, cs, es)
