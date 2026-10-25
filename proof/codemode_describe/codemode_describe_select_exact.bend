# eukhe: the proof of LAW codemode_describe_select_exact

import Base
import ../../bend/codemode_describe.bend as Dsc
import ../../laws/codemode_describe.bend as CodemodeDescribe
import ./base.bend as LACd

# PROOF of LAW codemode_describe_select_exact: a model round over the queues still in is the spec's round over every group, flagged in or out (cdsel.round); so are the rounds from the first queues (cdsel.rounds, cdsel.select).

def CodemodeDescribe.codemode_describe_select_exact(gs, budget):
  LACd.cdsel.select(gs, budget)
