# eukhe: the proof of LAW tiny_run_shutdown_answered
#
# PROOF: each step computes: a shutdown's answer decides alone.

import Base
import ../../bend/tiny.bend as Tn
import ../../laws/tiny/elect.bend as TinyElect

def TinyElect.tiny_run_shutdown_answered(m):
  ({==}, ({==}, ({==}, {==})))
