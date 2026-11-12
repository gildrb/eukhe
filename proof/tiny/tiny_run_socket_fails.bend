# eukhe: the proof of LAW tiny_run_socket_fails
#
# PROOF: each step computes: the phase's awaited ping decides on a
# failing socket without reading the tag.

import Base
import ../../bend/tiny.bend as Tn
import ../../laws/tiny/elect.bend as TinyElect

def TinyElect.tiny_run_socket_fails(m, g):
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, {==}))))))))
