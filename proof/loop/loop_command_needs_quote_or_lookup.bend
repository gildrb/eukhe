# eukhe: the proof of LAW loop_command_needs_quote_or_lookup
#
# PROOF: every row computes: Lp.classify matches quoted, then (unquoted)
# found, then the polarity, and each side is the same command.

import Base
import ../../laws/loop/model.bend as Loop

def Loop.loop_command_needs_quote_or_lookup(w, r, f):
  ({==}, {==}, {==}, {==})
