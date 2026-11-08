# eukhe: the proof of LAW command_resolve_spec
#
# PROOF of LAW command_resolve_spec: the model's walk is the spec's, step
# by step (its search is cmd_named: nm_search; its other moves are the
# spec's), and its finish is the spec's (kids.any is cmd_has_kid, join is
# cmd_render): proof/command/base/whole.bend.

import Base
import ../../laws/command/whole.bend as CommandWhole
import ./base/whole.bend as LACommandWhole

def CommandWhole.command_resolve_spec(t, line):
  LACommandWhole.pwh.resolve(t, line)
