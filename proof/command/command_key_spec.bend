# eukhe: the proof of LAW command_key_spec
#
# PROOF of LAW command_key_spec: the model cuts and walks the words as the
# spec does (pwh.cut, pwh.walk); at the root or a walked path its row is
# cmd_key_at's (nm_key_row), anywhere else its key is cmd_key_bare's
# (nm_bare).

import Base
import ../../laws/command/whole.bend as CommandWhole
import ./base/whole.bend as LACommandWhole

def CommandWhole.command_key_spec(t, line, sel, k):
  LACommandWhole.pwh.key(t, line, sel, k)
