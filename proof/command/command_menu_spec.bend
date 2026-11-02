# eukhe: the proof of LAW command_menu_spec
#
# PROOF of LAW command_menu_spec: the model cuts the words into those
# before the last and the last (pwh.cut), walks the first as the spec does
# (pwh.walk), and lists cmd_rows of the lowercased last word (cb_lows,
# cb_items).

import Base
import ../../laws/command/whole.bend as CommandWhole
import ./base/whole.bend as LACommandWhole

def CommandWhole.command_menu_spec(t, line):
  LACommandWhole.pwh.menu(t, line)
