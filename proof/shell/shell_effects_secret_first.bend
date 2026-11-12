# eukhe: the proof of LAW shell_effects_secret_first
# A part that names a secret path has 6, then its plain codes; one that
# names none has its plain codes: both sides compute the same list.

import Base
import ../../bend/tools.bend as Tl
import ../../laws/shell.bend as Shell
import ./base.bend as LASh

def Shell.shell_effects_secret_first(o):
  {==}
