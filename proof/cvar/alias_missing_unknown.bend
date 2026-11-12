# eukhe: the proof of LAW alias_missing_unknown
# No alias has the name, so its body is the run of a missing alias
# (LE.ex.body_absent), which is reported (alias_unknown_reported).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/model.bend as Cvar
import ../../laws/cvar/entry.bend as CvarEntry
import ./alias_unknown_reported.bend as PAUR
import ./base/expand.bend as LE

def CvarEntry.alias_missing_unknown(n, as, none):
  Cvar.alias_unknown_reported(n, as, LE.ex.body_absent(as, n, none))
