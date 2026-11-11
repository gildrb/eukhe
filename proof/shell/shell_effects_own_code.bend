# eukhe: the proof of LAW shell_effects_own_code
# A code that is not 6 is kept (Tl.plain.add with drop False).

import Base
import ../../bend/tools.bend as Tl
import ../../laws/shell.bend as Shell
import ./base.bend as LASh

def Shell.shell_effects_own_code(c, not6):
  %Equal.sym(Bool, Nat.is_eq(c, 6n), False{}, not6) : {List.append(&2, Nat, Tl.plain.add(_, c, Nil{}), Nil{}) == [c] : List<&2, Nat>}
  {==}
