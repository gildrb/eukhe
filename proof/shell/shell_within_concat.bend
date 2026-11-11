# eukhe: the proof of LAW shell_within_concat
# Effect by effect, with the associativity of Bool.and (LASh.sh.and_assoc).

import Base
import ../../bend/tools.bend as Tl
import ../../laws/shell.bend as Shell
import ./base.bend as LASh

def Shell.shell_within_concat(es, fs, auto):
  match es:
    case Nil{}:
      {==}
    case +c <> +t:
      %Equal.sym(Bool, Tl.within(List.append(&2, Nat, t, fs), auto), Bool.and(Tl.within(t, auto), Tl.within(fs, auto)), Shell.shell_within_concat(t, fs, auto)) : {Bool.and(Bool.and(Tl.grantable(c), Tl.elem(auto, c)), _) == Bool.and(Bool.and(Bool.and(Tl.grantable(c), Tl.elem(auto, c)), Tl.within(t, auto)), Tl.within(fs, auto)) : Bool}
      LASh.sh.and_assoc(Bool.and(Tl.grantable(c), Tl.elem(auto, c)), Tl.within(t, auto), Tl.within(fs, auto))
