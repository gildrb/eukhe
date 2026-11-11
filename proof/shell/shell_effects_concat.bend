# eukhe: the proof of LAW shell_effects_concat
# The parts' effect lists of ps then qs are those of ps then those of qs
# (shec.effs); joining lists in a row is joining each part (shec.join,
# by associativity of append).

import Base
import ../../bend/tools.bend as Tl
import ../../laws/shell.bend as Shell
import ./base.bend as LASh

def shec.effs(ps: List<&2, Tl.Part>, +qs: List<&2, Tl.Part>) -> {Tl.parts.effs(List.append(&2, Tl.Part, ps, qs)) == List.append(&2, List<&2, Nat>, Tl.parts.effs(ps), Tl.parts.effs(qs)) : List<&2, List<&2, Nat>>}:
  match ps:
    case Nil{}:
      {==}
    case p <> t:
      %shec.effs(t, qs) : {Tl.part.effs(p) <> Tl.parts.effs(List.append(&2, Tl.Part, t, qs)) == Tl.part.effs(p) <> _ : List<&2, List<&2, Nat>>}
      {==}

def shec.join(xss: List<&2, List<&2, Nat>>, +yss: List<&2, List<&2, Nat>>) -> {Tl.join(List.append(&2, List<&2, Nat>, xss, yss)) == List.append(&2, Nat, Tl.join(xss), Tl.join(yss)) : List<&2, Nat>}:
  match xss:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(List<&2, Nat>, Tl.join(List.append(&2, List<&2, Nat>, t, yss)), List.append(&2, Nat, Tl.join(t), Tl.join(yss)), shec.join(t, yss)) : {List.append(&2, Nat, x, _) == List.append(&2, Nat, List.append(&2, Nat, x, Tl.join(t)), Tl.join(yss)) : List<&2, Nat>}
      Equal.sym(List<&2, Nat>, List.append(&2, Nat, List.append(&2, Nat, x, Tl.join(t)), Tl.join(yss)), List.append(&2, Nat, x, List.append(&2, Nat, Tl.join(t), Tl.join(yss))), LASh.sh.app_assoc(Nat, x, Tl.join(t), Tl.join(yss)))

def Shell.shell_effects_concat(ps, qs):
  %Equal.sym(List<&2, List<&2, Nat>>, Tl.parts.effs(List.append(&2, Tl.Part, ps, qs)), List.append(&2, List<&2, Nat>, Tl.parts.effs(ps), Tl.parts.effs(qs)), shec.effs(ps, qs)) : {Tl.join(_) == List.append(&2, Nat, Tl.join(Tl.parts.effs(ps)), Tl.join(Tl.parts.effs(qs))) : List<&2, Nat>}
  shec.join(Tl.parts.effs(ps), Tl.parts.effs(qs))
