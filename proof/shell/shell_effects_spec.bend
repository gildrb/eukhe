# eukhe: the proof of LAW shell_effects_spec
# Appending a part's effects to the rest is the spec's 6-then-plain-codes
# on that rest (shef.plain, shef.part); then part by part.

import Base
import ../../bend/tools.bend as Tl
import ../../laws/shell.bend as Shell

def shef.keep(b: Bool, c: Nat, xs: List<&2, Nat>, +r: List<&2, Nat>) -> {List.append(&2, Nat, Tl.plain.add(b, c, xs), r) == Shell.sh_plain.keep(b, c, List.append(&2, Nat, xs, r)) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def shef.plain(cs: List<&2, Nat>, +r: List<&2, Nat>) -> {List.append(&2, Nat, Tl.plain(cs), r) == Shell.sh_plain(cs, r) : List<&2, Nat>}:
  match cs:
    case Nil{}:
      {==}
    case +c <> +t:
      %shef.plain(t, r) : {List.append(&2, Nat, Tl.plain(c <> t), r) == Shell.sh_plain.keep(Nat.is_eq(c, 6n), c, _) : List<&2, Nat>}
      shef.keep(Nat.is_eq(c, 6n), c, Tl.plain(t), r)

def shef.part(o: List<&2, Nat>, s: Bool, +r: List<&2, Nat>) -> {List.append(&2, Nat, Tl.part.effs(Tl.Part{o, s}), r) == Shell.sh_secret(s, Shell.sh_plain(o, r)) : List<&2, Nat>}:
  match s:
    case True{}:
      %shef.plain(o, r) : {6n <> List.append(&2, Nat, Tl.plain(o), r) == 6n <> _ : List<&2, Nat>}
      {==}
    case False{}:
      shef.plain(o, r)

def Shell.shell_effects_spec(ps):
  match ps:
    case Nil{}:
      {==}
    case p <> +t:
      match p:
        case Tl.Part{o, s}:
          %Shell.shell_effects_spec(t) : {List.append(&2, Nat, Tl.part.effs(Tl.Part{o, s}), Tl.join(Tl.parts.effs(t))) == Shell.sh_secret(s, Shell.sh_plain(o, _)) : List<&2, Nat>}
          shef.part(o, s, Tl.join(Tl.parts.effs(t)))
