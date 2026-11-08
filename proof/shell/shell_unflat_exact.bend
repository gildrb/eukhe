# eukhe: the proof of LAW shell_unflat_exact
# Every state the right fold reaches spells the suffix it read (shue.fold);
# the lists of a state spell the same (shue.lists).

import Base
import ../../bend/wire_flat.bend as Fl
import ../../laws/shell.bend as Shell

# the suffix a fold state stands for
def shue.spell(st: Fl.St) -> List<&2, Nat>:
  match st:
    case Fl.Start{}:
      Nil{}
    case Fl.Mid{o, d}:
      Shell.sh_flat_one(o, Shell.sh_flat(d))

# a fold state m, if any, spells ns
def shue.Ok(ns: List<&2, Nat>, m: Maybe<&2, Fl.St>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{st}:
      {ns == shue.spell(st) : List<&2, Nat>}

def shue.Read(ns: List<&2, Nat>, r: Maybe<&2, List<&2, List<&2, Nat>>>) -> Type:
  match r:
    case None{}:
      Unit
    case Some{xss}:
      {ns == Shell.sh_flat(xss) : List<&2, Nat>}

def shue.lists(st: Fl.St) -> {Shell.sh_flat(Fl.St.lists(st)) == shue.spell(st) : List<&2, Nat>}:
  match st:
    case Fl.Start{}:
      {==}
    case Fl.Mid{o, d}:
      {==}

def shue.item(n: Nat, st: Fl.St, rest: List<&2, Nat>, ih: {rest == shue.spell(st) : List<&2, Nat>}) -> shue.Ok(n <> rest, Fl.step.item(n, st)):
  match n:
    case 0n:
      %Equal.sym(List<&2, Nat>, Shell.sh_flat(Fl.St.lists(st)), shue.spell(st), shue.lists(st)) : {0n <> rest == 0n <> _ : List<&2, Nat>}
      %ih : {0n <> rest == 0n <> _ : List<&2, Nat>}
      {==}
    case 1n+x:
      match st:
        case Fl.Start{}:
          Unit{}
        case Fl.Mid{o, d}:
          %ih : {{1n+x : Nat} <> rest == {1n+x : Nat} <> _ : List<&2, Nat>}
          {==}

def shue.step(n: Nat, rest: List<&2, Nat>, m: Maybe<&2, Fl.St>, ih: shue.Ok(rest, m)) -> shue.Ok(n <> rest, Fl.step(n, m)):
  match m:
    case None{}:
      Unit{}
    case Some{st}:
      shue.item(n, st, rest, ih)

def shue.fold(ns: List<&2, Nat>) -> shue.Ok(ns, Fl.fold(ns)):
  match ns:
    case Nil{}:
      {==}
    case n <> +rest:
      shue.step(n, rest, Fl.fold(rest), shue.fold(rest))

def shue.fin(ns: List<&2, Nat>, m: Maybe<&2, Fl.St>, ok: shue.Ok(ns, m)) -> shue.Read(ns, Fl.unflat.fin(m)):
  match m:
    case None{}:
      Unit{}
    case Some{st}:
      %Equal.sym(List<&2, Nat>, Shell.sh_flat(Fl.St.lists(st)), shue.spell(st), shue.lists(st)) : {ns == _ : List<&2, Nat>}
      ok

def Shell.shell_unflat_exact(ns, xss, h):
  %h : shue.Read(ns, _)
  shue.fin(ns, Fl.fold(ns), shue.fold(ns))
