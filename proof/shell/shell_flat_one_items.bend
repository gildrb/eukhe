# eukhe: the proof of LAW shell_flat_one_items
# Item by item: the item at place i of xs is at place i of its spelling,
# offset by one (shfi.at, before any rest).

import Base
import ../../bend/wire_flat.bend as Fl
import ../../laws/shell.bend as Shell
import ../base/staging.bend as LStg

def shfi.MI(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      True{}

def shfi.succ(m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      Some{1n+v}

def shfi.at(xs: List<&2, Nat>, +i: Nat, +x: Nat, -r: List<&2, Nat>, h: {List.get(&2, Nat, xs, i) == Some{x} : Maybe<&2, Nat>}) -> {List.get(&2, Nat, Fl.one(xs, r), i) == Some{1n+x} : Maybe<&2, Nat>}:
  match xs:
    case Nil{}:
      LStg.stg.absurdF({List.get(&2, Nat, Fl.one(Nil{}, r), i) == Some{1n+x} : Maybe<&2, Nat>}, Equal.cong(Maybe<&2, Nat>, Bool, shfi.MI, None{}, Some{x}, h))
    case y <> t:
      match i:
        case 0n:
          Equal.cong(Maybe<&2, Nat>, Maybe<&2, Nat>, shfi.succ, Some{y}, Some{x}, h)
        case 1n+p:
          shfi.at(t, p, x, r, h)

def Shell.shell_flat_one_items(xs, i, x, at):
  shfi.at(xs, i, x, Nil{}, at)
