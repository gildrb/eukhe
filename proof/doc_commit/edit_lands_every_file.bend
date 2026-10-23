# eukhe: the proof of LAW edit_lands_every_file

import Base
import ../../bend/doc_commit.bend as Cm
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pc.lands_put(x: Cm.Fault, k: Cm.Op, -rest: List<&2, Cm.Doc>, +n: Nat, ok: {Bool.or(Cm.Fault.fails(x), Cm.failing(rest)) == False{} : Bool}, ih: {Cm.failing(rest) == False{} : Bool} -> {Cm.landed.go(rest, 1n+n) == Cm.ids(rest, 1n+n) : List<&2, Nat>}) -> {Cm.landed.put(n, Cm.landed.go(rest, 1n+n), Cm.publish.go(x, k)) == n <> Cm.ids(rest, 1n+n) : List<&2, Nat>}:
  match x:
    case Cm.Clean{}:
      %ih(ok) : {n <> Cm.landed.go(rest, 1n+n) == n <> _ : List<&2, Nat>}
      {==}
    case Cm.Sync{}:
      %ih(ok) : {n <> Cm.landed.go(rest, 1n+n) == n <> _ : List<&2, Nat>}
      {==}
    case Cm.Publish{}:
      LA.documents.pc.absurd({Cm.landed.put(n, Cm.landed.go(rest, 1n+n), Cm.Failed{}) == n <> Cm.ids(rest, 1n+n) : List<&2, Nat>}, ok)
    case Cm.Remove{}:
      match k:
        case Cm.Update{}:
          %ih(ok) : {n <> Cm.landed.go(rest, 1n+n) == n <> _ : List<&2, Nat>}
          {==}
        case Cm.Moving{}:
          %ih(ok) : {n <> Cm.landed.go(rest, 1n+n) == n <> _ : List<&2, Nat>}
          {==}

# with no failed publish, every file lands
def pc.lands_go(fs: List<&2, Cm.Doc>, +n: Nat, ok: {Cm.failing(fs) == False{} : Bool}) -> {Cm.landed.go(fs, n) == Cm.ids(fs, n) : List<&2, Nat>}:
  match fs:
    case Nil{}:
      {==}
    case g <> +rest:
      match g:
        case Cm.Doc{k, c, x}:
          pc.lands_put(x, k, rest, n, ok, h => pc.lands_go(rest, 1n+n, h))

# the law edit_lands_every_file
def pc.lands_every_file(+fs: List<&2, Cm.Doc>, same: {Cm.conflict(fs) == False{} : Bool}, sound: {Cm.failing(fs) == False{} : Bool}) -> {Cm.landed(fs) == Cm.ids(fs, 0n) : List<&2, Nat>}:
  %Equal.sym(Bool, Cm.conflict(fs), False{}, same) : {Cm.landed.pick(_, fs) == Cm.ids(fs, 0n) : List<&2, Nat>}
  pc.lands_go(fs, 0n, sound)

def Laws.edit_lands_every_file(fs, same, sound):
  pc.lands_every_file(fs, same, sound)
