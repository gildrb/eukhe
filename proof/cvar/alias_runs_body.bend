# eukhe: the proof of LAW alias_runs_body

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar.bend as Cvar
import ./base.bend as LA

# Lists
# -----

def pv.app_nil(xs: List<&2, Cv.Cmd>) -> {List.append(&2, Cv.Cmd, xs, Nil{}) == xs : List<&2, Cv.Cmd>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      Equal.cong(List<&2, Cv.Cmd>, List<&2, Cv.Cmd>, z => h <> z, List.append(&2, Cv.Cmd, t, Nil{}), t, pv.app_nil(t))

# reversing twice: rev(rev(b, o), p) is o reversed onto b ++ p
def pv.rev_rev(b: List<&2, Cv.Cmd>, +o: List<&2, Cv.Cmd>, +p: List<&2, Cv.Cmd>) -> {Cv.rev(Cv.rev(b, o), p) == Cv.rev(o, List.append(&2, Cv.Cmd, b, p)) : List<&2, Cv.Cmd>}:
  match b:
    case Nil{}:
      {==}
    case +x <> rest:
      pv.rev_rev(rest, x <> o, p)

# a plain list expands to itself (reversed onto the accumulator) at any
# depth
def pv.flat(b: List<&2, Cv.Cmd>, k: Nat, +as: List<&2, Cv.Alias>, +out: List<&2, Cv.Cmd>, h: {Cv.plain(b) == True{} : Bool}) -> {Cv.expand.go(k, b, as, Cv.Flat{out}) == Cv.Flat{Cv.rev(b, out)} : Cv.Exp}:
  match b:
    case Nil{}:
      match k:
        case 0n:
          {==}
        case 1n+e:
          {==}
    case c <> rest:
      match c:
        case Cv.CSet{+i, +v}:
          match k:
            case 0n:
              pv.flat(rest, 0n, as, Cv.CSet{i, v} <> out, h)
            case 1n+e:
              pv.flat(rest, 1n+e, as, Cv.CSet{i, v} <> out, h)
        case Cv.CToggle{+i}:
          match k:
            case 0n:
              pv.flat(rest, 0n, as, Cv.CToggle{i} <> out, h)
            case 1n+e:
              pv.flat(rest, 1n+e, as, Cv.CToggle{i} <> out, h)
        case Cv.CRun{n}:
          LA.pv.absurdF({Cv.expand.go(k, Cv.CRun{n} <> rest, as, Cv.Flat{out}) == Cv.Flat{Cv.rev(Cv.CRun{n} <> rest, out)} : Cv.Exp}, h)
        case Cv.CGone{n}:
          LA.pv.absurdF({Cv.expand.go(k, Cv.CGone{n} <> rest, as, Cv.Flat{out}) == Cv.Flat{Cv.rev(Cv.CGone{n} <> rest, out)} : Cv.Exp}, h)

def Cvar.alias_runs_body(n, b, as, flat):
  +t = {Cv.Alias{n, b} <> as : List<&2, Cv.Alias>}
  +k = List.length(&2, Cv.Alias, t)
  %Equal.sym(List<&2, Cv.Cmd>, Cv.body(t, n), b, LA.pv.body_head(n, b, as)) : {Cv.fin(Cv.expand.go(k, _, t, Cv.Flat{Nil{}})) == Cv.Flat{b} : Cv.Exp}
  %Equal.sym(Cv.Exp, Cv.expand.go(k, b, t, Cv.Flat{Nil{}}), Cv.Flat{Cv.rev(b, Nil{})}, pv.flat(b, k, t, Nil{}, flat)) : {Cv.fin(_) == Cv.Flat{b} : Cv.Exp}
  Equal.cong(List<&2, Cv.Cmd>, Cv.Exp, l => Cv.Flat{l}, Cv.rev(Cv.rev(b, Nil{}), Nil{}), b, Equal.trans(List<&2, Cv.Cmd>, Cv.rev(Cv.rev(b, Nil{}), Nil{}), List.append(&2, Cv.Cmd, b, Nil{}), b, pv.rev_rev(b, Nil{}, Nil{}), pv.app_nil(b)))
