# eukhe: the proof of LAW socket_dir_owned

import Base
import ../../bend/fsmode.bend as Fs
import ../../laws/fsmode.bend as Fsmode

# ---- fsmode ----

# proof_fsmode: the laws of LAWS.bend section fsmode over the model in
# bend/fsmode.bend. Each decision is a match on its inputs, so each law
# follows by case analysis; a clash of two constructors is refuted with a
# motive that sends the expected constructor to the goal and the others
# to Unit.

# Clashes
# -------

def pf.VD(v: Fs.Verdict, A: Type) -> Type:
  match v:
    case Fs.Create{m}:
      Unit
    case Fs.Use{}:
      A
    case Fs.Refuse{}:
      Unit

def pf.refuse_use(-A: Type, e: {Fs.Refuse{} == Fs.Use{} : Fs.Verdict}) -> A:
  %e : pf.VD(_, A)
  Unit{}

def pf.create_use(-A: Type, +m: Fs.Mode, e: {Fs.Create{m} == Fs.Use{} : Fs.Verdict}) -> A:
  %e : pf.VD(_, A)
  Unit{}

# The socket dir
# --------------

def pf.dir_owned(mine: Bool, loose: Bool, used: {Fs.socket_dir.dir(mine, loose) == Fs.Use{} : Fs.Verdict}) -> {Bool.and(mine, Bool.not(loose)) == True{} : Bool}:
  match mine loose:
    case True{} False{}:
      {==}
    case True{} True{}:
      pf.refuse_use({Bool.and(True{}, Bool.not(True{})) == True{} : Bool}, used)
    case False{} l:
      pf.refuse_use({Bool.and(False{}, Bool.not(l)) == True{} : Bool}, used)

def owned(d: Fs.Seen, used: {Fs.socket_dir(d) == Fs.Use{} : Fs.Verdict}) -> {Fs.Seen.safe(d) == True{} : Bool}:
  match d:
    case Fs.Seen{k, mine, loose}:
      match k:
        case Fs.Missing{}:
          pf.create_use({Fs.Seen.safe(Fs.Seen{Fs.Missing{}, mine, loose}) == True{} : Bool}, Fs.dir_mode(), used)
        case Fs.Dir{}:
          pf.dir_owned(mine, loose, used)
        case Fs.Link{}:
          pf.refuse_use({Fs.Seen.safe(Fs.Seen{Fs.Link{}, mine, loose}) == True{} : Bool}, used)
        case Fs.Other{}:
          pf.refuse_use({Fs.Seen.safe(Fs.Seen{Fs.Other{}, mine, loose}) == True{} : Bool}, used)

# File modes, the socket dir and the working dir

def Fsmode.socket_dir_owned(d, used):
  owned(d, used)
