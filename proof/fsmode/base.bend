# eukhe: lemmas the proofs of area fsmode share

import Base
import ../../bend/ffi_fsmode.bend as FFs
import ../../bend/fsmode.bend as Fs
import ../../laws/fsmode.bend as Fsmode

def fsmode.pf.BD(b: Bool, A: Type) -> Type:
  match b:
    case True{}:
      A
    case False{}:
      Unit

def fsmode.pf.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : fsmode.pf.BD(_, A)
  Unit{}

def fsmode.pf.absurdT(-A: Type, e: {True{} == False{} : Bool}) -> A:
  fsmode.pf.absurdF(A, Equal.sym(Bool, True{}, False{}, e))

# The decisions
# -------------

# a real dir: the entry's verdict is the laws' on every owner and mode
def fs.dir_reply(mine: Bool, loose: Bool) -> {FFs.answer.dir(Fs.Seen{Fs.Dir{}, mine, loose}) == Fsmode.dir_reply.dir(mine, loose) : String}:
  match mine loose:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# a named cwd: the entry's verdict is the laws'
def fs.cwd_named(empty: Bool, s: Fs.Stat) -> {FFs.put_open(Fs.open(Fs.cwd.named(empty, s))) == Fsmode.cwd_reply.named(empty, s) : String}:
  match empty:
    case True{}:
      {==}
    case False{}:
      match s:
        case Fs.Absent{}:
          {==}
        case Fs.AFile{}:
          {==}
        case Fs.ADir{}:
          {==}
