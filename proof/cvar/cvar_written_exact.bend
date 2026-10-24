# eukhe: the proof of LAW cvar_written_exact
# Set by set: the model's test of a set (its cvar's flag, its validity in
# an agent layer) is the spec's (LR.re.find, LR.re.valid), and a set the
# test keeps leads the rest.

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar.bend as Cvar
import ./base/resolve.bend as LR

def wr.flag(m: Maybe<&2, Cv.Decl>, f: Cv.Flag) -> {Cv.flag.at(m, f) == Cvar.spec_flag.at(m, f) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{d}:
      match d:
        case Cv.Decl{i, t, c, p, r, v}:
          match f:
            case Cv.Persist{}:
              {==}
            case Cv.Replicate{}:
              {==}

def wr.keep(b: Bool, +s: Cv.Bind, +rest: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +f: Cv.Flag, ih: {Cv.written(rest, ds, f) == Cvar.spec_written(rest, ds, f) : List<&2, Cv.Bind>}) -> {Cv.written.go(s <> rest, ds, f, b) == Cvar.spec_keep(b, s, Cvar.spec_written(rest, ds, f)) : List<&2, Cv.Bind>}:
  match b:
    case True{}:
      Equal.cong(List<&2, Cv.Bind>, List<&2, Cv.Bind>, t => s <> t, Cv.written(rest, ds, f), Cvar.spec_written(rest, ds, f), ih)
    case False{}:
      ih

def wr.go(ss: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +f: Cv.Flag) -> {Cv.written(ss, ds, f) == Cvar.spec_written(ss, ds, f) : List<&2, Cv.Bind>}:
  match ss:
    case Nil{}:
      {==}
    case Cv.Bind{+i, +v} <> +rest:
      +s = {Cv.Bind{i, v} : Cv.Bind}
      %LR.re.find(ds, i) : {Cv.written(s <> rest, ds, f) == Cvar.spec_keep(Bool.and(Cvar.spec_flag.at(_, f), Cvar.spec_valid(ds, Cv.Agent{}, s)), s, Cvar.spec_written(rest, ds, f)) : List<&2, Cv.Bind>}
      %LR.re.valid(ds, Cv.Agent{}, s) : {Cv.written(s <> rest, ds, f) == Cvar.spec_keep(Bool.and(Cvar.spec_flag.at(Cv.find(ds, i), f), _), s, Cvar.spec_written(rest, ds, f)) : List<&2, Cv.Bind>}
      %wr.flag(Cv.find(ds, i), f) : {Cv.written(s <> rest, ds, f) == Cvar.spec_keep(Bool.and(_, Cv.valid(ds, Cv.Agent{}, s)), s, Cvar.spec_written(rest, ds, f)) : List<&2, Cv.Bind>}
      wr.keep(Bool.and(Cv.flag.at(Cv.find(ds, i), f), Cv.valid(ds, Cv.Agent{}, s)), s, rest, ds, f, wr.go(rest, ds, f))

def Cvar.cvar_written_exact(ss, ds, f):
  wr.go(ss, ds, f)
