# eukhe: the proof of LAW cvar_written_one
# The set's test is its cvar's flag and its validity in an agent layer;
# the flag is the declaration's (wro.flag), the validity is the laws'
# counting rule (LR.rs.valid), which is the verdict's (LV.ck.fine_at).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/resolution.bend as Cvar
import ./base/resolve.bend as LR
import ./base/verdict.bend as LV

def wro.flag(m: Maybe<&2, Cv.Decl>, f: Cv.Flag) -> {Cv.flag.at(m, f) == Cvar.spec_has_flag(m, f) : Bool}:
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

def wro.keep(h: Bool, +s: Cv.Bind, +ds: List<&2, Cv.Decl>, +f: Cv.Flag) -> {Cv.written.go([s], ds, f, h) == Cvar.spec_keep_if(h, s) : List<&2, Cv.Bind>}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

def wro.go(+i: Nat, +v: Cv.Val, +ds: List<&2, Cv.Decl>, +f: Cv.Flag) -> {Cv.written([Cv.Bind{i, v}], ds, f) == Cvar.spec_keep_if(Bool.and(Cvar.spec_has_flag(Cv.find(ds, i), f), Cvar.spec_ck_fine(Cv.check(ds, Cv.Agent{}, Cv.Bind{i, v}))), Cv.Bind{i, v}) : List<&2, Cv.Bind>}:
  +s = {Cv.Bind{i, v} : Cv.Bind}
  +m = Cv.find(ds, i)
  +ev = Equal.trans(Bool, Cvar.spec_ck_fine(Cv.check(ds, Cv.Agent{}, s)), Cvar.spec_counts(ds, Cv.Agent{}, s), Cv.valid(ds, Cv.Agent{}, s), LV.ck.fine_at(m, Cv.Agent{}, i, v), Equal.sym(Bool, Cv.valid(ds, Cv.Agent{}, s), Cvar.spec_counts(ds, Cv.Agent{}, s), LR.rs.valid(ds, Cv.Agent{}, s)))
  %Equal.sym(Bool, Cvar.spec_ck_fine(Cv.check(ds, Cv.Agent{}, s)), Cv.valid(ds, Cv.Agent{}, s), ev) : {Cv.written([s], ds, f) == Cvar.spec_keep_if(Bool.and(Cvar.spec_has_flag(m, f), _), s) : List<&2, Cv.Bind>}
  %wro.flag(m, f) : {Cv.written([s], ds, f) == Cvar.spec_keep_if(Bool.and(_, Cv.valid(ds, Cv.Agent{}, s)), s) : List<&2, Cv.Bind>}
  wro.keep(Bool.and(Cv.flag.at(m, f), Cv.valid(ds, Cv.Agent{}, s)), s, ds, f)

def Cvar.cvar_written_one(s, ds, f):
  match s:
    case Cv.Bind{+i, +v}:
      wro.go(i, v, ds, f)
