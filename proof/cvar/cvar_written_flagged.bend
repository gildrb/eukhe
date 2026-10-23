# eukhe: the proof of LAW cvar_written_flagged

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar.bend as Cvar
import ./base.bend as LA

# Written sets
# ------------

def pv.wf(ss: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +f: Cv.Flag, hit: Bool, eh: {Cv.out.at(ss, ds, f) == hit : Bool}) -> {Cv.all_flag(Cv.written.go(ss, ds, f, hit), ds, f) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case +s <> +rest:
      match hit:
        case True{}:
          +w = Cv.written.go(rest, ds, f, Cv.out.at(rest, ds, f))
          +fl = Cv.flag.at(Cv.find(ds, Cv.Bind.id(s)), f)
          LA.pv.and_t(fl, Cv.all_flag(w, ds, f), LA.cvar.pv.and_l(fl, Cv.valid(ds, Cv.Agent{}, s), eh), pv.wf(rest, ds, f, Cv.out.at(rest, ds, f), {==}))
        case False{}:
          pv.wf(rest, ds, f, Cv.out.at(rest, ds, f), {==})

def pv.wf_top(+ss: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +f: Cv.Flag) -> {Cv.all_flag(Cv.written(ss, ds, f), ds, f) == True{} : Bool}:
  pv.wf(ss, ds, f, Cv.out.at(ss, ds, f), {==})

def pv.cvar_written_flagged(ss: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +f: Cv.Flag) -> {Cv.all_flag(Cv.written(ss, ds, f), ds, f) == True{} : Bool}:
  pv.wf_top(ss, ds, f)

def Cvar.cvar_written_flagged(ss, ds, f):
  pv.cvar_written_flagged(ss, ds, f)
