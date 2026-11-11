# eukhe: the proof of LAW cvar_written_append
# Induction on the first run: the test of a set reads that set alone.

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/resolution.bend as Cvar

def wra.step(h: Bool, +s: Cv.Bind, +r: List<&2, Cv.Bind>, +b: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +f: Cv.Flag, ih: {Cv.written(List.append(&2, Cv.Bind, r, b), ds, f) == List.append(&2, Cv.Bind, Cv.written(r, ds, f), Cv.written(b, ds, f)) : List<&2, Cv.Bind>}) -> {Cv.written.go(s <> List.append(&2, Cv.Bind, r, b), ds, f, h) == List.append(&2, Cv.Bind, Cv.written.go(s <> r, ds, f, h), Cv.written(b, ds, f)) : List<&2, Cv.Bind>}:
  match h:
    case True{}:
      Equal.cong(List<&2, Cv.Bind>, List<&2, Cv.Bind>, t => s <> t, Cv.written(List.append(&2, Cv.Bind, r, b), ds, f), List.append(&2, Cv.Bind, Cv.written(r, ds, f), Cv.written(b, ds, f)), ih)
    case False{}:
      ih

def wra.go(a: List<&2, Cv.Bind>, +b: List<&2, Cv.Bind>, +ds: List<&2, Cv.Decl>, +f: Cv.Flag) -> {Cv.written(List.append(&2, Cv.Bind, a, b), ds, f) == List.append(&2, Cv.Bind, Cv.written(a, ds, f), Cv.written(b, ds, f)) : List<&2, Cv.Bind>}:
  match a:
    case Nil{}:
      {==}
    case +s <> +r:
      wra.step(Bool.and(Cv.flag.at(Cv.find(ds, Cv.Bind.id(s)), f), Cv.valid(ds, Cv.Agent{}, s)), s, r, b, ds, f, wra.go(r, b, ds, f))

def Cvar.cvar_written_append(a, b, ds, f):
  wra.go(a, b, ds, f)
